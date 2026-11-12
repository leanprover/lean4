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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_markStored___redArg(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__3;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "norm"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(87, 130, 109, 65, 232, 6, 169, 172)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(15, 182, 41, 28, 2, 115, 0, 31)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__6;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "not normalized: "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__8;
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
lean_object* v___y_5_; lean_object* v_p_6_; lean_object* v_p_15_; uint8_t v___x_16_; 
v_p_15_ = lean_ctor_get(v_c_3_, 0);
v___x_16_ = l_Int_Internal_Linear_Poly_isSorted(v_p_15_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
lean_inc_ref(v_p_15_);
v___x_17_ = l_Int_Internal_Linear_Poly_norm(v_p_15_);
v___x_18_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_18_, 0, v_c_3_);
v___x_19_ = lean_box(0);
lean_inc_ref(v___x_17_);
v___x_20_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_20_, 0, v___x_17_);
lean_ctor_set(v___x_20_, 1, v___x_18_);
lean_ctor_set(v___x_20_, 2, v___x_19_);
v___y_5_ = v___x_20_;
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
lean_object* v_k_7_; lean_object* v___x_8_; uint8_t v___x_9_; 
v_k_7_ = l_Int_Internal_Linear_Poly_gcdCoeffs_x27(v_p_6_);
v___x_8_ = lean_unsigned_to_nat(1u);
v___x_9_ = lean_nat_dec_eq(v_k_7_, v___x_8_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_10_ = lean_nat_to_int(v_k_7_);
v___x_11_ = l_Int_Internal_Linear_Poly_div(v___x_10_, v_p_6_);
lean_dec(v___x_10_);
v___x_12_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_12_, 0, v___y_5_);
v___x_13_ = lean_box(0);
v___x_14_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_14_, 0, v___x_11_);
lean_ctor_set(v___x_14_, 1, v___x_12_);
lean_ctor_set(v___x_14_, 2, v___x_13_);
return v___x_14_;
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0(lean_object* v_msgData_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v___x_27_; lean_object* v_env_28_; uint8_t v___x_29_; lean_object* v_env_30_; lean_object* v___x_31_; lean_object* v_toCold_32_; lean_object* v_mctx_33_; lean_object* v_lctx_34_; lean_object* v_options_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_27_ = lean_st_ref_get(v___y_25_);
v_env_28_ = lean_ctor_get(v___x_27_, 0);
lean_inc_ref(v_env_28_);
lean_dec(v___x_27_);
v___x_29_ = 0;
v_env_30_ = l_Lean_Environment_setRecordingDeps(v_env_28_, v___x_29_);
v___x_31_ = lean_st_ref_get(v___y_23_);
v_toCold_32_ = lean_ctor_get(v___y_24_, 0);
v_mctx_33_ = lean_ctor_get(v___x_31_, 0);
lean_inc_ref(v_mctx_33_);
lean_dec(v___x_31_);
v_lctx_34_ = lean_ctor_get(v___y_22_, 2);
v_options_35_ = lean_ctor_get(v_toCold_32_, 2);
lean_inc_ref(v_options_35_);
lean_inc_ref(v_lctx_34_);
v___x_36_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_36_, 0, v_env_30_);
lean_ctor_set(v___x_36_, 1, v_mctx_33_);
lean_ctor_set(v___x_36_, 2, v_lctx_34_);
lean_ctor_set(v___x_36_, 3, v_options_35_);
v___x_37_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
lean_ctor_set(v___x_37_, 1, v_msgData_21_);
v___x_38_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0___boxed(lean_object* v_msgData_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0(v_msgData_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
return v_res_45_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_46_; double v___x_47_; 
v___x_46_ = lean_unsigned_to_nat(0u);
v___x_47_ = lean_float_of_nat(v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(lean_object* v_cls_51_, lean_object* v_msg_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v_ref_58_; lean_object* v___x_59_; lean_object* v_a_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_105_; 
v_ref_58_ = lean_ctor_get(v___y_55_, 2);
v___x_59_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0(v_msg_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
v_a_60_ = lean_ctor_get(v___x_59_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_59_);
if (v_isSharedCheck_105_ == 0)
{
v___x_62_ = v___x_59_;
v_isShared_63_ = v_isSharedCheck_105_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_a_60_);
lean_dec(v___x_59_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_105_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_64_; lean_object* v_traceState_65_; lean_object* v_env_66_; lean_object* v_nextMacroScope_67_; lean_object* v_ngen_68_; lean_object* v_auxDeclNGen_69_; lean_object* v_cache_70_; lean_object* v_recordedDeps_71_; lean_object* v_messages_72_; lean_object* v_infoState_73_; lean_object* v_snapshotTasks_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_104_; 
v___x_64_ = lean_st_ref_take(v___y_56_);
v_traceState_65_ = lean_ctor_get(v___x_64_, 4);
v_env_66_ = lean_ctor_get(v___x_64_, 0);
v_nextMacroScope_67_ = lean_ctor_get(v___x_64_, 1);
v_ngen_68_ = lean_ctor_get(v___x_64_, 2);
v_auxDeclNGen_69_ = lean_ctor_get(v___x_64_, 3);
v_cache_70_ = lean_ctor_get(v___x_64_, 5);
v_recordedDeps_71_ = lean_ctor_get(v___x_64_, 6);
v_messages_72_ = lean_ctor_get(v___x_64_, 7);
v_infoState_73_ = lean_ctor_get(v___x_64_, 8);
v_snapshotTasks_74_ = lean_ctor_get(v___x_64_, 9);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_104_ == 0)
{
v___x_76_ = v___x_64_;
v_isShared_77_ = v_isSharedCheck_104_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_snapshotTasks_74_);
lean_inc(v_infoState_73_);
lean_inc(v_messages_72_);
lean_inc(v_recordedDeps_71_);
lean_inc(v_cache_70_);
lean_inc(v_traceState_65_);
lean_inc(v_auxDeclNGen_69_);
lean_inc(v_ngen_68_);
lean_inc(v_nextMacroScope_67_);
lean_inc(v_env_66_);
lean_dec(v___x_64_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_104_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
uint64_t v_tid_78_; lean_object* v_traces_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_103_; 
v_tid_78_ = lean_ctor_get_uint64(v_traceState_65_, sizeof(void*)*1);
v_traces_79_ = lean_ctor_get(v_traceState_65_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v_traceState_65_);
if (v_isSharedCheck_103_ == 0)
{
v___x_81_ = v_traceState_65_;
v_isShared_82_ = v_isSharedCheck_103_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_traces_79_);
lean_dec(v_traceState_65_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_103_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_83_; lean_object* v___x_84_; double v___x_85_; uint8_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_94_; 
v___x_83_ = lean_box(0);
v___x_84_ = lean_box(0);
v___x_85_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0);
v___x_86_ = 0;
v___x_87_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__1));
v___x_88_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_88_, 0, v_cls_51_);
lean_ctor_set(v___x_88_, 1, v___x_84_);
lean_ctor_set(v___x_88_, 2, v___x_87_);
lean_ctor_set_float(v___x_88_, sizeof(void*)*3, v___x_85_);
lean_ctor_set_float(v___x_88_, sizeof(void*)*3 + 8, v___x_85_);
lean_ctor_set_uint8(v___x_88_, sizeof(void*)*3 + 16, v___x_86_);
v___x_89_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__2));
v___x_90_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_90_, 0, v___x_88_);
lean_ctor_set(v___x_90_, 1, v_a_60_);
lean_ctor_set(v___x_90_, 2, v___x_89_);
lean_inc(v_ref_58_);
v___x_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_91_, 0, v_ref_58_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = l_Lean_PersistentArray_push___redArg(v_traces_79_, v___x_91_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 0, v___x_92_);
v___x_94_ = v___x_81_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_92_);
lean_ctor_set_uint64(v_reuseFailAlloc_102_, sizeof(void*)*1, v_tid_78_);
v___x_94_ = v_reuseFailAlloc_102_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
lean_object* v___x_96_; 
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 4, v___x_94_);
v___x_96_ = v___x_76_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_env_66_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_nextMacroScope_67_);
lean_ctor_set(v_reuseFailAlloc_101_, 2, v_ngen_68_);
lean_ctor_set(v_reuseFailAlloc_101_, 3, v_auxDeclNGen_69_);
lean_ctor_set(v_reuseFailAlloc_101_, 4, v___x_94_);
lean_ctor_set(v_reuseFailAlloc_101_, 5, v_cache_70_);
lean_ctor_set(v_reuseFailAlloc_101_, 6, v_recordedDeps_71_);
lean_ctor_set(v_reuseFailAlloc_101_, 7, v_messages_72_);
lean_ctor_set(v_reuseFailAlloc_101_, 8, v_infoState_73_);
lean_ctor_set(v_reuseFailAlloc_101_, 9, v_snapshotTasks_74_);
v___x_96_ = v_reuseFailAlloc_101_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
lean_object* v___x_97_; lean_object* v___x_99_; 
v___x_97_ = lean_st_ref_put(v___y_56_, v___x_96_);
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 0, v___x_83_);
v___x_99_ = v___x_62_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_83_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(lean_object* v_a_132_, lean_object* v_x_133_, lean_object* v_c_u2081_134_, lean_object* v_b_135_, lean_object* v_c_u2082_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v___y_149_; lean_object* v___y_155_; lean_object* v_p_208_; lean_object* v_p_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v_p_208_ = lean_ctor_get(v_c_u2081_134_, 0);
v_p_209_ = lean_ctor_get(v_c_u2082_136_, 0);
v___x_210_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_211_ = lean_int_dec_le(v___x_210_, v_a_132_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
lean_inc_ref(v_p_208_);
v___x_212_ = l_Int_Internal_Linear_Poly_mul(v_p_208_, v_b_135_);
v___x_213_ = lean_int_neg(v_a_132_);
lean_inc_ref(v_p_209_);
v___x_214_ = l_Int_Internal_Linear_Poly_mul(v_p_209_, v___x_213_);
lean_dec(v___x_213_);
v___x_215_ = l_Int_Internal_Linear_Poly_combine(v___x_212_, v___x_214_);
v___y_155_ = v___x_215_;
goto v___jp_154_;
}
else
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
lean_inc_ref(v_p_209_);
v___x_216_ = l_Int_Internal_Linear_Poly_mul(v_p_209_, v_a_132_);
v___x_217_ = lean_int_neg(v_b_135_);
lean_inc_ref(v_p_208_);
v___x_218_ = l_Int_Internal_Linear_Poly_mul(v_p_208_, v___x_217_);
lean_dec(v___x_217_);
v___x_219_ = l_Int_Internal_Linear_Poly_combine(v___x_216_, v___x_218_);
v___y_155_ = v___x_219_;
goto v___jp_154_;
}
v___jp_148_:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_150_ = lean_alloc_ctor(12, 3, 0);
lean_ctor_set(v___x_150_, 0, v_x_133_);
lean_ctor_set(v___x_150_, 1, v_c_u2081_134_);
lean_ctor_set(v___x_150_, 2, v_c_u2082_136_);
v___x_151_ = lean_box(0);
v___x_152_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_152_, 0, v___y_149_);
lean_ctor_set(v___x_152_, 1, v___x_150_);
lean_ctor_set(v___x_152_, 2, v___x_151_);
v___x_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
return v___x_153_;
}
v___jp_154_:
{
lean_object* v_toCold_156_; lean_object* v_options_157_; uint8_t v_hasTrace_158_; 
v_toCold_156_ = lean_ctor_get(v_a_145_, 0);
v_options_157_ = lean_ctor_get(v_toCold_156_, 2);
v_hasTrace_158_ = lean_ctor_get_uint8(v_options_157_, sizeof(void*)*1);
if (v_hasTrace_158_ == 0)
{
v___y_149_ = v___y_155_;
goto v___jp_148_;
}
else
{
lean_object* v_inheritedTraceOptions_159_; lean_object* v_cls_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v_inheritedTraceOptions_159_ = lean_ctor_get(v_toCold_156_, 11);
v_cls_160_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__3));
v___x_161_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6);
v___x_162_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_159_, v_options_157_, v___x_161_);
if (v___x_162_ == 0)
{
v___y_149_ = v___y_155_;
goto v___jp_148_;
}
else
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_133_, v_a_137_, v_a_145_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v_a_164_; lean_object* v___x_165_; 
v_a_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_a_164_);
lean_dec_ref_known(v___x_163_, 1);
lean_inc_ref(v_c_u2081_134_);
v___x_165_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_u2081_134_, v_a_137_, v_a_145_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v_a_166_; lean_object* v___x_167_; 
v_a_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_a_166_);
lean_dec_ref_known(v___x_165_, 1);
lean_inc_ref(v_c_u2082_136_);
v___x_167_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_136_, v_a_137_, v_a_145_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_a_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_a_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_a_168_);
lean_dec_ref_known(v___x_167_, 1);
v___x_169_ = l_Lean_MessageData_ofExpr(v_a_164_);
v___x_170_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8);
v___x_171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_169_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
v___x_172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v_a_166_);
v___x_173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v___x_170_);
v___x_174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v_a_168_);
v___x_175_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v_cls_160_, v___x_174_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_dec_ref_known(v___x_175_, 1);
v___y_149_ = v___y_155_;
goto v___jp_148_;
}
else
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
lean_dec_ref(v___y_155_);
lean_dec_ref(v_c_u2082_136_);
lean_dec_ref(v_c_u2081_134_);
lean_dec(v_x_133_);
v_a_176_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_183_ == 0)
{
v___x_178_ = v___x_175_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_175_);
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
lean_dec(v_a_166_);
lean_dec(v_a_164_);
lean_dec_ref(v___y_155_);
lean_dec_ref(v_c_u2082_136_);
lean_dec_ref(v_c_u2081_134_);
lean_dec(v_x_133_);
v_a_184_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_191_ == 0)
{
v___x_186_ = v___x_167_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_167_);
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
lean_dec(v_a_164_);
lean_dec_ref(v___y_155_);
lean_dec_ref(v_c_u2082_136_);
lean_dec_ref(v_c_u2081_134_);
lean_dec(v_x_133_);
v_a_192_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_165_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_165_);
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
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_dec_ref(v___y_155_);
lean_dec_ref(v_c_u2082_136_);
lean_dec_ref(v_c_u2081_134_);
lean_dec(v_x_133_);
v_a_200_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_163_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_163_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0(lean_object* v_cls_237_, lean_object* v_msg_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v_cls_237_, v_msg_238_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___boxed(lean_object* v_cls_251_, lean_object* v_msg_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0(v_cls_251_, v_msg_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v___y_254_);
lean_dec(v___y_253_);
return v_res_264_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = l_Lean_maxRecDepthErrorMessage;
v___x_271_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
return v___x_271_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_273_ = l_Lean_MessageData_ofFormat(v___x_272_);
return v___x_273_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_275_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_276_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set(v___x_276_, 1, v___x_274_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_277_){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_279_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v_ref_277_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(v_ref_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_285_, lean_object* v_ref_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(v_ref_286_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_299_, lean_object* v_ref_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0(v_00_u03b1_299_, v_ref_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec(v___y_301_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(lean_object* v_c_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v_p_325_; lean_object* v_toCold_326_; lean_object* v_currRecDepth_327_; lean_object* v_ref_328_; uint16_t v_optionFlags_329_; uint8_t v_suppressElabErrors_330_; uint8_t v_checkDeprecated_331_; uint8_t v_isRecordingDeps_332_; lean_object* v_maxRecDepth_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v_p_325_ = lean_ctor_get(v_c_313_, 0);
v_toCold_326_ = lean_ctor_get(v_a_322_, 0);
lean_inc_ref(v_toCold_326_);
v_currRecDepth_327_ = lean_ctor_get(v_a_322_, 1);
lean_inc(v_currRecDepth_327_);
v_ref_328_ = lean_ctor_get(v_a_322_, 2);
lean_inc(v_ref_328_);
v_optionFlags_329_ = lean_ctor_get_uint16(v_a_322_, sizeof(void*)*3);
v_suppressElabErrors_330_ = lean_ctor_get_uint8(v_a_322_, sizeof(void*)*3 + 2);
v_checkDeprecated_331_ = lean_ctor_get_uint8(v_a_322_, sizeof(void*)*3 + 3);
v_isRecordingDeps_332_ = lean_ctor_get_uint8(v_a_322_, sizeof(void*)*3 + 4);
lean_dec_ref(v_a_322_);
v_maxRecDepth_364_ = lean_ctor_get(v_toCold_326_, 3);
v___x_365_ = lean_unsigned_to_nat(0u);
v___x_366_ = lean_nat_dec_eq(v_maxRecDepth_364_, v___x_365_);
if (v___x_366_ == 0)
{
uint8_t v___x_367_; 
v___x_367_ = lean_nat_dec_eq(v_currRecDepth_327_, v_maxRecDepth_364_);
if (v___x_367_ == 0)
{
goto v___jp_333_;
}
else
{
lean_object* v___x_368_; 
lean_dec(v_currRecDepth_327_);
lean_dec_ref(v_toCold_326_);
lean_dec_ref(v_c_313_);
v___x_368_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(v_ref_328_);
return v___x_368_;
}
}
else
{
goto v___jp_333_;
}
v___jp_333_:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_334_ = lean_unsigned_to_nat(1u);
v___x_335_ = lean_nat_add(v_currRecDepth_327_, v___x_334_);
lean_dec(v_currRecDepth_327_);
v___x_336_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_336_, 0, v_toCold_326_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
lean_ctor_set(v___x_336_, 2, v_ref_328_);
lean_ctor_set_uint16(v___x_336_, sizeof(void*)*3, v_optionFlags_329_);
lean_ctor_set_uint8(v___x_336_, sizeof(void*)*3 + 2, v_suppressElabErrors_330_);
lean_ctor_set_uint8(v___x_336_, sizeof(void*)*3 + 3, v_checkDeprecated_331_);
lean_ctor_set_uint8(v___x_336_, sizeof(void*)*3 + 4, v_isRecordingDeps_332_);
lean_inc_ref(v_p_325_);
v___x_337_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_325_, v_a_314_, v___x_336_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_355_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_355_ == 0)
{
v___x_340_ = v___x_337_;
v_isShared_341_ = v_isSharedCheck_355_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_355_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
if (lean_obj_tag(v_a_338_) == 1)
{
lean_object* v_val_342_; lean_object* v_snd_343_; lean_object* v_snd_344_; lean_object* v_fst_345_; lean_object* v_fst_346_; lean_object* v_p_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
lean_del_object(v___x_340_);
v_val_342_ = lean_ctor_get(v_a_338_, 0);
lean_inc(v_val_342_);
lean_dec_ref_known(v_a_338_, 1);
v_snd_343_ = lean_ctor_get(v_val_342_, 1);
lean_inc(v_snd_343_);
v_snd_344_ = lean_ctor_get(v_snd_343_, 1);
lean_inc(v_snd_344_);
v_fst_345_ = lean_ctor_get(v_val_342_, 0);
lean_inc(v_fst_345_);
lean_dec(v_val_342_);
v_fst_346_ = lean_ctor_get(v_snd_343_, 0);
lean_inc(v_fst_346_);
lean_dec(v_snd_343_);
v_p_347_ = lean_ctor_get(v_snd_344_, 0);
v___x_348_ = l_Int_Internal_Linear_Poly_coeff(v_p_347_, v_fst_346_);
v___x_349_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(v___x_348_, v_fst_346_, v_snd_344_, v_fst_345_, v_c_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v___x_336_, v_a_323_);
lean_dec(v_fst_345_);
lean_dec(v___x_348_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_a_350_);
lean_dec_ref_known(v___x_349_, 1);
v_c_313_ = v_a_350_;
v_a_322_ = v___x_336_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_336_, 3);
return v___x_349_;
}
}
else
{
lean_object* v___x_353_; 
lean_dec(v_a_338_);
lean_dec_ref_known(v___x_336_, 3);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v_c_313_);
v___x_353_ = v___x_340_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_c_313_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
else
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
lean_dec_ref_known(v___x_336_, 3);
lean_dec_ref(v_c_313_);
v_a_356_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_337_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_337_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
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
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isNegEq(lean_object* v_p_u2081_382_, lean_object* v_p_u2082_383_){
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
lean_object* v_k_389_; lean_object* v_v_390_; lean_object* v_p_391_; lean_object* v_k_392_; lean_object* v_v_393_; lean_object* v_p_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v_k_389_ = lean_ctor_get(v_p_u2081_382_, 0);
v_v_390_ = lean_ctor_get(v_p_u2081_382_, 1);
v_p_391_ = lean_ctor_get(v_p_u2081_382_, 2);
v_k_392_ = lean_ctor_get(v_p_u2082_383_, 0);
v_v_393_ = lean_ctor_get(v_p_u2082_383_, 1);
v_p_394_ = lean_ctor_get(v_p_u2082_383_, 2);
v___x_395_ = lean_int_neg(v_k_392_);
v___x_396_ = lean_int_dec_eq(v_k_389_, v___x_395_);
lean_dec(v___x_395_);
if (v___x_396_ == 0)
{
return v___x_396_;
}
else
{
uint8_t v___x_397_; 
v___x_397_ = lean_nat_dec_eq(v_v_390_, v_v_393_);
if (v___x_397_ == 0)
{
return v___x_397_;
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
uint8_t v___x_399_; 
v___x_399_ = 0;
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isNegEq___boxed(lean_object* v_p_u2081_400_, lean_object* v_p_u2082_401_){
_start:
{
uint8_t v_res_402_; lean_object* v_r_403_; 
v_res_402_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_u2081_400_, v_p_u2082_401_);
lean_dec_ref(v_p_u2082_401_);
lean_dec_ref(v_p_u2081_400_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(lean_object* v_c_404_, lean_object* v_as_405_, size_t v_i_406_, size_t v_stop_407_, lean_object* v_b_408_){
_start:
{
lean_object* v___y_410_; uint8_t v___x_414_; 
v___x_414_ = lean_usize_dec_eq(v_i_406_, v_stop_407_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; lean_object* v_p_416_; lean_object* v_p_417_; uint8_t v___x_418_; 
v___x_415_ = lean_array_uget_borrowed(v_as_405_, v_i_406_);
v_p_416_ = lean_ctor_get(v___x_415_, 0);
v_p_417_ = lean_ctor_get(v_c_404_, 0);
v___x_418_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_416_, v_p_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; 
lean_inc(v___x_415_);
v___x_419_ = l_Lean_PersistentArray_push___redArg(v_b_408_, v___x_415_);
v___y_410_ = v___x_419_;
goto v___jp_409_;
}
else
{
v___y_410_ = v_b_408_;
goto v___jp_409_;
}
}
else
{
return v_b_408_;
}
v___jp_409_:
{
size_t v___x_411_; size_t v___x_412_; 
v___x_411_ = ((size_t)1ULL);
v___x_412_ = lean_usize_add(v_i_406_, v___x_411_);
v_i_406_ = v___x_412_;
v_b_408_ = v___y_410_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1___boxed(lean_object* v_c_420_, lean_object* v_as_421_, lean_object* v_i_422_, lean_object* v_stop_423_, lean_object* v_b_424_){
_start:
{
size_t v_i_boxed_425_; size_t v_stop_boxed_426_; lean_object* v_res_427_; 
v_i_boxed_425_ = lean_unbox_usize(v_i_422_);
lean_dec(v_i_422_);
v_stop_boxed_426_ = lean_unbox_usize(v_stop_423_);
lean_dec(v_stop_423_);
v_res_427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v_c_420_, v_as_421_, v_i_boxed_425_, v_stop_boxed_426_, v_b_424_);
lean_dec_ref(v_as_421_);
lean_dec_ref(v_c_420_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(lean_object* v_c_428_, lean_object* v_x_429_, lean_object* v_x_430_){
_start:
{
if (lean_obj_tag(v_x_429_) == 0)
{
lean_object* v_cs_431_; lean_object* v___x_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v_cs_431_ = lean_ctor_get(v_x_429_, 0);
v___x_432_ = lean_unsigned_to_nat(0u);
v___x_433_ = lean_array_get_size(v_cs_431_);
v___x_434_ = lean_nat_dec_lt(v___x_432_, v___x_433_);
if (v___x_434_ == 0)
{
return v_x_430_;
}
else
{
size_t v___x_435_; size_t v___x_436_; lean_object* v___x_437_; 
v___x_435_ = ((size_t)0ULL);
v___x_436_ = lean_usize_of_nat(v___x_433_);
v___x_437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v_c_428_, v_cs_431_, v___x_435_, v___x_436_, v_x_430_);
return v___x_437_;
}
}
else
{
lean_object* v_vs_438_; lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v_vs_438_ = lean_ctor_get(v_x_429_, 0);
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = lean_array_get_size(v_vs_438_);
v___x_441_ = lean_nat_dec_lt(v___x_439_, v___x_440_);
if (v___x_441_ == 0)
{
return v_x_430_;
}
else
{
size_t v___x_442_; size_t v___x_443_; lean_object* v___x_444_; 
v___x_442_ = ((size_t)0ULL);
v___x_443_ = lean_usize_of_nat(v___x_440_);
v___x_444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v_c_428_, v_vs_438_, v___x_442_, v___x_443_, v_x_430_);
return v___x_444_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(lean_object* v_c_445_, lean_object* v_as_446_, size_t v_i_447_, size_t v_stop_448_, lean_object* v_b_449_){
_start:
{
uint8_t v___x_450_; 
v___x_450_ = lean_usize_dec_eq(v_i_447_, v_stop_448_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; lean_object* v___x_452_; size_t v___x_453_; size_t v___x_454_; 
v___x_451_ = lean_array_uget_borrowed(v_as_446_, v_i_447_);
v___x_452_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v_c_445_, v___x_451_, v_b_449_);
v___x_453_ = ((size_t)1ULL);
v___x_454_ = lean_usize_add(v_i_447_, v___x_453_);
v_i_447_ = v___x_454_;
v_b_449_ = v___x_452_;
goto _start;
}
else
{
return v_b_449_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1___boxed(lean_object* v_c_456_, lean_object* v_as_457_, lean_object* v_i_458_, lean_object* v_stop_459_, lean_object* v_b_460_){
_start:
{
size_t v_i_boxed_461_; size_t v_stop_boxed_462_; lean_object* v_res_463_; 
v_i_boxed_461_ = lean_unbox_usize(v_i_458_);
lean_dec(v_i_458_);
v_stop_boxed_462_ = lean_unbox_usize(v_stop_459_);
lean_dec(v_stop_459_);
v_res_463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v_c_456_, v_as_457_, v_i_boxed_461_, v_stop_boxed_462_, v_b_460_);
lean_dec_ref(v_as_457_);
lean_dec_ref(v_c_456_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2___boxed(lean_object* v_c_464_, lean_object* v_x_465_, lean_object* v_x_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v_c_464_, v_x_465_, v_x_466_);
lean_dec_ref(v_x_465_);
lean_dec_ref(v_c_464_);
return v_res_467_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(lean_object* v_c_469_, lean_object* v_x_470_, size_t v_x_471_, size_t v_x_472_, lean_object* v_x_473_){
_start:
{
if (lean_obj_tag(v_x_470_) == 0)
{
lean_object* v_cs_474_; lean_object* v___x_475_; size_t v___x_476_; lean_object* v_j_477_; lean_object* v___x_478_; size_t v___x_479_; size_t v___x_480_; size_t v___x_481_; size_t v___x_482_; size_t v___x_483_; size_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v_cs_474_ = lean_ctor_get(v_x_470_, 0);
v___x_475_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0);
v___x_476_ = lean_usize_shift_right(v_x_471_, v_x_472_);
v_j_477_ = lean_usize_to_nat(v___x_476_);
v___x_478_ = lean_array_get_borrowed(v___x_475_, v_cs_474_, v_j_477_);
v___x_479_ = ((size_t)1ULL);
v___x_480_ = lean_usize_shift_left(v___x_479_, v_x_472_);
v___x_481_ = lean_usize_sub(v___x_480_, v___x_479_);
v___x_482_ = lean_usize_land(v_x_471_, v___x_481_);
v___x_483_ = ((size_t)5ULL);
v___x_484_ = lean_usize_sub(v_x_472_, v___x_483_);
v___x_485_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v_c_469_, v___x_478_, v___x_482_, v___x_484_, v_x_473_);
v___x_486_ = lean_unsigned_to_nat(1u);
v___x_487_ = lean_nat_add(v_j_477_, v___x_486_);
lean_dec(v_j_477_);
v___x_488_ = lean_array_get_size(v_cs_474_);
v___x_489_ = lean_nat_dec_lt(v___x_487_, v___x_488_);
if (v___x_489_ == 0)
{
lean_dec(v___x_487_);
return v___x_485_;
}
else
{
size_t v___x_490_; size_t v___x_491_; lean_object* v___x_492_; 
v___x_490_ = lean_usize_of_nat(v___x_487_);
lean_dec(v___x_487_);
v___x_491_ = lean_usize_of_nat(v___x_488_);
v___x_492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v_c_469_, v_cs_474_, v___x_490_, v___x_491_, v___x_485_);
return v___x_492_;
}
}
else
{
lean_object* v_vs_493_; lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v_vs_493_ = lean_ctor_get(v_x_470_, 0);
v___x_494_ = lean_usize_to_nat(v_x_471_);
v___x_495_ = lean_array_get_size(v_vs_493_);
v___x_496_ = lean_nat_dec_lt(v___x_494_, v___x_495_);
if (v___x_496_ == 0)
{
lean_dec(v___x_494_);
return v_x_473_;
}
else
{
size_t v___x_497_; size_t v___x_498_; lean_object* v___x_499_; 
v___x_497_ = lean_usize_of_nat(v___x_494_);
lean_dec(v___x_494_);
v___x_498_ = lean_usize_of_nat(v___x_495_);
v___x_499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v_c_469_, v_vs_493_, v___x_497_, v___x_498_, v_x_473_);
return v___x_499_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___boxed(lean_object* v_c_500_, lean_object* v_x_501_, lean_object* v_x_502_, lean_object* v_x_503_, lean_object* v_x_504_){
_start:
{
size_t v_x_1577__boxed_505_; size_t v_x_1578__boxed_506_; lean_object* v_res_507_; 
v_x_1577__boxed_505_ = lean_unbox_usize(v_x_502_);
lean_dec(v_x_502_);
v_x_1578__boxed_506_ = lean_unbox_usize(v_x_503_);
lean_dec(v_x_503_);
v_res_507_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v_c_500_, v_x_501_, v_x_1577__boxed_505_, v_x_1578__boxed_506_, v_x_504_);
lean_dec_ref(v_x_501_);
lean_dec_ref(v_c_500_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(lean_object* v_c_508_, lean_object* v_t_509_, lean_object* v_init_510_, lean_object* v_start_511_){
_start:
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = lean_nat_dec_eq(v_start_511_, v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v_root_514_; lean_object* v_tail_515_; size_t v_shift_516_; lean_object* v_tailOff_517_; uint8_t v___x_518_; 
v_root_514_ = lean_ctor_get(v_t_509_, 0);
v_tail_515_ = lean_ctor_get(v_t_509_, 1);
v_shift_516_ = lean_ctor_get_usize(v_t_509_, 4);
v_tailOff_517_ = lean_ctor_get(v_t_509_, 3);
v___x_518_ = lean_nat_dec_le(v_tailOff_517_, v_start_511_);
if (v___x_518_ == 0)
{
size_t v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_519_ = lean_usize_of_nat(v_start_511_);
v___x_520_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v_c_508_, v_root_514_, v___x_519_, v_shift_516_, v_init_510_);
v___x_521_ = lean_array_get_size(v_tail_515_);
v___x_522_ = lean_nat_dec_lt(v___x_512_, v___x_521_);
if (v___x_522_ == 0)
{
return v___x_520_;
}
else
{
size_t v___x_523_; size_t v___x_524_; lean_object* v___x_525_; 
v___x_523_ = ((size_t)0ULL);
v___x_524_ = lean_usize_of_nat(v___x_521_);
v___x_525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v_c_508_, v_tail_515_, v___x_523_, v___x_524_, v___x_520_);
return v___x_525_;
}
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_526_ = lean_nat_sub(v_start_511_, v_tailOff_517_);
v___x_527_ = lean_array_get_size(v_tail_515_);
v___x_528_ = lean_nat_dec_lt(v___x_526_, v___x_527_);
if (v___x_528_ == 0)
{
lean_dec(v___x_526_);
return v_init_510_;
}
else
{
size_t v___x_529_; size_t v___x_530_; lean_object* v___x_531_; 
v___x_529_ = lean_usize_of_nat(v___x_526_);
lean_dec(v___x_526_);
v___x_530_ = lean_usize_of_nat(v___x_527_);
v___x_531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v_c_508_, v_tail_515_, v___x_529_, v___x_530_, v_init_510_);
return v___x_531_;
}
}
}
else
{
lean_object* v_root_532_; lean_object* v_tail_533_; lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v_root_532_ = lean_ctor_get(v_t_509_, 0);
v_tail_533_ = lean_ctor_get(v_t_509_, 1);
v___x_534_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v_c_508_, v_root_532_, v_init_510_);
v___x_535_ = lean_array_get_size(v_tail_533_);
v___x_536_ = lean_nat_dec_lt(v___x_512_, v___x_535_);
if (v___x_536_ == 0)
{
return v___x_534_;
}
else
{
size_t v___x_537_; size_t v___x_538_; lean_object* v___x_539_; 
v___x_537_ = ((size_t)0ULL);
v___x_538_ = lean_usize_of_nat(v___x_535_);
v___x_539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v_c_508_, v_tail_533_, v___x_537_, v___x_538_, v___x_534_);
return v___x_539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0___boxed(lean_object* v_c_540_, lean_object* v_t_541_, lean_object* v_init_542_, lean_object* v_start_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v_c_540_, v_t_541_, v_init_542_, v_start_543_);
lean_dec(v_start_543_);
lean_dec_ref(v_t_541_);
lean_dec_ref(v_c_540_);
return v_res_544_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_545_ = lean_unsigned_to_nat(32u);
v___x_546_ = lean_mk_empty_array_with_capacity(v___x_545_);
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1(void){
_start:
{
size_t v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_548_ = ((size_t)5ULL);
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = lean_unsigned_to_nat(32u);
v___x_551_ = lean_mk_empty_array_with_capacity(v___x_550_);
v___x_552_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0);
v___x_553_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_553_, 0, v___x_552_);
lean_ctor_set(v___x_553_, 1, v___x_551_);
lean_ctor_set(v___x_553_, 2, v___x_549_);
lean_ctor_set(v___x_553_, 3, v___x_549_);
lean_ctor_set_usize(v___x_553_, 4, v___x_548_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(lean_object* v_c_554_, lean_object* v_x_555_, size_t v_x_556_, size_t v_x_557_){
_start:
{
if (lean_obj_tag(v_x_555_) == 0)
{
lean_object* v_cs_558_; size_t v_j_559_; lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v_cs_558_ = lean_ctor_get(v_x_555_, 0);
v_j_559_ = lean_usize_shift_right(v_x_556_, v_x_557_);
v___x_560_ = lean_usize_to_nat(v_j_559_);
v___x_561_ = lean_array_get_size(v_cs_558_);
v___x_562_ = lean_nat_dec_lt(v___x_560_, v___x_561_);
if (v___x_562_ == 0)
{
lean_dec(v___x_560_);
return v_x_555_;
}
else
{
lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_580_; 
lean_inc_ref(v_cs_558_);
v_isSharedCheck_580_ = !lean_is_exclusive(v_x_555_);
if (v_isSharedCheck_580_ == 0)
{
lean_object* v_unused_581_; 
v_unused_581_ = lean_ctor_get(v_x_555_, 0);
lean_dec(v_unused_581_);
v___x_564_ = v_x_555_;
v_isShared_565_ = v_isSharedCheck_580_;
goto v_resetjp_563_;
}
else
{
lean_dec(v_x_555_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_580_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
size_t v___x_566_; size_t v___x_567_; size_t v___x_568_; size_t v_i_569_; size_t v___x_570_; size_t v_shift_571_; lean_object* v_v_572_; lean_object* v___x_573_; lean_object* v_xs_x27_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
v___x_566_ = ((size_t)1ULL);
v___x_567_ = lean_usize_shift_left(v___x_566_, v_x_557_);
v___x_568_ = lean_usize_sub(v___x_567_, v___x_566_);
v_i_569_ = lean_usize_land(v_x_556_, v___x_568_);
v___x_570_ = ((size_t)5ULL);
v_shift_571_ = lean_usize_sub(v_x_557_, v___x_570_);
v_v_572_ = lean_array_fget(v_cs_558_, v___x_560_);
v___x_573_ = lean_box(0);
v_xs_x27_574_ = lean_array_fset(v_cs_558_, v___x_560_, v___x_573_);
v___x_575_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v_c_554_, v_v_572_, v_i_569_, v_shift_571_);
v___x_576_ = lean_array_fset(v_xs_x27_574_, v___x_560_, v___x_575_);
lean_dec(v___x_560_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_576_);
v___x_578_ = v___x_564_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
else
{
lean_object* v_vs_582_; lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v_vs_582_ = lean_ctor_get(v_x_555_, 0);
v___x_583_ = lean_usize_to_nat(v_x_556_);
v___x_584_ = lean_array_get_size(v_vs_582_);
v___x_585_ = lean_nat_dec_lt(v___x_583_, v___x_584_);
if (v___x_585_ == 0)
{
lean_dec(v___x_583_);
return v_x_555_;
}
else
{
lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_599_; 
lean_inc_ref(v_vs_582_);
v_isSharedCheck_599_ = !lean_is_exclusive(v_x_555_);
if (v_isSharedCheck_599_ == 0)
{
lean_object* v_unused_600_; 
v_unused_600_ = lean_ctor_get(v_x_555_, 0);
lean_dec(v_unused_600_);
v___x_587_ = v_x_555_;
v_isShared_588_ = v_isSharedCheck_599_;
goto v_resetjp_586_;
}
else
{
lean_dec(v_x_555_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_599_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v_v_589_; lean_object* v___x_590_; lean_object* v_xs_x27_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_597_; 
v_v_589_ = lean_array_fget(v_vs_582_, v___x_583_);
v___x_590_ = lean_box(0);
v_xs_x27_591_ = lean_array_fset(v_vs_582_, v___x_583_, v___x_590_);
v___x_592_ = lean_unsigned_to_nat(0u);
v___x_593_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1);
v___x_594_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v_c_554_, v_v_589_, v___x_593_, v___x_592_);
lean_dec(v_v_589_);
v___x_595_ = lean_array_fset(v_xs_x27_591_, v___x_583_, v___x_594_);
lean_dec(v___x_583_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_595_);
v___x_597_ = v___x_587_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___boxed(lean_object* v_c_601_, lean_object* v_x_602_, lean_object* v_x_603_, lean_object* v_x_604_){
_start:
{
size_t v_x_1704__boxed_605_; size_t v_x_1705__boxed_606_; lean_object* v_res_607_; 
v_x_1704__boxed_605_ = lean_unbox_usize(v_x_603_);
lean_dec(v_x_603_);
v_x_1705__boxed_606_ = lean_unbox_usize(v_x_604_);
lean_dec(v_x_604_);
v_res_607_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v_c_601_, v_x_602_, v_x_1704__boxed_605_, v_x_1705__boxed_606_);
lean_dec_ref(v_c_601_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(lean_object* v_c_608_, lean_object* v_t_609_, lean_object* v_i_610_){
_start:
{
lean_object* v_root_611_; lean_object* v_tail_612_; lean_object* v_size_613_; size_t v_shift_614_; lean_object* v_tailOff_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_643_; 
v_root_611_ = lean_ctor_get(v_t_609_, 0);
v_tail_612_ = lean_ctor_get(v_t_609_, 1);
v_size_613_ = lean_ctor_get(v_t_609_, 2);
v_shift_614_ = lean_ctor_get_usize(v_t_609_, 4);
v_tailOff_615_ = lean_ctor_get(v_t_609_, 3);
v_isSharedCheck_643_ = !lean_is_exclusive(v_t_609_);
if (v_isSharedCheck_643_ == 0)
{
v___x_617_ = v_t_609_;
v_isShared_618_ = v_isSharedCheck_643_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_tailOff_615_);
lean_inc(v_size_613_);
lean_inc(v_tail_612_);
lean_inc(v_root_611_);
lean_dec(v_t_609_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_643_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
uint8_t v___x_619_; 
v___x_619_ = lean_nat_dec_le(v_tailOff_615_, v_i_610_);
if (v___x_619_ == 0)
{
size_t v___x_620_; lean_object* v___x_621_; lean_object* v___x_623_; 
v___x_620_ = lean_usize_of_nat(v_i_610_);
v___x_621_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v_c_608_, v_root_611_, v___x_620_, v_shift_614_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_621_);
v___x_623_ = v___x_617_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_621_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_tail_612_);
lean_ctor_set(v_reuseFailAlloc_624_, 2, v_size_613_);
lean_ctor_set(v_reuseFailAlloc_624_, 3, v_tailOff_615_);
lean_ctor_set_usize(v_reuseFailAlloc_624_, 4, v_shift_614_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_625_ = lean_nat_sub(v_i_610_, v_tailOff_615_);
v___x_626_ = lean_array_get_size(v_tail_612_);
v___x_627_ = lean_nat_dec_lt(v___x_625_, v___x_626_);
if (v___x_627_ == 0)
{
lean_object* v___x_629_; 
lean_dec(v___x_625_);
if (v_isShared_618_ == 0)
{
v___x_629_ = v___x_617_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_root_611_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_tail_612_);
lean_ctor_set(v_reuseFailAlloc_630_, 2, v_size_613_);
lean_ctor_set(v_reuseFailAlloc_630_, 3, v_tailOff_615_);
lean_ctor_set_usize(v_reuseFailAlloc_630_, 4, v_shift_614_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
else
{
lean_object* v_v_631_; lean_object* v___x_632_; lean_object* v_xs_x27_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_641_; 
v_v_631_ = lean_array_fget(v_tail_612_, v___x_625_);
v___x_632_ = lean_box(0);
v_xs_x27_633_ = lean_array_fset(v_tail_612_, v___x_625_, v___x_632_);
v___x_634_ = lean_unsigned_to_nat(32u);
v___x_635_ = lean_mk_empty_array_with_capacity(v___x_634_);
lean_dec_ref(v___x_635_);
v___x_636_ = lean_unsigned_to_nat(0u);
v___x_637_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1);
v___x_638_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v_c_608_, v_v_631_, v___x_637_, v___x_636_);
lean_dec(v_v_631_);
v___x_639_ = lean_array_fset(v_xs_x27_633_, v___x_625_, v___x_638_);
lean_dec(v___x_625_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v___x_639_);
v___x_641_ = v___x_617_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_root_611_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_642_, 2, v_size_613_);
lean_ctor_set(v_reuseFailAlloc_642_, 3, v_tailOff_615_);
lean_ctor_set_usize(v_reuseFailAlloc_642_, 4, v_shift_614_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1___boxed(lean_object* v_c_644_, lean_object* v_t_645_, lean_object* v_i_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_c_644_, v_t_645_, v_i_646_);
lean_dec(v_i_646_);
lean_dec_ref(v_c_644_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0(lean_object* v_c_648_, lean_object* v_v_649_, lean_object* v_s_650_){
_start:
{
lean_object* v_vars_651_; lean_object* v_varMap_652_; lean_object* v_varsHistory_653_; lean_object* v_natToIntMap_654_; lean_object* v_natDef_655_; lean_object* v_dvds_656_; lean_object* v_lowers_657_; lean_object* v_uppers_658_; lean_object* v_diseqs_659_; lean_object* v_elimEqs_660_; lean_object* v_active_661_; lean_object* v_elimStack_662_; lean_object* v_occurs_663_; lean_object* v_assignment_664_; lean_object* v_nextCnstrId_665_; uint8_t v_caseSplits_666_; lean_object* v_steps_667_; lean_object* v_penalties_668_; lean_object* v_numReorderRequests_669_; lean_object* v_conflict_x3f_670_; lean_object* v_diseqSplits_671_; lean_object* v_divMod_672_; uint8_t v_usedCommRing_673_; lean_object* v_nonlinearOccs_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_682_; 
v_vars_651_ = lean_ctor_get(v_s_650_, 0);
v_varMap_652_ = lean_ctor_get(v_s_650_, 1);
v_varsHistory_653_ = lean_ctor_get(v_s_650_, 2);
v_natToIntMap_654_ = lean_ctor_get(v_s_650_, 3);
v_natDef_655_ = lean_ctor_get(v_s_650_, 4);
v_dvds_656_ = lean_ctor_get(v_s_650_, 5);
v_lowers_657_ = lean_ctor_get(v_s_650_, 6);
v_uppers_658_ = lean_ctor_get(v_s_650_, 7);
v_diseqs_659_ = lean_ctor_get(v_s_650_, 8);
v_elimEqs_660_ = lean_ctor_get(v_s_650_, 9);
v_active_661_ = lean_ctor_get(v_s_650_, 10);
v_elimStack_662_ = lean_ctor_get(v_s_650_, 11);
v_occurs_663_ = lean_ctor_get(v_s_650_, 12);
v_assignment_664_ = lean_ctor_get(v_s_650_, 13);
v_nextCnstrId_665_ = lean_ctor_get(v_s_650_, 14);
v_caseSplits_666_ = lean_ctor_get_uint8(v_s_650_, sizeof(void*)*22);
v_steps_667_ = lean_ctor_get(v_s_650_, 15);
v_penalties_668_ = lean_ctor_get(v_s_650_, 16);
v_numReorderRequests_669_ = lean_ctor_get(v_s_650_, 17);
v_conflict_x3f_670_ = lean_ctor_get(v_s_650_, 18);
v_diseqSplits_671_ = lean_ctor_get(v_s_650_, 19);
v_divMod_672_ = lean_ctor_get(v_s_650_, 20);
v_usedCommRing_673_ = lean_ctor_get_uint8(v_s_650_, sizeof(void*)*22 + 1);
v_nonlinearOccs_674_ = lean_ctor_get(v_s_650_, 21);
v_isSharedCheck_682_ = !lean_is_exclusive(v_s_650_);
if (v_isSharedCheck_682_ == 0)
{
v___x_676_ = v_s_650_;
v_isShared_677_ = v_isSharedCheck_682_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_nonlinearOccs_674_);
lean_inc(v_divMod_672_);
lean_inc(v_diseqSplits_671_);
lean_inc(v_conflict_x3f_670_);
lean_inc(v_numReorderRequests_669_);
lean_inc(v_penalties_668_);
lean_inc(v_steps_667_);
lean_inc(v_nextCnstrId_665_);
lean_inc(v_assignment_664_);
lean_inc(v_occurs_663_);
lean_inc(v_elimStack_662_);
lean_inc(v_active_661_);
lean_inc(v_elimEqs_660_);
lean_inc(v_diseqs_659_);
lean_inc(v_uppers_658_);
lean_inc(v_lowers_657_);
lean_inc(v_dvds_656_);
lean_inc(v_natDef_655_);
lean_inc(v_natToIntMap_654_);
lean_inc(v_varsHistory_653_);
lean_inc(v_varMap_652_);
lean_inc(v_vars_651_);
lean_dec(v_s_650_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_682_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v___x_680_; 
v___x_678_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_c_648_, v_uppers_658_, v_v_649_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 7, v___x_678_);
v___x_680_ = v___x_676_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_vars_651_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_varMap_652_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v_varsHistory_653_);
lean_ctor_set(v_reuseFailAlloc_681_, 3, v_natToIntMap_654_);
lean_ctor_set(v_reuseFailAlloc_681_, 4, v_natDef_655_);
lean_ctor_set(v_reuseFailAlloc_681_, 5, v_dvds_656_);
lean_ctor_set(v_reuseFailAlloc_681_, 6, v_lowers_657_);
lean_ctor_set(v_reuseFailAlloc_681_, 7, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_681_, 8, v_diseqs_659_);
lean_ctor_set(v_reuseFailAlloc_681_, 9, v_elimEqs_660_);
lean_ctor_set(v_reuseFailAlloc_681_, 10, v_active_661_);
lean_ctor_set(v_reuseFailAlloc_681_, 11, v_elimStack_662_);
lean_ctor_set(v_reuseFailAlloc_681_, 12, v_occurs_663_);
lean_ctor_set(v_reuseFailAlloc_681_, 13, v_assignment_664_);
lean_ctor_set(v_reuseFailAlloc_681_, 14, v_nextCnstrId_665_);
lean_ctor_set(v_reuseFailAlloc_681_, 15, v_steps_667_);
lean_ctor_set(v_reuseFailAlloc_681_, 16, v_penalties_668_);
lean_ctor_set(v_reuseFailAlloc_681_, 17, v_numReorderRequests_669_);
lean_ctor_set(v_reuseFailAlloc_681_, 18, v_conflict_x3f_670_);
lean_ctor_set(v_reuseFailAlloc_681_, 19, v_diseqSplits_671_);
lean_ctor_set(v_reuseFailAlloc_681_, 20, v_divMod_672_);
lean_ctor_set(v_reuseFailAlloc_681_, 21, v_nonlinearOccs_674_);
lean_ctor_set_uint8(v_reuseFailAlloc_681_, sizeof(void*)*22, v_caseSplits_666_);
lean_ctor_set_uint8(v_reuseFailAlloc_681_, sizeof(void*)*22 + 1, v_usedCommRing_673_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___boxed(lean_object* v_c_683_, lean_object* v_v_684_, lean_object* v_s_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0(v_c_683_, v_v_684_, v_s_685_);
lean_dec(v_v_684_);
lean_dec_ref(v_c_683_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1(lean_object* v_c_687_, lean_object* v_v_688_, lean_object* v_s_689_){
_start:
{
lean_object* v_vars_690_; lean_object* v_varMap_691_; lean_object* v_varsHistory_692_; lean_object* v_natToIntMap_693_; lean_object* v_natDef_694_; lean_object* v_dvds_695_; lean_object* v_lowers_696_; lean_object* v_uppers_697_; lean_object* v_diseqs_698_; lean_object* v_elimEqs_699_; lean_object* v_active_700_; lean_object* v_elimStack_701_; lean_object* v_occurs_702_; lean_object* v_assignment_703_; lean_object* v_nextCnstrId_704_; uint8_t v_caseSplits_705_; lean_object* v_steps_706_; lean_object* v_penalties_707_; lean_object* v_numReorderRequests_708_; lean_object* v_conflict_x3f_709_; lean_object* v_diseqSplits_710_; lean_object* v_divMod_711_; uint8_t v_usedCommRing_712_; lean_object* v_nonlinearOccs_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_721_; 
v_vars_690_ = lean_ctor_get(v_s_689_, 0);
v_varMap_691_ = lean_ctor_get(v_s_689_, 1);
v_varsHistory_692_ = lean_ctor_get(v_s_689_, 2);
v_natToIntMap_693_ = lean_ctor_get(v_s_689_, 3);
v_natDef_694_ = lean_ctor_get(v_s_689_, 4);
v_dvds_695_ = lean_ctor_get(v_s_689_, 5);
v_lowers_696_ = lean_ctor_get(v_s_689_, 6);
v_uppers_697_ = lean_ctor_get(v_s_689_, 7);
v_diseqs_698_ = lean_ctor_get(v_s_689_, 8);
v_elimEqs_699_ = lean_ctor_get(v_s_689_, 9);
v_active_700_ = lean_ctor_get(v_s_689_, 10);
v_elimStack_701_ = lean_ctor_get(v_s_689_, 11);
v_occurs_702_ = lean_ctor_get(v_s_689_, 12);
v_assignment_703_ = lean_ctor_get(v_s_689_, 13);
v_nextCnstrId_704_ = lean_ctor_get(v_s_689_, 14);
v_caseSplits_705_ = lean_ctor_get_uint8(v_s_689_, sizeof(void*)*22);
v_steps_706_ = lean_ctor_get(v_s_689_, 15);
v_penalties_707_ = lean_ctor_get(v_s_689_, 16);
v_numReorderRequests_708_ = lean_ctor_get(v_s_689_, 17);
v_conflict_x3f_709_ = lean_ctor_get(v_s_689_, 18);
v_diseqSplits_710_ = lean_ctor_get(v_s_689_, 19);
v_divMod_711_ = lean_ctor_get(v_s_689_, 20);
v_usedCommRing_712_ = lean_ctor_get_uint8(v_s_689_, sizeof(void*)*22 + 1);
v_nonlinearOccs_713_ = lean_ctor_get(v_s_689_, 21);
v_isSharedCheck_721_ = !lean_is_exclusive(v_s_689_);
if (v_isSharedCheck_721_ == 0)
{
v___x_715_ = v_s_689_;
v_isShared_716_ = v_isSharedCheck_721_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_nonlinearOccs_713_);
lean_inc(v_divMod_711_);
lean_inc(v_diseqSplits_710_);
lean_inc(v_conflict_x3f_709_);
lean_inc(v_numReorderRequests_708_);
lean_inc(v_penalties_707_);
lean_inc(v_steps_706_);
lean_inc(v_nextCnstrId_704_);
lean_inc(v_assignment_703_);
lean_inc(v_occurs_702_);
lean_inc(v_elimStack_701_);
lean_inc(v_active_700_);
lean_inc(v_elimEqs_699_);
lean_inc(v_diseqs_698_);
lean_inc(v_uppers_697_);
lean_inc(v_lowers_696_);
lean_inc(v_dvds_695_);
lean_inc(v_natDef_694_);
lean_inc(v_natToIntMap_693_);
lean_inc(v_varsHistory_692_);
lean_inc(v_varMap_691_);
lean_inc(v_vars_690_);
lean_dec(v_s_689_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_721_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_717_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_c_687_, v_lowers_696_, v_v_688_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 6, v___x_717_);
v___x_719_ = v___x_715_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_vars_690_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_varMap_691_);
lean_ctor_set(v_reuseFailAlloc_720_, 2, v_varsHistory_692_);
lean_ctor_set(v_reuseFailAlloc_720_, 3, v_natToIntMap_693_);
lean_ctor_set(v_reuseFailAlloc_720_, 4, v_natDef_694_);
lean_ctor_set(v_reuseFailAlloc_720_, 5, v_dvds_695_);
lean_ctor_set(v_reuseFailAlloc_720_, 6, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_720_, 7, v_uppers_697_);
lean_ctor_set(v_reuseFailAlloc_720_, 8, v_diseqs_698_);
lean_ctor_set(v_reuseFailAlloc_720_, 9, v_elimEqs_699_);
lean_ctor_set(v_reuseFailAlloc_720_, 10, v_active_700_);
lean_ctor_set(v_reuseFailAlloc_720_, 11, v_elimStack_701_);
lean_ctor_set(v_reuseFailAlloc_720_, 12, v_occurs_702_);
lean_ctor_set(v_reuseFailAlloc_720_, 13, v_assignment_703_);
lean_ctor_set(v_reuseFailAlloc_720_, 14, v_nextCnstrId_704_);
lean_ctor_set(v_reuseFailAlloc_720_, 15, v_steps_706_);
lean_ctor_set(v_reuseFailAlloc_720_, 16, v_penalties_707_);
lean_ctor_set(v_reuseFailAlloc_720_, 17, v_numReorderRequests_708_);
lean_ctor_set(v_reuseFailAlloc_720_, 18, v_conflict_x3f_709_);
lean_ctor_set(v_reuseFailAlloc_720_, 19, v_diseqSplits_710_);
lean_ctor_set(v_reuseFailAlloc_720_, 20, v_divMod_711_);
lean_ctor_set(v_reuseFailAlloc_720_, 21, v_nonlinearOccs_713_);
lean_ctor_set_uint8(v_reuseFailAlloc_720_, sizeof(void*)*22, v_caseSplits_705_);
lean_ctor_set_uint8(v_reuseFailAlloc_720_, sizeof(void*)*22 + 1, v_usedCommRing_712_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1___boxed(lean_object* v_c_722_, lean_object* v_v_723_, lean_object* v_s_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1(v_c_722_, v_v_723_, v_s_724_);
lean_dec(v_v_723_);
lean_dec_ref(v_c_722_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(lean_object* v_c_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
lean_object* v_p_733_; 
v_p_733_ = lean_ctor_get(v_c_726_, 0);
if (lean_obj_tag(v_p_733_) == 1)
{
lean_object* v_k_734_; lean_object* v_v_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v_k_734_ = lean_ctor_get(v_p_733_, 0);
v_v_735_ = lean_ctor_get(v_p_733_, 1);
lean_inc(v_v_735_);
v___x_736_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_737_ = lean_int_dec_lt(v_k_734_, v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___f_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___f_738_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_738_, 0, v_c_726_);
lean_closure_set(v___f_738_, 1, v_v_735_);
v___x_739_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_740_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_739_, v___f_738_, v_a_727_);
return v___x_740_;
}
else
{
lean_object* v___f_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___f_741_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_741_, 0, v_c_726_);
lean_closure_set(v___f_741_, 1, v_v_735_);
v___x_742_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_743_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_742_, v___f_741_, v_a_727_);
return v___x_743_;
}
}
else
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_);
return v___x_744_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___boxed(lean_object* v_c_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_c_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
lean_dec(v_a_748_);
lean_dec_ref(v_a_747_);
lean_dec(v_a_746_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(lean_object* v_c_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_c_753_, v_a_754_, v_a_760_, v_a_761_, v_a_762_, v_a_763_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___boxed(lean_object* v_c_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(v_c_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
lean_dec(v_a_768_);
lean_dec(v_a_767_);
return v_res_778_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_792_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_793_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_794_ = l_Lean_Name_append(v___x_793_, v___x_792_);
return v___x_794_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7(void){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6));
v___x_797_ = l_Lean_stringToMessageData(v___x_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(lean_object* v_c_798_, lean_object* v_as_799_, size_t v_sz_800_, size_t v_i_801_, lean_object* v_b_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
uint8_t v___x_814_; 
v___x_814_ = lean_usize_dec_lt(v_i_801_, v_sz_800_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; 
lean_dec_ref(v_c_798_);
v___x_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_815_, 0, v_b_802_);
return v___x_815_;
}
else
{
lean_object* v_snd_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_905_; 
v_snd_816_ = lean_ctor_get(v_b_802_, 1);
v_isSharedCheck_905_ = !lean_is_exclusive(v_b_802_);
if (v_isSharedCheck_905_ == 0)
{
lean_object* v_unused_906_; 
v_unused_906_ = lean_ctor_get(v_b_802_, 0);
lean_dec(v_unused_906_);
v___x_818_ = v_b_802_;
v_isShared_819_ = v_isSharedCheck_905_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_snd_816_);
lean_dec(v_b_802_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_905_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v_p_820_; lean_object* v_a_821_; lean_object* v_p_822_; lean_object* v___x_823_; uint8_t v___x_824_; 
v_p_820_ = lean_ctor_get(v_c_798_, 0);
v_a_821_ = lean_array_uget_borrowed(v_as_799_, v_i_801_);
v_p_822_ = lean_ctor_get(v_a_821_, 0);
v___x_823_ = lean_box(0);
v___x_824_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_820_, v_p_822_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; size_t v___x_826_; size_t v___x_827_; 
lean_del_object(v___x_818_);
lean_dec(v_snd_816_);
v___x_825_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__1));
v___x_826_ = ((size_t)1ULL);
v___x_827_ = lean_usize_add(v_i_801_, v___x_826_);
v_i_801_ = v___x_827_;
v_b_802_ = v___x_825_;
goto _start;
}
else
{
lean_object* v___x_829_; 
lean_inc_ref(v_p_820_);
lean_inc(v_a_821_);
v___x_829_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_821_, v___y_803_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_toCold_830_; lean_object* v_options_831_; lean_object* v_inheritedTraceOptions_832_; uint8_t v_hasTrace_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; 
lean_dec_ref_known(v___x_829_, 1);
v_toCold_830_ = lean_ctor_get(v___y_811_, 0);
v_options_831_ = lean_ctor_get(v_toCold_830_, 2);
v_inheritedTraceOptions_832_ = lean_ctor_get(v_toCold_830_, 11);
v_hasTrace_833_ = lean_ctor_get_uint8(v_options_831_, sizeof(void*)*1);
lean_inc(v_a_821_);
v___x_834_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_834_, 0, v_c_798_);
lean_ctor_set(v___x_834_, 1, v_a_821_);
v___x_835_ = lean_box(0);
v___x_836_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_836_, 0, v_p_820_);
lean_ctor_set(v___x_836_, 1, v___x_834_);
lean_ctor_set(v___x_836_, 2, v___x_835_);
if (v_hasTrace_833_ == 0)
{
v___y_838_ = v___y_803_;
v___y_839_ = v___y_804_;
v___y_840_ = v___y_805_;
v___y_841_ = v___y_806_;
v___y_842_ = v___y_807_;
v___y_843_ = v___y_808_;
v___y_844_ = v___y_809_;
v___y_845_ = v___y_810_;
v___y_846_ = v___y_811_;
v___y_847_ = v___y_812_;
goto v___jp_837_;
}
else
{
lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_873_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_874_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_875_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_832_, v_options_831_, v___x_874_);
if (v___x_875_ == 0)
{
v___y_838_ = v___y_803_;
v___y_839_ = v___y_804_;
v___y_840_ = v___y_805_;
v___y_841_ = v___y_806_;
v___y_842_ = v___y_807_;
v___y_843_ = v___y_808_;
v___y_844_ = v___y_809_;
v___y_845_ = v___y_810_;
v___y_846_ = v___y_811_;
v___y_847_ = v___y_812_;
goto v___jp_837_;
}
else
{
lean_object* v___x_876_; 
lean_inc_ref(v___x_836_);
v___x_876_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_836_, v___y_803_, v___y_811_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_877_);
lean_dec_ref_known(v___x_876_, 1);
v___x_878_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
lean_ctor_set(v___x_879_, 1, v_a_877_);
v___x_880_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_873_, v___x_879_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_dec_ref_known(v___x_880_, 1);
v___y_838_ = v___y_803_;
v___y_839_ = v___y_804_;
v___y_840_ = v___y_805_;
v___y_841_ = v___y_806_;
v___y_842_ = v___y_807_;
v___y_843_ = v___y_808_;
v___y_844_ = v___y_809_;
v___y_845_ = v___y_810_;
v___y_846_ = v___y_811_;
v___y_847_ = v___y_812_;
goto v___jp_837_;
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec_ref_known(v___x_836_, 3);
lean_del_object(v___x_818_);
lean_dec(v_snd_816_);
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
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
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_dec_ref_known(v___x_836_, 3);
lean_del_object(v___x_818_);
lean_dec(v_snd_816_);
v_a_889_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_876_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_876_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
}
v___jp_837_:
{
lean_object* v___x_848_; 
lean_inc(v___y_847_);
lean_inc_ref(v___y_846_);
lean_inc(v___y_845_);
lean_inc_ref(v___y_844_);
lean_inc(v___y_843_);
lean_inc_ref(v___y_842_);
lean_inc(v___y_841_);
lean_inc_ref(v___y_840_);
lean_inc(v___y_839_);
lean_inc(v___y_838_);
v___x_848_ = lean_grind_cutsat_assert_eq(v___x_836_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_863_; 
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_863_ == 0)
{
lean_object* v_unused_864_; 
v_unused_864_ = lean_ctor_get(v___x_848_, 0);
lean_dec(v_unused_864_);
v___x_850_ = v___x_848_;
v_isShared_851_ = v_isSharedCheck_863_;
goto v_resetjp_849_;
}
else
{
lean_dec(v___x_848_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_863_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_852_ = lean_box(v___x_824_);
v___x_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 1, v___x_823_);
lean_ctor_set(v___x_818_, 0, v___x_853_);
v___x_855_ = v___x_818_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v___x_823_);
v___x_855_ = v_reuseFailAlloc_862_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
v___x_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v_snd_816_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_858_);
v___x_860_ = v___x_850_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_del_object(v___x_818_);
lean_dec(v_snd_816_);
v_a_865_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_848_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_848_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_dec_ref(v_p_820_);
lean_del_object(v___x_818_);
lean_dec(v_snd_816_);
lean_dec_ref(v_c_798_);
v_a_897_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_829_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_829_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_c_907_, lean_object* v_as_908_, lean_object* v_sz_909_, lean_object* v_i_910_, lean_object* v_b_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
size_t v_sz_boxed_923_; size_t v_i_boxed_924_; lean_object* v_res_925_; 
v_sz_boxed_923_ = lean_unbox_usize(v_sz_909_);
lean_dec(v_sz_909_);
v_i_boxed_924_ = lean_unbox_usize(v_i_910_);
lean_dec(v_i_910_);
v_res_925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(v_c_907_, v_as_908_, v_sz_boxed_923_, v_i_boxed_924_, v_b_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v_as_908_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(lean_object* v_c_932_, lean_object* v_as_933_, size_t v_sz_934_, size_t v_i_935_, lean_object* v_b_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
uint8_t v___x_948_; 
v___x_948_ = lean_usize_dec_lt(v_i_935_, v_sz_934_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; 
lean_dec_ref(v_c_932_);
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v_b_936_);
return v___x_949_;
}
else
{
lean_object* v_snd_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_1039_; 
v_snd_950_ = lean_ctor_get(v_b_936_, 1);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_b_936_);
if (v_isSharedCheck_1039_ == 0)
{
lean_object* v_unused_1040_; 
v_unused_1040_ = lean_ctor_get(v_b_936_, 0);
lean_dec(v_unused_1040_);
v___x_952_ = v_b_936_;
v_isShared_953_ = v_isSharedCheck_1039_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_snd_950_);
lean_dec(v_b_936_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_1039_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v_p_954_; lean_object* v_a_955_; lean_object* v_p_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
v_p_954_ = lean_ctor_get(v_c_932_, 0);
v_a_955_ = lean_array_uget_borrowed(v_as_933_, v_i_935_);
v_p_956_ = lean_ctor_get(v_a_955_, 0);
v___x_957_ = lean_box(0);
v___x_958_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_954_, v_p_956_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; size_t v___x_960_; size_t v___x_961_; lean_object* v___x_962_; 
lean_del_object(v___x_952_);
lean_dec(v_snd_950_);
v___x_959_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__1));
v___x_960_ = ((size_t)1ULL);
v___x_961_ = lean_usize_add(v_i_935_, v___x_960_);
v___x_962_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(v_c_932_, v_as_933_, v_sz_934_, v___x_961_, v___x_959_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
return v___x_962_;
}
else
{
lean_object* v___x_963_; 
lean_inc_ref(v_p_954_);
lean_inc(v_a_955_);
v___x_963_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_955_, v___y_937_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_toCold_964_; lean_object* v_options_965_; lean_object* v_inheritedTraceOptions_966_; uint8_t v_hasTrace_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; 
lean_dec_ref_known(v___x_963_, 1);
v_toCold_964_ = lean_ctor_get(v___y_945_, 0);
v_options_965_ = lean_ctor_get(v_toCold_964_, 2);
v_inheritedTraceOptions_966_ = lean_ctor_get(v_toCold_964_, 11);
v_hasTrace_967_ = lean_ctor_get_uint8(v_options_965_, sizeof(void*)*1);
lean_inc(v_a_955_);
v___x_968_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_968_, 0, v_c_932_);
lean_ctor_set(v___x_968_, 1, v_a_955_);
v___x_969_ = lean_box(0);
v___x_970_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_970_, 0, v_p_954_);
lean_ctor_set(v___x_970_, 1, v___x_968_);
lean_ctor_set(v___x_970_, 2, v___x_969_);
if (v_hasTrace_967_ == 0)
{
v___y_972_ = v___y_937_;
v___y_973_ = v___y_938_;
v___y_974_ = v___y_939_;
v___y_975_ = v___y_940_;
v___y_976_ = v___y_941_;
v___y_977_ = v___y_942_;
v___y_978_ = v___y_943_;
v___y_979_ = v___y_944_;
v___y_980_ = v___y_945_;
v___y_981_ = v___y_946_;
goto v___jp_971_;
}
else
{
lean_object* v___x_1007_; lean_object* v___x_1008_; uint8_t v___x_1009_; 
v___x_1007_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1008_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1009_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_966_, v_options_965_, v___x_1008_);
if (v___x_1009_ == 0)
{
v___y_972_ = v___y_937_;
v___y_973_ = v___y_938_;
v___y_974_ = v___y_939_;
v___y_975_ = v___y_940_;
v___y_976_ = v___y_941_;
v___y_977_ = v___y_942_;
v___y_978_ = v___y_943_;
v___y_979_ = v___y_944_;
v___y_980_ = v___y_945_;
v___y_981_ = v___y_946_;
goto v___jp_971_;
}
else
{
lean_object* v___x_1010_; 
lean_inc_ref(v___x_970_);
v___x_1010_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_970_, v___y_937_, v___y_945_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref_known(v___x_1010_, 1);
v___x_1012_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
lean_ctor_set(v___x_1013_, 1, v_a_1011_);
v___x_1014_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1007_, v___x_1013_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_dec_ref_known(v___x_1014_, 1);
v___y_972_ = v___y_937_;
v___y_973_ = v___y_938_;
v___y_974_ = v___y_939_;
v___y_975_ = v___y_940_;
v___y_976_ = v___y_941_;
v___y_977_ = v___y_942_;
v___y_978_ = v___y_943_;
v___y_979_ = v___y_944_;
v___y_980_ = v___y_945_;
v___y_981_ = v___y_946_;
goto v___jp_971_;
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec_ref_known(v___x_970_, 3);
lean_del_object(v___x_952_);
lean_dec(v_snd_950_);
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1014_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1014_);
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
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec_ref_known(v___x_970_, 3);
lean_del_object(v___x_952_);
lean_dec(v_snd_950_);
v_a_1023_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1010_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1010_);
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
v___jp_971_:
{
lean_object* v___x_982_; 
lean_inc(v___y_981_);
lean_inc_ref(v___y_980_);
lean_inc(v___y_979_);
lean_inc_ref(v___y_978_);
lean_inc(v___y_977_);
lean_inc_ref(v___y_976_);
lean_inc(v___y_975_);
lean_inc_ref(v___y_974_);
lean_inc(v___y_973_);
lean_inc(v___y_972_);
v___x_982_ = lean_grind_cutsat_assert_eq(v___x_970_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_997_; 
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_997_ == 0)
{
lean_object* v_unused_998_; 
v_unused_998_ = lean_ctor_get(v___x_982_, 0);
lean_dec(v_unused_998_);
v___x_984_ = v___x_982_;
v_isShared_985_ = v_isSharedCheck_997_;
goto v_resetjp_983_;
}
else
{
lean_dec(v___x_982_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_997_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_986_ = lean_box(v___x_958_);
v___x_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 1, v___x_957_);
lean_ctor_set(v___x_952_, 0, v___x_987_);
v___x_989_ = v___x_952_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v___x_957_);
v___x_989_ = v_reuseFailAlloc_996_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_994_; 
v___x_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
v___x_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
v___x_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
lean_ctor_set(v___x_992_, 1, v_snd_950_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v___x_992_);
v___x_994_ = v___x_984_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_992_);
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
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_del_object(v___x_952_);
lean_dec(v_snd_950_);
v_a_999_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_982_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_982_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_dec_ref(v_p_954_);
lean_del_object(v___x_952_);
lean_dec(v_snd_950_);
lean_dec_ref(v_c_932_);
v_a_1031_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_963_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_963_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___boxed(lean_object* v_c_1041_, lean_object* v_as_1042_, lean_object* v_sz_1043_, lean_object* v_i_1044_, lean_object* v_b_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
size_t v_sz_boxed_1057_; size_t v_i_boxed_1058_; lean_object* v_res_1059_; 
v_sz_boxed_1057_ = lean_unbox_usize(v_sz_1043_);
lean_dec(v_sz_1043_);
v_i_boxed_1058_ = lean_unbox_usize(v_i_1044_);
lean_dec(v_i_1044_);
v_res_1059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(v_c_1041_, v_as_1042_, v_sz_boxed_1057_, v_i_boxed_1058_, v_b_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v_as_1042_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(lean_object* v_init_1060_, lean_object* v_c_1061_, lean_object* v_n_1062_, lean_object* v_b_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
if (lean_obj_tag(v_n_1062_) == 0)
{
lean_object* v_cs_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; size_t v_sz_1078_; size_t v___x_1079_; lean_object* v___x_1080_; 
v_cs_1075_ = lean_ctor_get(v_n_1062_, 0);
v___x_1076_ = lean_box(0);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v_b_1063_);
v_sz_1078_ = lean_array_size(v_cs_1075_);
v___x_1079_ = ((size_t)0ULL);
v___x_1080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v_init_1060_, v_c_1061_, v_cs_1075_, v_sz_1078_, v___x_1079_, v___x_1077_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1095_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1095_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1095_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v_fst_1085_; 
v_fst_1085_ = lean_ctor_get(v_a_1081_, 0);
if (lean_obj_tag(v_fst_1085_) == 0)
{
lean_object* v_snd_1086_; lean_object* v___x_1087_; lean_object* v___x_1089_; 
v_snd_1086_ = lean_ctor_get(v_a_1081_, 1);
lean_inc(v_snd_1086_);
lean_dec(v_a_1081_);
v___x_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1087_, 0, v_snd_1086_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1087_);
v___x_1089_ = v___x_1083_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
else
{
lean_object* v_val_1091_; lean_object* v___x_1093_; 
lean_inc_ref(v_fst_1085_);
lean_dec(v_a_1081_);
v_val_1091_ = lean_ctor_get(v_fst_1085_, 0);
lean_inc(v_val_1091_);
lean_dec_ref_known(v_fst_1085_, 1);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v_val_1091_);
v___x_1093_ = v___x_1083_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_val_1091_);
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
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
v_a_1096_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1080_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1080_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
else
{
lean_object* v_vs_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; size_t v_sz_1107_; size_t v___x_1108_; lean_object* v___x_1109_; 
v_vs_1104_ = lean_ctor_get(v_n_1062_, 0);
v___x_1105_ = lean_box(0);
v___x_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
lean_ctor_set(v___x_1106_, 1, v_b_1063_);
v_sz_1107_ = lean_array_size(v_vs_1104_);
v___x_1108_ = ((size_t)0ULL);
v___x_1109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(v_c_1061_, v_vs_1104_, v_sz_1107_, v___x_1108_, v___x_1106_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1124_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1112_ = v___x_1109_;
v_isShared_1113_ = v_isSharedCheck_1124_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1109_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1124_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v_fst_1114_; 
v_fst_1114_ = lean_ctor_get(v_a_1110_, 0);
if (lean_obj_tag(v_fst_1114_) == 0)
{
lean_object* v_snd_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
v_snd_1115_ = lean_ctor_get(v_a_1110_, 1);
lean_inc(v_snd_1115_);
lean_dec(v_a_1110_);
v___x_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1116_, 0, v_snd_1115_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v___x_1116_);
v___x_1118_ = v___x_1112_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
else
{
lean_object* v_val_1120_; lean_object* v___x_1122_; 
lean_inc_ref(v_fst_1114_);
lean_dec(v_a_1110_);
v_val_1120_ = lean_ctor_get(v_fst_1114_, 0);
lean_inc(v_val_1120_);
lean_dec_ref_known(v_fst_1114_, 1);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v_val_1120_);
v___x_1122_ = v___x_1112_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_val_1120_);
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
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
v_a_1125_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1109_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1109_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(lean_object* v_init_1133_, lean_object* v_c_1134_, lean_object* v_as_1135_, size_t v_sz_1136_, size_t v_i_1137_, lean_object* v_b_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
uint8_t v___x_1150_; 
v___x_1150_ = lean_usize_dec_lt(v_i_1137_, v_sz_1136_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; 
lean_dec_ref(v_c_1134_);
v___x_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1151_, 0, v_b_1138_);
return v___x_1151_;
}
else
{
lean_object* v_snd_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1186_; 
v_snd_1152_ = lean_ctor_get(v_b_1138_, 1);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_b_1138_);
if (v_isSharedCheck_1186_ == 0)
{
lean_object* v_unused_1187_; 
v_unused_1187_ = lean_ctor_get(v_b_1138_, 0);
lean_dec(v_unused_1187_);
v___x_1154_ = v_b_1138_;
v_isShared_1155_ = v_isSharedCheck_1186_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_snd_1152_);
lean_dec(v_b_1138_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1186_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; lean_object* v_a_1157_; lean_object* v___x_1158_; 
v___x_1156_ = lean_box(0);
v_a_1157_ = lean_array_uget_borrowed(v_as_1135_, v_i_1137_);
lean_inc(v_snd_1152_);
lean_inc_ref(v_c_1134_);
v___x_1158_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1133_, v_c_1134_, v_a_1157_, v_snd_1152_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1177_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1161_ = v___x_1158_;
v_isShared_1162_ = v_isSharedCheck_1177_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1158_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1177_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
if (lean_obj_tag(v_a_1159_) == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1165_; 
lean_dec_ref(v_c_1134_);
v___x_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1163_, 0, v_a_1159_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v___x_1163_);
v___x_1165_ = v___x_1154_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1163_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_snd_1152_);
v___x_1165_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1167_; 
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 0, v___x_1165_);
v___x_1167_ = v___x_1161_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; 
lean_del_object(v___x_1161_);
lean_dec(v_snd_1152_);
v_a_1170_ = lean_ctor_get(v_a_1159_, 0);
lean_inc(v_a_1170_);
lean_dec_ref_known(v_a_1159_, 1);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 1, v_a_1170_);
lean_ctor_set(v___x_1154_, 0, v___x_1156_);
v___x_1172_ = v___x_1154_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_a_1170_);
v___x_1172_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
size_t v___x_1173_; size_t v___x_1174_; 
v___x_1173_ = ((size_t)1ULL);
v___x_1174_ = lean_usize_add(v_i_1137_, v___x_1173_);
v_i_1137_ = v___x_1174_;
v_b_1138_ = v___x_1172_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_del_object(v___x_1154_);
lean_dec(v_snd_1152_);
lean_dec_ref(v_c_1134_);
v_a_1178_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1158_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1158_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_1188_ = _args[0];
lean_object* v_c_1189_ = _args[1];
lean_object* v_as_1190_ = _args[2];
lean_object* v_sz_1191_ = _args[3];
lean_object* v_i_1192_ = _args[4];
lean_object* v_b_1193_ = _args[5];
lean_object* v___y_1194_ = _args[6];
lean_object* v___y_1195_ = _args[7];
lean_object* v___y_1196_ = _args[8];
lean_object* v___y_1197_ = _args[9];
lean_object* v___y_1198_ = _args[10];
lean_object* v___y_1199_ = _args[11];
lean_object* v___y_1200_ = _args[12];
lean_object* v___y_1201_ = _args[13];
lean_object* v___y_1202_ = _args[14];
lean_object* v___y_1203_ = _args[15];
lean_object* v___y_1204_ = _args[16];
_start:
{
size_t v_sz_boxed_1205_; size_t v_i_boxed_1206_; lean_object* v_res_1207_; 
v_sz_boxed_1205_ = lean_unbox_usize(v_sz_1191_);
lean_dec(v_sz_1191_);
v_i_boxed_1206_ = lean_unbox_usize(v_i_1192_);
lean_dec(v_i_1192_);
v_res_1207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v_init_1188_, v_c_1189_, v_as_1190_, v_sz_boxed_1205_, v_i_boxed_1206_, v_b_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v_as_1190_);
lean_dec_ref(v_init_1188_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___boxed(lean_object* v_init_1208_, lean_object* v_c_1209_, lean_object* v_n_1210_, lean_object* v_b_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1208_, v_c_1209_, v_n_1210_, v_b_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v_n_1210_);
lean_dec_ref(v_init_1208_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(lean_object* v_c_1230_, lean_object* v_as_1231_, size_t v_sz_1232_, size_t v_i_1233_, lean_object* v_b_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
uint8_t v___x_1246_; 
v___x_1246_ = lean_usize_dec_lt(v_i_1233_, v_sz_1232_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; 
lean_dec_ref(v_c_1230_);
v___x_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1247_, 0, v_b_1234_);
return v___x_1247_;
}
else
{
lean_object* v_snd_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1336_; 
v_snd_1248_ = lean_ctor_get(v_b_1234_, 1);
v_isSharedCheck_1336_ = !lean_is_exclusive(v_b_1234_);
if (v_isSharedCheck_1336_ == 0)
{
lean_object* v_unused_1337_; 
v_unused_1337_ = lean_ctor_get(v_b_1234_, 0);
lean_dec(v_unused_1337_);
v___x_1250_ = v_b_1234_;
v_isShared_1251_ = v_isSharedCheck_1336_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_snd_1248_);
lean_dec(v_b_1234_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1336_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v_p_1252_; lean_object* v_a_1253_; lean_object* v_p_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v_p_1252_ = lean_ctor_get(v_c_1230_, 0);
v_a_1253_ = lean_array_uget_borrowed(v_as_1231_, v_i_1233_);
v_p_1254_ = lean_ctor_get(v_a_1253_, 0);
v___x_1255_ = lean_box(0);
v___x_1256_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_1252_, v_p_1254_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; size_t v___x_1258_; size_t v___x_1259_; 
lean_del_object(v___x_1250_);
lean_dec(v_snd_1248_);
v___x_1257_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__1));
v___x_1258_ = ((size_t)1ULL);
v___x_1259_ = lean_usize_add(v_i_1233_, v___x_1258_);
v_i_1233_ = v___x_1259_;
v_b_1234_ = v___x_1257_;
goto _start;
}
else
{
lean_object* v___x_1261_; 
lean_inc_ref(v_p_1252_);
lean_inc(v_a_1253_);
v___x_1261_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_1253_, v___y_1235_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_toCold_1262_; lean_object* v_options_1263_; lean_object* v_inheritedTraceOptions_1264_; uint8_t v_hasTrace_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; 
lean_dec_ref_known(v___x_1261_, 1);
v_toCold_1262_ = lean_ctor_get(v___y_1243_, 0);
v_options_1263_ = lean_ctor_get(v_toCold_1262_, 2);
v_inheritedTraceOptions_1264_ = lean_ctor_get(v_toCold_1262_, 11);
v_hasTrace_1265_ = lean_ctor_get_uint8(v_options_1263_, sizeof(void*)*1);
lean_inc(v_a_1253_);
v___x_1266_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_1266_, 0, v_c_1230_);
lean_ctor_set(v___x_1266_, 1, v_a_1253_);
v___x_1267_ = lean_box(0);
v___x_1268_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1268_, 0, v_p_1252_);
lean_ctor_set(v___x_1268_, 1, v___x_1266_);
lean_ctor_set(v___x_1268_, 2, v___x_1267_);
if (v_hasTrace_1265_ == 0)
{
v___y_1270_ = v___y_1235_;
v___y_1271_ = v___y_1236_;
v___y_1272_ = v___y_1237_;
v___y_1273_ = v___y_1238_;
v___y_1274_ = v___y_1239_;
v___y_1275_ = v___y_1240_;
v___y_1276_ = v___y_1241_;
v___y_1277_ = v___y_1242_;
v___y_1278_ = v___y_1243_;
v___y_1279_ = v___y_1244_;
goto v___jp_1269_;
}
else
{
lean_object* v___x_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1304_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1305_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1306_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1264_, v_options_1263_, v___x_1305_);
if (v___x_1306_ == 0)
{
v___y_1270_ = v___y_1235_;
v___y_1271_ = v___y_1236_;
v___y_1272_ = v___y_1237_;
v___y_1273_ = v___y_1238_;
v___y_1274_ = v___y_1239_;
v___y_1275_ = v___y_1240_;
v___y_1276_ = v___y_1241_;
v___y_1277_ = v___y_1242_;
v___y_1278_ = v___y_1243_;
v___y_1279_ = v___y_1244_;
goto v___jp_1269_;
}
else
{
lean_object* v___x_1307_; 
lean_inc_ref(v___x_1268_);
v___x_1307_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1268_, v___y_1235_, v___y_1243_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_a_1308_);
lean_dec_ref_known(v___x_1307_, 1);
v___x_1309_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
lean_ctor_set(v___x_1310_, 1, v_a_1308_);
v___x_1311_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1304_, v___x_1310_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_dec_ref_known(v___x_1311_, 1);
v___y_1270_ = v___y_1235_;
v___y_1271_ = v___y_1236_;
v___y_1272_ = v___y_1237_;
v___y_1273_ = v___y_1238_;
v___y_1274_ = v___y_1239_;
v___y_1275_ = v___y_1240_;
v___y_1276_ = v___y_1241_;
v___y_1277_ = v___y_1242_;
v___y_1278_ = v___y_1243_;
v___y_1279_ = v___y_1244_;
goto v___jp_1269_;
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_dec_ref_known(v___x_1268_, 3);
lean_del_object(v___x_1250_);
lean_dec(v_snd_1248_);
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1311_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1311_);
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
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec_ref_known(v___x_1268_, 3);
lean_del_object(v___x_1250_);
lean_dec(v_snd_1248_);
v_a_1320_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1307_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1307_);
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
v___jp_1269_:
{
lean_object* v___x_1280_; 
lean_inc(v___y_1279_);
lean_inc_ref(v___y_1278_);
lean_inc(v___y_1277_);
lean_inc_ref(v___y_1276_);
lean_inc(v___y_1275_);
lean_inc_ref(v___y_1274_);
lean_inc(v___y_1273_);
lean_inc_ref(v___y_1272_);
lean_inc(v___y_1271_);
lean_inc(v___y_1270_);
v___x_1280_ = lean_grind_cutsat_assert_eq(v___x_1268_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1294_; 
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1294_ == 0)
{
lean_object* v_unused_1295_; 
v_unused_1295_ = lean_ctor_get(v___x_1280_, 0);
lean_dec(v_unused_1295_);
v___x_1282_ = v___x_1280_;
v_isShared_1283_ = v_isSharedCheck_1294_;
goto v_resetjp_1281_;
}
else
{
lean_dec(v___x_1280_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1294_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1287_; 
v___x_1284_ = lean_box(v___x_1256_);
v___x_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 1, v___x_1255_);
lean_ctor_set(v___x_1250_, 0, v___x_1285_);
v___x_1287_ = v___x_1250_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1285_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v___x_1255_);
v___x_1287_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
v___x_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
lean_ctor_set(v___x_1289_, 1, v_snd_1248_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 0, v___x_1289_);
v___x_1291_ = v___x_1282_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_del_object(v___x_1250_);
lean_dec(v_snd_1248_);
v_a_1296_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1280_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1280_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec_ref(v_p_1252_);
lean_del_object(v___x_1250_);
lean_dec(v_snd_1248_);
lean_dec_ref(v_c_1230_);
v_a_1328_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1261_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1261_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___boxed(lean_object* v_c_1338_, lean_object* v_as_1339_, lean_object* v_sz_1340_, lean_object* v_i_1341_, lean_object* v_b_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
size_t v_sz_boxed_1354_; size_t v_i_boxed_1355_; lean_object* v_res_1356_; 
v_sz_boxed_1354_ = lean_unbox_usize(v_sz_1340_);
lean_dec(v_sz_1340_);
v_i_boxed_1355_ = lean_unbox_usize(v_i_1341_);
lean_dec(v_i_1341_);
v_res_1356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v_c_1338_, v_as_1339_, v_sz_boxed_1354_, v_i_boxed_1355_, v_b_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v_as_1339_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(lean_object* v_c_1360_, lean_object* v_as_1361_, size_t v_sz_1362_, size_t v_i_1363_, lean_object* v_b_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
uint8_t v___x_1376_; 
v___x_1376_ = lean_usize_dec_lt(v_i_1363_, v_sz_1362_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; 
lean_dec_ref(v_c_1360_);
v___x_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1377_, 0, v_b_1364_);
return v___x_1377_;
}
else
{
lean_object* v_snd_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1466_; 
v_snd_1378_ = lean_ctor_get(v_b_1364_, 1);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_b_1364_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; 
v_unused_1467_ = lean_ctor_get(v_b_1364_, 0);
lean_dec(v_unused_1467_);
v___x_1380_ = v_b_1364_;
v_isShared_1381_ = v_isSharedCheck_1466_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_snd_1378_);
lean_dec(v_b_1364_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1466_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v_p_1382_; lean_object* v_a_1383_; lean_object* v_p_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v_p_1382_ = lean_ctor_get(v_c_1360_, 0);
v_a_1383_ = lean_array_uget_borrowed(v_as_1361_, v_i_1363_);
v_p_1384_ = lean_ctor_get(v_a_1383_, 0);
v___x_1385_ = lean_box(0);
v___x_1386_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_1382_, v_p_1384_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; size_t v___x_1388_; size_t v___x_1389_; lean_object* v___x_1390_; 
lean_del_object(v___x_1380_);
lean_dec(v_snd_1378_);
v___x_1387_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___closed__0));
v___x_1388_ = ((size_t)1ULL);
v___x_1389_ = lean_usize_add(v_i_1363_, v___x_1388_);
v___x_1390_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v_c_1360_, v_as_1361_, v_sz_1362_, v___x_1389_, v___x_1387_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
return v___x_1390_;
}
else
{
lean_object* v___x_1391_; 
lean_inc_ref(v_p_1382_);
lean_inc(v_a_1383_);
v___x_1391_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_1383_, v___y_1365_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_toCold_1392_; lean_object* v_options_1393_; lean_object* v_inheritedTraceOptions_1394_; uint8_t v_hasTrace_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; 
lean_dec_ref_known(v___x_1391_, 1);
v_toCold_1392_ = lean_ctor_get(v___y_1373_, 0);
v_options_1393_ = lean_ctor_get(v_toCold_1392_, 2);
v_inheritedTraceOptions_1394_ = lean_ctor_get(v_toCold_1392_, 11);
v_hasTrace_1395_ = lean_ctor_get_uint8(v_options_1393_, sizeof(void*)*1);
lean_inc(v_a_1383_);
v___x_1396_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_1396_, 0, v_c_1360_);
lean_ctor_set(v___x_1396_, 1, v_a_1383_);
v___x_1397_ = lean_box(0);
v___x_1398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1398_, 0, v_p_1382_);
lean_ctor_set(v___x_1398_, 1, v___x_1396_);
lean_ctor_set(v___x_1398_, 2, v___x_1397_);
if (v_hasTrace_1395_ == 0)
{
v___y_1400_ = v___y_1365_;
v___y_1401_ = v___y_1366_;
v___y_1402_ = v___y_1367_;
v___y_1403_ = v___y_1368_;
v___y_1404_ = v___y_1369_;
v___y_1405_ = v___y_1370_;
v___y_1406_ = v___y_1371_;
v___y_1407_ = v___y_1372_;
v___y_1408_ = v___y_1373_;
v___y_1409_ = v___y_1374_;
goto v___jp_1399_;
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1434_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1435_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1436_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1394_, v_options_1393_, v___x_1435_);
if (v___x_1436_ == 0)
{
v___y_1400_ = v___y_1365_;
v___y_1401_ = v___y_1366_;
v___y_1402_ = v___y_1367_;
v___y_1403_ = v___y_1368_;
v___y_1404_ = v___y_1369_;
v___y_1405_ = v___y_1370_;
v___y_1406_ = v___y_1371_;
v___y_1407_ = v___y_1372_;
v___y_1408_ = v___y_1373_;
v___y_1409_ = v___y_1374_;
goto v___jp_1399_;
}
else
{
lean_object* v___x_1437_; 
lean_inc_ref(v___x_1398_);
v___x_1437_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1398_, v___y_1365_, v___y_1373_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref_known(v___x_1437_, 1);
v___x_1439_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
lean_ctor_set(v___x_1440_, 1, v_a_1438_);
v___x_1441_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1434_, v___x_1440_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_dec_ref_known(v___x_1441_, 1);
v___y_1400_ = v___y_1365_;
v___y_1401_ = v___y_1366_;
v___y_1402_ = v___y_1367_;
v___y_1403_ = v___y_1368_;
v___y_1404_ = v___y_1369_;
v___y_1405_ = v___y_1370_;
v___y_1406_ = v___y_1371_;
v___y_1407_ = v___y_1372_;
v___y_1408_ = v___y_1373_;
v___y_1409_ = v___y_1374_;
goto v___jp_1399_;
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec_ref_known(v___x_1398_, 3);
lean_del_object(v___x_1380_);
lean_dec(v_snd_1378_);
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1441_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1441_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec_ref_known(v___x_1398_, 3);
lean_del_object(v___x_1380_);
lean_dec(v_snd_1378_);
v_a_1450_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1437_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1437_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
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
}
v___jp_1399_:
{
lean_object* v___x_1410_; 
lean_inc(v___y_1409_);
lean_inc_ref(v___y_1408_);
lean_inc(v___y_1407_);
lean_inc_ref(v___y_1406_);
lean_inc(v___y_1405_);
lean_inc_ref(v___y_1404_);
lean_inc(v___y_1403_);
lean_inc_ref(v___y_1402_);
lean_inc(v___y_1401_);
lean_inc(v___y_1400_);
v___x_1410_ = lean_grind_cutsat_assert_eq(v___x_1398_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1424_; 
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1424_ == 0)
{
lean_object* v_unused_1425_; 
v_unused_1425_ = lean_ctor_get(v___x_1410_, 0);
lean_dec(v_unused_1425_);
v___x_1412_ = v___x_1410_;
v_isShared_1413_ = v_isSharedCheck_1424_;
goto v_resetjp_1411_;
}
else
{
lean_dec(v___x_1410_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1424_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1417_; 
v___x_1414_ = lean_box(v___x_1386_);
v___x_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 1, v___x_1385_);
lean_ctor_set(v___x_1380_, 0, v___x_1415_);
v___x_1417_ = v___x_1380_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v___x_1385_);
v___x_1417_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
v___x_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
lean_ctor_set(v___x_1419_, 1, v_snd_1378_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 0, v___x_1419_);
v___x_1421_ = v___x_1412_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1419_);
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
else
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1433_; 
lean_del_object(v___x_1380_);
lean_dec(v_snd_1378_);
v_a_1426_ = lean_ctor_get(v___x_1410_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1428_ = v___x_1410_;
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1410_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1433_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
if (v_isShared_1429_ == 0)
{
v___x_1431_ = v___x_1428_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_a_1426_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec_ref(v_p_1382_);
lean_del_object(v___x_1380_);
lean_dec(v_snd_1378_);
lean_dec_ref(v_c_1360_);
v_a_1458_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1391_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1391_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___boxed(lean_object* v_c_1468_, lean_object* v_as_1469_, lean_object* v_sz_1470_, lean_object* v_i_1471_, lean_object* v_b_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
size_t v_sz_boxed_1484_; size_t v_i_boxed_1485_; lean_object* v_res_1486_; 
v_sz_boxed_1484_ = lean_unbox_usize(v_sz_1470_);
lean_dec(v_sz_1470_);
v_i_boxed_1485_ = lean_unbox_usize(v_i_1471_);
lean_dec(v_i_1471_);
v_res_1486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v_c_1468_, v_as_1469_, v_sz_boxed_1484_, v_i_boxed_1485_, v_b_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v_as_1469_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(lean_object* v_c_1487_, lean_object* v_t_1488_, lean_object* v_init_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_root_1501_; lean_object* v_tail_1502_; lean_object* v___x_1503_; 
v_root_1501_ = lean_ctor_get(v_t_1488_, 0);
v_tail_1502_ = lean_ctor_get(v_t_1488_, 1);
lean_inc_ref(v_c_1487_);
lean_inc_ref(v_init_1489_);
v___x_1503_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1489_, v_c_1487_, v_root_1501_, v_init_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
lean_dec_ref(v_init_1489_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1540_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1506_ = v___x_1503_;
v_isShared_1507_ = v_isSharedCheck_1540_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1503_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1540_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
if (lean_obj_tag(v_a_1504_) == 0)
{
lean_object* v_a_1508_; lean_object* v___x_1510_; 
lean_dec_ref(v_c_1487_);
v_a_1508_ = lean_ctor_get(v_a_1504_, 0);
lean_inc(v_a_1508_);
lean_dec_ref_known(v_a_1504_, 1);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 0, v_a_1508_);
v___x_1510_ = v___x_1506_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1508_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; size_t v_sz_1515_; size_t v___x_1516_; lean_object* v___x_1517_; 
lean_del_object(v___x_1506_);
v_a_1512_ = lean_ctor_get(v_a_1504_, 0);
lean_inc(v_a_1512_);
lean_dec_ref_known(v_a_1504_, 1);
v___x_1513_ = lean_box(0);
v___x_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
lean_ctor_set(v___x_1514_, 1, v_a_1512_);
v_sz_1515_ = lean_array_size(v_tail_1502_);
v___x_1516_ = ((size_t)0ULL);
v___x_1517_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v_c_1487_, v_tail_1502_, v_sz_1515_, v___x_1516_, v___x_1514_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1531_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1520_ = v___x_1517_;
v_isShared_1521_ = v_isSharedCheck_1531_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1517_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1531_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v_fst_1522_; 
v_fst_1522_ = lean_ctor_get(v_a_1518_, 0);
if (lean_obj_tag(v_fst_1522_) == 0)
{
lean_object* v_snd_1523_; lean_object* v___x_1525_; 
v_snd_1523_ = lean_ctor_get(v_a_1518_, 1);
lean_inc(v_snd_1523_);
lean_dec(v_a_1518_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v_snd_1523_);
v___x_1525_ = v___x_1520_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_snd_1523_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
else
{
lean_object* v_val_1527_; lean_object* v___x_1529_; 
lean_inc_ref(v_fst_1522_);
lean_dec(v_a_1518_);
v_val_1527_ = lean_ctor_get(v_fst_1522_, 0);
lean_inc(v_val_1527_);
lean_dec_ref_known(v_fst_1522_, 1);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v_val_1527_);
v___x_1529_ = v___x_1520_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_val_1527_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
v_a_1532_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1517_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1517_);
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
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_dec_ref(v_c_1487_);
v_a_1541_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1503_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1503_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0___boxed(lean_object* v_c_1549_, lean_object* v_t_1550_, lean_object* v_init_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v_c_1549_, v_t_1550_, v_init_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v_t_1550_);
return v_res_1563_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0(void){
_start:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_instInhabitedPersistentArray_default___redArg();
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(lean_object* v_c_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_){
_start:
{
lean_object* v_p_1577_; 
v_p_1577_ = lean_ctor_get(v_c_1565_, 0);
if (lean_obj_tag(v_p_1577_) == 1)
{
lean_object* v_k_1578_; lean_object* v_v_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v_k_1578_ = lean_ctor_get(v_p_1577_, 0);
v_v_1579_ = lean_ctor_get(v_p_1577_, 1);
v___x_1580_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
v___x_1581_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1566_, v_a_1574_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___y_1584_; lean_object* v___x_1610_; uint8_t v___x_1611_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1581_, 1);
v___x_1610_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_1611_ = lean_int_dec_lt(v_k_1578_, v___x_1610_);
if (v___x_1611_ == 0)
{
lean_object* v_lowers_1612_; lean_object* v_size_1613_; uint8_t v___x_1614_; 
v_lowers_1612_ = lean_ctor_get(v_a_1582_, 6);
lean_inc_ref(v_lowers_1612_);
lean_dec(v_a_1582_);
v_size_1613_ = lean_ctor_get(v_lowers_1612_, 2);
v___x_1614_ = lean_nat_dec_lt(v_v_1579_, v_size_1613_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; 
lean_dec_ref(v_lowers_1612_);
v___x_1615_ = l_outOfBounds___redArg(v___x_1580_);
v___y_1584_ = v___x_1615_;
goto v___jp_1583_;
}
else
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1580_, v_lowers_1612_, v_v_1579_);
lean_dec_ref(v_lowers_1612_);
v___y_1584_ = v___x_1616_;
goto v___jp_1583_;
}
}
else
{
lean_object* v_uppers_1617_; lean_object* v_size_1618_; uint8_t v___x_1619_; 
v_uppers_1617_ = lean_ctor_get(v_a_1582_, 7);
lean_inc_ref(v_uppers_1617_);
lean_dec(v_a_1582_);
v_size_1618_ = lean_ctor_get(v_uppers_1617_, 2);
v___x_1619_ = lean_nat_dec_lt(v_v_1579_, v_size_1618_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; 
lean_dec_ref(v_uppers_1617_);
v___x_1620_ = l_outOfBounds___redArg(v___x_1580_);
v___y_1584_ = v___x_1620_;
goto v___jp_1583_;
}
else
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1580_, v_uppers_1617_, v_v_1579_);
lean_dec_ref(v_uppers_1617_);
v___y_1584_ = v___x_1621_;
goto v___jp_1583_;
}
}
v___jp_1583_:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0));
v___x_1586_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v_c_1565_, v___y_1584_, v___x_1585_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_);
lean_dec_ref(v___y_1584_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1601_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1589_ = v___x_1586_;
v_isShared_1590_ = v_isSharedCheck_1601_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1586_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1601_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v_fst_1591_; 
v_fst_1591_ = lean_ctor_get(v_a_1587_, 0);
lean_inc(v_fst_1591_);
lean_dec(v_a_1587_);
if (lean_obj_tag(v_fst_1591_) == 0)
{
uint8_t v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1595_; 
v___x_1592_ = 0;
v___x_1593_ = lean_box(v___x_1592_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 0, v___x_1593_);
v___x_1595_ = v___x_1589_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1593_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
else
{
lean_object* v_val_1597_; lean_object* v___x_1599_; 
v_val_1597_ = lean_ctor_get(v_fst_1591_, 0);
lean_inc(v_val_1597_);
lean_dec_ref_known(v_fst_1591_, 1);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 0, v_val_1597_);
v___x_1599_ = v___x_1589_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_val_1597_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
v_a_1602_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1586_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1586_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec_ref(v_c_1565_);
v_a_1622_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1581_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1581_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
else
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1565_, v_a_1566_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_);
return v___x_1630_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___boxed(lean_object* v_c_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_c_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_);
lean_dec(v_a_1641_);
lean_dec_ref(v_a_1640_);
lean_dec(v_a_1639_);
lean_dec_ref(v_a_1638_);
lean_dec(v_a_1637_);
lean_dec_ref(v_a_1636_);
lean_dec(v_a_1635_);
lean_dec_ref(v_a_1634_);
lean_dec(v_a_1633_);
lean_dec(v_a_1632_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(lean_object* v___x_1644_, lean_object* v_as_1645_, size_t v_i_1646_, size_t v_stop_1647_, lean_object* v_b_1648_){
_start:
{
lean_object* v___y_1650_; uint8_t v___x_1654_; 
v___x_1654_ = lean_usize_dec_eq(v_i_1646_, v_stop_1647_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1655_; lean_object* v_p_1656_; uint8_t v___x_1657_; 
v___x_1655_ = lean_array_uget_borrowed(v_as_1645_, v_i_1646_);
v_p_1656_ = lean_ctor_get(v___x_1655_, 0);
v___x_1657_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_1656_, v___x_1644_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; 
lean_inc(v___x_1655_);
v___x_1658_ = l_Lean_PersistentArray_push___redArg(v_b_1648_, v___x_1655_);
v___y_1650_ = v___x_1658_;
goto v___jp_1649_;
}
else
{
v___y_1650_ = v_b_1648_;
goto v___jp_1649_;
}
}
else
{
return v_b_1648_;
}
v___jp_1649_:
{
size_t v___x_1651_; size_t v___x_1652_; 
v___x_1651_ = ((size_t)1ULL);
v___x_1652_ = lean_usize_add(v_i_1646_, v___x_1651_);
v_i_1646_ = v___x_1652_;
v_b_1648_ = v___y_1650_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1___boxed(lean_object* v___x_1659_, lean_object* v_as_1660_, lean_object* v_i_1661_, lean_object* v_stop_1662_, lean_object* v_b_1663_){
_start:
{
size_t v_i_boxed_1664_; size_t v_stop_boxed_1665_; lean_object* v_res_1666_; 
v_i_boxed_1664_ = lean_unbox_usize(v_i_1661_);
lean_dec(v_i_1661_);
v_stop_boxed_1665_ = lean_unbox_usize(v_stop_1662_);
lean_dec(v_stop_1662_);
v_res_1666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1659_, v_as_1660_, v_i_boxed_1664_, v_stop_boxed_1665_, v_b_1663_);
lean_dec_ref(v_as_1660_);
lean_dec_ref(v___x_1659_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(lean_object* v___x_1667_, lean_object* v_x_1668_, lean_object* v_x_1669_){
_start:
{
if (lean_obj_tag(v_x_1668_) == 0)
{
lean_object* v_cs_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
v_cs_1670_ = lean_ctor_get(v_x_1668_, 0);
v___x_1671_ = lean_unsigned_to_nat(0u);
v___x_1672_ = lean_array_get_size(v_cs_1670_);
v___x_1673_ = lean_nat_dec_lt(v___x_1671_, v___x_1672_);
if (v___x_1673_ == 0)
{
return v_x_1669_;
}
else
{
size_t v___x_1674_; size_t v___x_1675_; lean_object* v___x_1676_; 
v___x_1674_ = ((size_t)0ULL);
v___x_1675_ = lean_usize_of_nat(v___x_1672_);
v___x_1676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1667_, v_cs_1670_, v___x_1674_, v___x_1675_, v_x_1669_);
return v___x_1676_;
}
}
else
{
lean_object* v_vs_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; 
v_vs_1677_ = lean_ctor_get(v_x_1668_, 0);
v___x_1678_ = lean_unsigned_to_nat(0u);
v___x_1679_ = lean_array_get_size(v_vs_1677_);
v___x_1680_ = lean_nat_dec_lt(v___x_1678_, v___x_1679_);
if (v___x_1680_ == 0)
{
return v_x_1669_;
}
else
{
size_t v___x_1681_; size_t v___x_1682_; lean_object* v___x_1683_; 
v___x_1681_ = ((size_t)0ULL);
v___x_1682_ = lean_usize_of_nat(v___x_1679_);
v___x_1683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1667_, v_vs_1677_, v___x_1681_, v___x_1682_, v_x_1669_);
return v___x_1683_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(lean_object* v___x_1684_, lean_object* v_as_1685_, size_t v_i_1686_, size_t v_stop_1687_, lean_object* v_b_1688_){
_start:
{
uint8_t v___x_1689_; 
v___x_1689_ = lean_usize_dec_eq(v_i_1686_, v_stop_1687_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1690_; lean_object* v___x_1691_; size_t v___x_1692_; size_t v___x_1693_; 
v___x_1690_ = lean_array_uget_borrowed(v_as_1685_, v_i_1686_);
v___x_1691_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1684_, v___x_1690_, v_b_1688_);
v___x_1692_ = ((size_t)1ULL);
v___x_1693_ = lean_usize_add(v_i_1686_, v___x_1692_);
v_i_1686_ = v___x_1693_;
v_b_1688_ = v___x_1691_;
goto _start;
}
else
{
return v_b_1688_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v___x_1695_, lean_object* v_as_1696_, lean_object* v_i_1697_, lean_object* v_stop_1698_, lean_object* v_b_1699_){
_start:
{
size_t v_i_boxed_1700_; size_t v_stop_boxed_1701_; lean_object* v_res_1702_; 
v_i_boxed_1700_ = lean_unbox_usize(v_i_1697_);
lean_dec(v_i_1697_);
v_stop_boxed_1701_ = lean_unbox_usize(v_stop_1698_);
lean_dec(v_stop_1698_);
v_res_1702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1695_, v_as_1696_, v_i_boxed_1700_, v_stop_boxed_1701_, v_b_1699_);
lean_dec_ref(v_as_1696_);
lean_dec_ref(v___x_1695_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2___boxed(lean_object* v___x_1703_, lean_object* v_x_1704_, lean_object* v_x_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1703_, v_x_1704_, v_x_1705_);
lean_dec_ref(v_x_1704_);
lean_dec_ref(v___x_1703_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(lean_object* v___x_1707_, lean_object* v_x_1708_, size_t v_x_1709_, size_t v_x_1710_, lean_object* v_x_1711_){
_start:
{
if (lean_obj_tag(v_x_1708_) == 0)
{
lean_object* v_cs_1712_; lean_object* v___x_1713_; size_t v___x_1714_; lean_object* v_j_1715_; lean_object* v___x_1716_; size_t v___x_1717_; size_t v___x_1718_; size_t v___x_1719_; size_t v___x_1720_; size_t v___x_1721_; size_t v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; uint8_t v___x_1727_; 
v_cs_1712_ = lean_ctor_get(v_x_1708_, 0);
v___x_1713_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0);
v___x_1714_ = lean_usize_shift_right(v_x_1709_, v_x_1710_);
v_j_1715_ = lean_usize_to_nat(v___x_1714_);
v___x_1716_ = lean_array_get_borrowed(v___x_1713_, v_cs_1712_, v_j_1715_);
v___x_1717_ = ((size_t)1ULL);
v___x_1718_ = lean_usize_shift_left(v___x_1717_, v_x_1710_);
v___x_1719_ = lean_usize_sub(v___x_1718_, v___x_1717_);
v___x_1720_ = lean_usize_land(v_x_1709_, v___x_1719_);
v___x_1721_ = ((size_t)5ULL);
v___x_1722_ = lean_usize_sub(v_x_1710_, v___x_1721_);
v___x_1723_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1707_, v___x_1716_, v___x_1720_, v___x_1722_, v_x_1711_);
v___x_1724_ = lean_unsigned_to_nat(1u);
v___x_1725_ = lean_nat_add(v_j_1715_, v___x_1724_);
lean_dec(v_j_1715_);
v___x_1726_ = lean_array_get_size(v_cs_1712_);
v___x_1727_ = lean_nat_dec_lt(v___x_1725_, v___x_1726_);
if (v___x_1727_ == 0)
{
lean_dec(v___x_1725_);
return v___x_1723_;
}
else
{
size_t v___x_1728_; size_t v___x_1729_; lean_object* v___x_1730_; 
v___x_1728_ = lean_usize_of_nat(v___x_1725_);
lean_dec(v___x_1725_);
v___x_1729_ = lean_usize_of_nat(v___x_1726_);
v___x_1730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1707_, v_cs_1712_, v___x_1728_, v___x_1729_, v___x_1723_);
return v___x_1730_;
}
}
else
{
lean_object* v_vs_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; uint8_t v___x_1734_; 
v_vs_1731_ = lean_ctor_get(v_x_1708_, 0);
v___x_1732_ = lean_usize_to_nat(v_x_1709_);
v___x_1733_ = lean_array_get_size(v_vs_1731_);
v___x_1734_ = lean_nat_dec_lt(v___x_1732_, v___x_1733_);
if (v___x_1734_ == 0)
{
lean_dec(v___x_1732_);
return v_x_1711_;
}
else
{
size_t v___x_1735_; size_t v___x_1736_; lean_object* v___x_1737_; 
v___x_1735_ = lean_usize_of_nat(v___x_1732_);
lean_dec(v___x_1732_);
v___x_1736_ = lean_usize_of_nat(v___x_1733_);
v___x_1737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1707_, v_vs_1731_, v___x_1735_, v___x_1736_, v_x_1711_);
return v___x_1737_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0___boxed(lean_object* v___x_1738_, lean_object* v_x_1739_, lean_object* v_x_1740_, lean_object* v_x_1741_, lean_object* v_x_1742_){
_start:
{
size_t v_x_21099__boxed_1743_; size_t v_x_21100__boxed_1744_; lean_object* v_res_1745_; 
v_x_21099__boxed_1743_ = lean_unbox_usize(v_x_1740_);
lean_dec(v_x_1740_);
v_x_21100__boxed_1744_ = lean_unbox_usize(v_x_1741_);
lean_dec(v_x_1741_);
v_res_1745_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1738_, v_x_1739_, v_x_21099__boxed_1743_, v_x_21100__boxed_1744_, v_x_1742_);
lean_dec_ref(v_x_1739_);
lean_dec_ref(v___x_1738_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(lean_object* v___x_1746_, lean_object* v_t_1747_, lean_object* v_init_1748_, lean_object* v_start_1749_){
_start:
{
lean_object* v___x_1750_; uint8_t v___x_1751_; 
v___x_1750_ = lean_unsigned_to_nat(0u);
v___x_1751_ = lean_nat_dec_eq(v_start_1749_, v___x_1750_);
if (v___x_1751_ == 0)
{
lean_object* v_root_1752_; lean_object* v_tail_1753_; size_t v_shift_1754_; lean_object* v_tailOff_1755_; uint8_t v___x_1756_; 
v_root_1752_ = lean_ctor_get(v_t_1747_, 0);
v_tail_1753_ = lean_ctor_get(v_t_1747_, 1);
v_shift_1754_ = lean_ctor_get_usize(v_t_1747_, 4);
v_tailOff_1755_ = lean_ctor_get(v_t_1747_, 3);
v___x_1756_ = lean_nat_dec_le(v_tailOff_1755_, v_start_1749_);
if (v___x_1756_ == 0)
{
size_t v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1757_ = lean_usize_of_nat(v_start_1749_);
v___x_1758_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1746_, v_root_1752_, v___x_1757_, v_shift_1754_, v_init_1748_);
v___x_1759_ = lean_array_get_size(v_tail_1753_);
v___x_1760_ = lean_nat_dec_lt(v___x_1750_, v___x_1759_);
if (v___x_1760_ == 0)
{
return v___x_1758_;
}
else
{
size_t v___x_1761_; size_t v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = ((size_t)0ULL);
v___x_1762_ = lean_usize_of_nat(v___x_1759_);
v___x_1763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1746_, v_tail_1753_, v___x_1761_, v___x_1762_, v___x_1758_);
return v___x_1763_;
}
}
else
{
lean_object* v___x_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1764_ = lean_nat_sub(v_start_1749_, v_tailOff_1755_);
v___x_1765_ = lean_array_get_size(v_tail_1753_);
v___x_1766_ = lean_nat_dec_lt(v___x_1764_, v___x_1765_);
if (v___x_1766_ == 0)
{
lean_dec(v___x_1764_);
return v_init_1748_;
}
else
{
size_t v___x_1767_; size_t v___x_1768_; lean_object* v___x_1769_; 
v___x_1767_ = lean_usize_of_nat(v___x_1764_);
lean_dec(v___x_1764_);
v___x_1768_ = lean_usize_of_nat(v___x_1765_);
v___x_1769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1746_, v_tail_1753_, v___x_1767_, v___x_1768_, v_init_1748_);
return v___x_1769_;
}
}
}
else
{
lean_object* v_root_1770_; lean_object* v_tail_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; 
v_root_1770_ = lean_ctor_get(v_t_1747_, 0);
v_tail_1771_ = lean_ctor_get(v_t_1747_, 1);
v___x_1772_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1746_, v_root_1770_, v_init_1748_);
v___x_1773_ = lean_array_get_size(v_tail_1771_);
v___x_1774_ = lean_nat_dec_lt(v___x_1750_, v___x_1773_);
if (v___x_1774_ == 0)
{
return v___x_1772_;
}
else
{
size_t v___x_1775_; size_t v___x_1776_; lean_object* v___x_1777_; 
v___x_1775_ = ((size_t)0ULL);
v___x_1776_ = lean_usize_of_nat(v___x_1773_);
v___x_1777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1746_, v_tail_1771_, v___x_1775_, v___x_1776_, v___x_1772_);
return v___x_1777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0___boxed(lean_object* v___x_1778_, lean_object* v_t_1779_, lean_object* v_init_1780_, lean_object* v_start_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1778_, v_t_1779_, v_init_1780_, v_start_1781_);
lean_dec(v_start_1781_);
lean_dec_ref(v_t_1779_);
lean_dec_ref(v___x_1778_);
return v_res_1782_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1783_ = lean_unsigned_to_nat(32u);
v___x_1784_ = lean_mk_empty_array_with_capacity(v___x_1783_);
v___x_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1784_);
return v___x_1785_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1(void){
_start:
{
size_t v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1786_ = ((size_t)5ULL);
v___x_1787_ = lean_unsigned_to_nat(0u);
v___x_1788_ = lean_unsigned_to_nat(32u);
v___x_1789_ = lean_mk_empty_array_with_capacity(v___x_1788_);
v___x_1790_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0);
v___x_1791_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
lean_ctor_set(v___x_1791_, 1, v___x_1789_);
lean_ctor_set(v___x_1791_, 2, v___x_1787_);
lean_ctor_set(v___x_1791_, 3, v___x_1787_);
lean_ctor_set_usize(v___x_1791_, 4, v___x_1786_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(lean_object* v___x_1792_, lean_object* v_x_1793_, size_t v_x_1794_, size_t v_x_1795_){
_start:
{
if (lean_obj_tag(v_x_1793_) == 0)
{
lean_object* v_cs_1796_; size_t v_j_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; uint8_t v___x_1800_; 
v_cs_1796_ = lean_ctor_get(v_x_1793_, 0);
v_j_1797_ = lean_usize_shift_right(v_x_1794_, v_x_1795_);
v___x_1798_ = lean_usize_to_nat(v_j_1797_);
v___x_1799_ = lean_array_get_size(v_cs_1796_);
v___x_1800_ = lean_nat_dec_lt(v___x_1798_, v___x_1799_);
if (v___x_1800_ == 0)
{
lean_dec(v___x_1798_);
return v_x_1793_;
}
else
{
lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1818_; 
lean_inc_ref(v_cs_1796_);
v_isSharedCheck_1818_ = !lean_is_exclusive(v_x_1793_);
if (v_isSharedCheck_1818_ == 0)
{
lean_object* v_unused_1819_; 
v_unused_1819_ = lean_ctor_get(v_x_1793_, 0);
lean_dec(v_unused_1819_);
v___x_1802_ = v_x_1793_;
v_isShared_1803_ = v_isSharedCheck_1818_;
goto v_resetjp_1801_;
}
else
{
lean_dec(v_x_1793_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1818_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
size_t v___x_1804_; size_t v___x_1805_; size_t v___x_1806_; size_t v_i_1807_; size_t v___x_1808_; size_t v_shift_1809_; lean_object* v_v_1810_; lean_object* v___x_1811_; lean_object* v_xs_x27_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1804_ = ((size_t)1ULL);
v___x_1805_ = lean_usize_shift_left(v___x_1804_, v_x_1795_);
v___x_1806_ = lean_usize_sub(v___x_1805_, v___x_1804_);
v_i_1807_ = lean_usize_land(v_x_1794_, v___x_1806_);
v___x_1808_ = ((size_t)5ULL);
v_shift_1809_ = lean_usize_sub(v_x_1795_, v___x_1808_);
v_v_1810_ = lean_array_fget(v_cs_1796_, v___x_1798_);
v___x_1811_ = lean_box(0);
v_xs_x27_1812_ = lean_array_fset(v_cs_1796_, v___x_1798_, v___x_1811_);
v___x_1813_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1792_, v_v_1810_, v_i_1807_, v_shift_1809_);
v___x_1814_ = lean_array_fset(v_xs_x27_1812_, v___x_1798_, v___x_1813_);
lean_dec(v___x_1798_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v___x_1814_);
v___x_1816_ = v___x_1802_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
else
{
lean_object* v_vs_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; uint8_t v___x_1823_; 
v_vs_1820_ = lean_ctor_get(v_x_1793_, 0);
v___x_1821_ = lean_usize_to_nat(v_x_1794_);
v___x_1822_ = lean_array_get_size(v_vs_1820_);
v___x_1823_ = lean_nat_dec_lt(v___x_1821_, v___x_1822_);
if (v___x_1823_ == 0)
{
lean_dec(v___x_1821_);
return v_x_1793_;
}
else
{
lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1837_; 
lean_inc_ref(v_vs_1820_);
v_isSharedCheck_1837_ = !lean_is_exclusive(v_x_1793_);
if (v_isSharedCheck_1837_ == 0)
{
lean_object* v_unused_1838_; 
v_unused_1838_ = lean_ctor_get(v_x_1793_, 0);
lean_dec(v_unused_1838_);
v___x_1825_ = v_x_1793_;
v_isShared_1826_ = v_isSharedCheck_1837_;
goto v_resetjp_1824_;
}
else
{
lean_dec(v_x_1793_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1837_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v_v_1827_; lean_object* v___x_1828_; lean_object* v_xs_x27_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1835_; 
v_v_1827_ = lean_array_fget(v_vs_1820_, v___x_1821_);
v___x_1828_ = lean_box(0);
v_xs_x27_1829_ = lean_array_fset(v_vs_1820_, v___x_1821_, v___x_1828_);
v___x_1830_ = lean_unsigned_to_nat(0u);
v___x_1831_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1);
v___x_1832_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1792_, v_v_1827_, v___x_1831_, v___x_1830_);
lean_dec(v_v_1827_);
v___x_1833_ = lean_array_fset(v_xs_x27_1829_, v___x_1821_, v___x_1832_);
lean_dec(v___x_1821_);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v___x_1833_);
v___x_1835_ = v___x_1825_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___boxed(lean_object* v___x_1839_, lean_object* v_x_1840_, lean_object* v_x_1841_, lean_object* v_x_1842_){
_start:
{
size_t v_x_21231__boxed_1843_; size_t v_x_21232__boxed_1844_; lean_object* v_res_1845_; 
v_x_21231__boxed_1843_ = lean_unbox_usize(v_x_1841_);
lean_dec(v_x_1841_);
v_x_21232__boxed_1844_ = lean_unbox_usize(v_x_1842_);
lean_dec(v_x_1842_);
v_res_1845_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1839_, v_x_1840_, v_x_21231__boxed_1843_, v_x_21232__boxed_1844_);
lean_dec_ref(v___x_1839_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(lean_object* v___x_1846_, lean_object* v_t_1847_, lean_object* v_i_1848_){
_start:
{
lean_object* v_root_1849_; lean_object* v_tail_1850_; lean_object* v_size_1851_; size_t v_shift_1852_; lean_object* v_tailOff_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1881_; 
v_root_1849_ = lean_ctor_get(v_t_1847_, 0);
v_tail_1850_ = lean_ctor_get(v_t_1847_, 1);
v_size_1851_ = lean_ctor_get(v_t_1847_, 2);
v_shift_1852_ = lean_ctor_get_usize(v_t_1847_, 4);
v_tailOff_1853_ = lean_ctor_get(v_t_1847_, 3);
v_isSharedCheck_1881_ = !lean_is_exclusive(v_t_1847_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1855_ = v_t_1847_;
v_isShared_1856_ = v_isSharedCheck_1881_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_tailOff_1853_);
lean_inc(v_size_1851_);
lean_inc(v_tail_1850_);
lean_inc(v_root_1849_);
lean_dec(v_t_1847_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1881_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
uint8_t v___x_1857_; 
v___x_1857_ = lean_nat_dec_le(v_tailOff_1853_, v_i_1848_);
if (v___x_1857_ == 0)
{
size_t v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1858_ = lean_usize_of_nat(v_i_1848_);
v___x_1859_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1846_, v_root_1849_, v___x_1858_, v_shift_1852_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v___x_1859_);
v___x_1861_ = v___x_1855_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1859_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v_tail_1850_);
lean_ctor_set(v_reuseFailAlloc_1862_, 2, v_size_1851_);
lean_ctor_set(v_reuseFailAlloc_1862_, 3, v_tailOff_1853_);
lean_ctor_set_usize(v_reuseFailAlloc_1862_, 4, v_shift_1852_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1864_; uint8_t v___x_1865_; 
v___x_1863_ = lean_nat_sub(v_i_1848_, v_tailOff_1853_);
v___x_1864_ = lean_array_get_size(v_tail_1850_);
v___x_1865_ = lean_nat_dec_lt(v___x_1863_, v___x_1864_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1867_; 
lean_dec(v___x_1863_);
if (v_isShared_1856_ == 0)
{
v___x_1867_ = v___x_1855_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_root_1849_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v_tail_1850_);
lean_ctor_set(v_reuseFailAlloc_1868_, 2, v_size_1851_);
lean_ctor_set(v_reuseFailAlloc_1868_, 3, v_tailOff_1853_);
lean_ctor_set_usize(v_reuseFailAlloc_1868_, 4, v_shift_1852_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
else
{
lean_object* v_v_1869_; lean_object* v___x_1870_; lean_object* v_xs_x27_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1879_; 
v_v_1869_ = lean_array_fget(v_tail_1850_, v___x_1863_);
v___x_1870_ = lean_box(0);
v_xs_x27_1871_ = lean_array_fset(v_tail_1850_, v___x_1863_, v___x_1870_);
v___x_1872_ = lean_unsigned_to_nat(32u);
v___x_1873_ = lean_mk_empty_array_with_capacity(v___x_1872_);
lean_dec_ref(v___x_1873_);
v___x_1874_ = lean_unsigned_to_nat(0u);
v___x_1875_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1);
v___x_1876_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1846_, v_v_1869_, v___x_1875_, v___x_1874_);
lean_dec(v_v_1869_);
v___x_1877_ = lean_array_fset(v_xs_x27_1871_, v___x_1863_, v___x_1876_);
lean_dec(v___x_1863_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 1, v___x_1877_);
v___x_1879_ = v___x_1855_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_root_1849_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_1880_, 2, v_size_1851_);
lean_ctor_set(v_reuseFailAlloc_1880_, 3, v_tailOff_1853_);
lean_ctor_set_usize(v_reuseFailAlloc_1880_, 4, v_shift_1852_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1___boxed(lean_object* v___x_1882_, lean_object* v_t_1883_, lean_object* v_i_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(v___x_1882_, v_t_1883_, v_i_1884_);
lean_dec(v_i_1884_);
lean_dec_ref(v___x_1882_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(lean_object* v_p_1886_, lean_object* v_x_1887_, lean_object* v_s_1888_){
_start:
{
lean_object* v_vars_1889_; lean_object* v_varMap_1890_; lean_object* v_varsHistory_1891_; lean_object* v_natToIntMap_1892_; lean_object* v_natDef_1893_; lean_object* v_dvds_1894_; lean_object* v_lowers_1895_; lean_object* v_uppers_1896_; lean_object* v_diseqs_1897_; lean_object* v_elimEqs_1898_; lean_object* v_active_1899_; lean_object* v_elimStack_1900_; lean_object* v_occurs_1901_; lean_object* v_assignment_1902_; lean_object* v_nextCnstrId_1903_; uint8_t v_caseSplits_1904_; lean_object* v_steps_1905_; lean_object* v_penalties_1906_; lean_object* v_numReorderRequests_1907_; lean_object* v_conflict_x3f_1908_; lean_object* v_diseqSplits_1909_; lean_object* v_divMod_1910_; uint8_t v_usedCommRing_1911_; lean_object* v_nonlinearOccs_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1920_; 
v_vars_1889_ = lean_ctor_get(v_s_1888_, 0);
v_varMap_1890_ = lean_ctor_get(v_s_1888_, 1);
v_varsHistory_1891_ = lean_ctor_get(v_s_1888_, 2);
v_natToIntMap_1892_ = lean_ctor_get(v_s_1888_, 3);
v_natDef_1893_ = lean_ctor_get(v_s_1888_, 4);
v_dvds_1894_ = lean_ctor_get(v_s_1888_, 5);
v_lowers_1895_ = lean_ctor_get(v_s_1888_, 6);
v_uppers_1896_ = lean_ctor_get(v_s_1888_, 7);
v_diseqs_1897_ = lean_ctor_get(v_s_1888_, 8);
v_elimEqs_1898_ = lean_ctor_get(v_s_1888_, 9);
v_active_1899_ = lean_ctor_get(v_s_1888_, 10);
v_elimStack_1900_ = lean_ctor_get(v_s_1888_, 11);
v_occurs_1901_ = lean_ctor_get(v_s_1888_, 12);
v_assignment_1902_ = lean_ctor_get(v_s_1888_, 13);
v_nextCnstrId_1903_ = lean_ctor_get(v_s_1888_, 14);
v_caseSplits_1904_ = lean_ctor_get_uint8(v_s_1888_, sizeof(void*)*22);
v_steps_1905_ = lean_ctor_get(v_s_1888_, 15);
v_penalties_1906_ = lean_ctor_get(v_s_1888_, 16);
v_numReorderRequests_1907_ = lean_ctor_get(v_s_1888_, 17);
v_conflict_x3f_1908_ = lean_ctor_get(v_s_1888_, 18);
v_diseqSplits_1909_ = lean_ctor_get(v_s_1888_, 19);
v_divMod_1910_ = lean_ctor_get(v_s_1888_, 20);
v_usedCommRing_1911_ = lean_ctor_get_uint8(v_s_1888_, sizeof(void*)*22 + 1);
v_nonlinearOccs_1912_ = lean_ctor_get(v_s_1888_, 21);
v_isSharedCheck_1920_ = !lean_is_exclusive(v_s_1888_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1914_ = v_s_1888_;
v_isShared_1915_ = v_isSharedCheck_1920_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_nonlinearOccs_1912_);
lean_inc(v_divMod_1910_);
lean_inc(v_diseqSplits_1909_);
lean_inc(v_conflict_x3f_1908_);
lean_inc(v_numReorderRequests_1907_);
lean_inc(v_penalties_1906_);
lean_inc(v_steps_1905_);
lean_inc(v_nextCnstrId_1903_);
lean_inc(v_assignment_1902_);
lean_inc(v_occurs_1901_);
lean_inc(v_elimStack_1900_);
lean_inc(v_active_1899_);
lean_inc(v_elimEqs_1898_);
lean_inc(v_diseqs_1897_);
lean_inc(v_uppers_1896_);
lean_inc(v_lowers_1895_);
lean_inc(v_dvds_1894_);
lean_inc(v_natDef_1893_);
lean_inc(v_natToIntMap_1892_);
lean_inc(v_varsHistory_1891_);
lean_inc(v_varMap_1890_);
lean_inc(v_vars_1889_);
lean_dec(v_s_1888_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1920_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1916_; lean_object* v___x_1918_; 
v___x_1916_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(v_p_1886_, v_diseqs_1897_, v_x_1887_);
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 8, v___x_1916_);
v___x_1918_ = v___x_1914_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_vars_1889_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v_varMap_1890_);
lean_ctor_set(v_reuseFailAlloc_1919_, 2, v_varsHistory_1891_);
lean_ctor_set(v_reuseFailAlloc_1919_, 3, v_natToIntMap_1892_);
lean_ctor_set(v_reuseFailAlloc_1919_, 4, v_natDef_1893_);
lean_ctor_set(v_reuseFailAlloc_1919_, 5, v_dvds_1894_);
lean_ctor_set(v_reuseFailAlloc_1919_, 6, v_lowers_1895_);
lean_ctor_set(v_reuseFailAlloc_1919_, 7, v_uppers_1896_);
lean_ctor_set(v_reuseFailAlloc_1919_, 8, v___x_1916_);
lean_ctor_set(v_reuseFailAlloc_1919_, 9, v_elimEqs_1898_);
lean_ctor_set(v_reuseFailAlloc_1919_, 10, v_active_1899_);
lean_ctor_set(v_reuseFailAlloc_1919_, 11, v_elimStack_1900_);
lean_ctor_set(v_reuseFailAlloc_1919_, 12, v_occurs_1901_);
lean_ctor_set(v_reuseFailAlloc_1919_, 13, v_assignment_1902_);
lean_ctor_set(v_reuseFailAlloc_1919_, 14, v_nextCnstrId_1903_);
lean_ctor_set(v_reuseFailAlloc_1919_, 15, v_steps_1905_);
lean_ctor_set(v_reuseFailAlloc_1919_, 16, v_penalties_1906_);
lean_ctor_set(v_reuseFailAlloc_1919_, 17, v_numReorderRequests_1907_);
lean_ctor_set(v_reuseFailAlloc_1919_, 18, v_conflict_x3f_1908_);
lean_ctor_set(v_reuseFailAlloc_1919_, 19, v_diseqSplits_1909_);
lean_ctor_set(v_reuseFailAlloc_1919_, 20, v_divMod_1910_);
lean_ctor_set(v_reuseFailAlloc_1919_, 21, v_nonlinearOccs_1912_);
lean_ctor_set_uint8(v_reuseFailAlloc_1919_, sizeof(void*)*22, v_caseSplits_1904_);
lean_ctor_set_uint8(v_reuseFailAlloc_1919_, sizeof(void*)*22 + 1, v_usedCommRing_1911_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed(lean_object* v_p_1921_, lean_object* v_x_1922_, lean_object* v_s_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(v_p_1921_, v_x_1922_, v_s_1923_);
lean_dec(v_x_1922_);
lean_dec_ref(v_p_1921_);
return v_res_1924_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1925_ = lean_unsigned_to_nat(1u);
v___x_1926_ = lean_nat_to_int(v___x_1925_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(lean_object* v_c_1933_, lean_object* v_x_1934_, lean_object* v_as_1935_, size_t v_sz_1936_, size_t v_i_1937_, lean_object* v_b_1938_, lean_object* v___y_1939_){
_start:
{
uint8_t v___x_1941_; 
v___x_1941_ = lean_usize_dec_lt(v_i_1937_, v_sz_1936_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; 
lean_dec(v_x_1934_);
lean_dec_ref(v_c_1933_);
v___x_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1942_, 0, v_b_1938_);
return v___x_1942_;
}
else
{
lean_object* v_snd_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1989_; 
v_snd_1943_ = lean_ctor_get(v_b_1938_, 1);
v_isSharedCheck_1989_ = !lean_is_exclusive(v_b_1938_);
if (v_isSharedCheck_1989_ == 0)
{
lean_object* v_unused_1990_; 
v_unused_1990_ = lean_ctor_get(v_b_1938_, 0);
lean_dec(v_unused_1990_);
v___x_1945_ = v_b_1938_;
v_isShared_1946_ = v_isSharedCheck_1989_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_snd_1943_);
lean_dec(v_b_1938_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1989_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v_p_1947_; lean_object* v_a_1948_; lean_object* v_p_1949_; lean_object* v___x_1950_; lean_object* v___f_1951_; uint8_t v___x_1983_; 
v_p_1947_ = lean_ctor_get(v_c_1933_, 0);
v_a_1948_ = lean_array_uget_borrowed(v_as_1935_, v_i_1937_);
v_p_1949_ = lean_ctor_get(v_a_1948_, 0);
v___x_1950_ = lean_box(0);
lean_inc(v_x_1934_);
lean_inc_ref(v_p_1949_);
v___f_1951_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1951_, 0, v_p_1949_);
lean_closure_set(v___f_1951_, 1, v_x_1934_);
v___x_1983_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_1947_, v_p_1949_);
if (v___x_1983_ == 0)
{
uint8_t v___x_1984_; 
v___x_1984_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_1947_, v_p_1949_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1985_; size_t v___x_1986_; size_t v___x_1987_; 
lean_dec_ref(v___f_1951_);
lean_del_object(v___x_1945_);
lean_dec(v_snd_1943_);
v___x_1985_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2));
v___x_1986_ = ((size_t)1ULL);
v___x_1987_ = lean_usize_add(v_i_1937_, v___x_1986_);
v_i_1937_ = v___x_1987_;
v_b_1938_ = v___x_1985_;
goto _start;
}
else
{
lean_dec(v_x_1934_);
goto v___jp_1952_;
}
}
else
{
lean_dec(v_x_1934_);
goto v___jp_1952_;
}
v___jp_1952_:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1954_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1953_, v___f_1951_, v___y_1939_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1973_; 
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1973_ == 0)
{
lean_object* v_unused_1974_; 
v_unused_1974_ = lean_ctor_get(v___x_1954_, 0);
lean_dec(v_unused_1974_);
v___x_1956_ = v___x_1954_;
v_isShared_1957_ = v_isSharedCheck_1973_;
goto v_resetjp_1955_;
}
else
{
lean_dec(v___x_1954_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1973_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1966_; 
v___x_1958_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0);
lean_inc_ref(v_p_1947_);
v___x_1959_ = l_Int_Internal_Linear_Poly_addConst(v_p_1947_, v___x_1958_);
lean_inc(v_a_1948_);
v___x_1960_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_1960_, 0, v_c_1933_);
lean_ctor_set(v___x_1960_, 1, v_a_1948_);
v___x_1961_ = lean_box(0);
v___x_1962_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1959_);
lean_ctor_set(v___x_1962_, 1, v___x_1960_);
lean_ctor_set(v___x_1962_, 2, v___x_1961_);
v___x_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
v___x_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 1, v___x_1950_);
lean_ctor_set(v___x_1945_, 0, v___x_1964_);
v___x_1966_ = v___x_1945_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1964_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v___x_1950_);
v___x_1966_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1970_; 
v___x_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1966_);
v___x_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
lean_ctor_set(v___x_1968_, 1, v_snd_1943_);
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
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
lean_del_object(v___x_1945_);
lean_dec(v_snd_1943_);
lean_dec_ref(v_c_1933_);
v_a_1975_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1954_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1954_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___boxed(lean_object* v_c_1991_, lean_object* v_x_1992_, lean_object* v_as_1993_, lean_object* v_sz_1994_, lean_object* v_i_1995_, lean_object* v_b_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
size_t v_sz_boxed_1999_; size_t v_i_boxed_2000_; lean_object* v_res_2001_; 
v_sz_boxed_1999_ = lean_unbox_usize(v_sz_1994_);
lean_dec(v_sz_1994_);
v_i_boxed_2000_ = lean_unbox_usize(v_i_1995_);
lean_dec(v_i_1995_);
v_res_2001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_1991_, v_x_1992_, v_as_1993_, v_sz_boxed_1999_, v_i_boxed_2000_, v_b_1996_, v___y_1997_);
lean_dec(v___y_1997_);
lean_dec_ref(v_as_1993_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(lean_object* v_c_2008_, lean_object* v_x_2009_, lean_object* v_as_2010_, size_t v_sz_2011_, size_t v_i_2012_, lean_object* v_b_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
uint8_t v___x_2025_; 
v___x_2025_ = lean_usize_dec_lt(v_i_2012_, v_sz_2011_);
if (v___x_2025_ == 0)
{
lean_object* v___x_2026_; 
lean_dec(v_x_2009_);
lean_dec_ref(v_c_2008_);
v___x_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2026_, 0, v_b_2013_);
return v___x_2026_;
}
else
{
lean_object* v_snd_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2073_; 
v_snd_2027_ = lean_ctor_get(v_b_2013_, 1);
v_isSharedCheck_2073_ = !lean_is_exclusive(v_b_2013_);
if (v_isSharedCheck_2073_ == 0)
{
lean_object* v_unused_2074_; 
v_unused_2074_ = lean_ctor_get(v_b_2013_, 0);
lean_dec(v_unused_2074_);
v___x_2029_ = v_b_2013_;
v_isShared_2030_ = v_isSharedCheck_2073_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_snd_2027_);
lean_dec(v_b_2013_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2073_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v_p_2031_; lean_object* v_a_2032_; lean_object* v_p_2033_; lean_object* v___x_2034_; lean_object* v___f_2035_; uint8_t v___x_2067_; 
v_p_2031_ = lean_ctor_get(v_c_2008_, 0);
v_a_2032_ = lean_array_uget_borrowed(v_as_2010_, v_i_2012_);
v_p_2033_ = lean_ctor_get(v_a_2032_, 0);
v___x_2034_ = lean_box(0);
lean_inc(v_x_2009_);
lean_inc_ref(v_p_2033_);
v___f_2035_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2035_, 0, v_p_2033_);
lean_closure_set(v___f_2035_, 1, v_x_2009_);
v___x_2067_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_2031_, v_p_2033_);
if (v___x_2067_ == 0)
{
uint8_t v___x_2068_; 
v___x_2068_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_2031_, v_p_2033_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2069_; size_t v___x_2070_; size_t v___x_2071_; lean_object* v___x_2072_; 
lean_dec_ref(v___f_2035_);
lean_del_object(v___x_2029_);
lean_dec(v_snd_2027_);
v___x_2069_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__1));
v___x_2070_ = ((size_t)1ULL);
v___x_2071_ = lean_usize_add(v_i_2012_, v___x_2070_);
v___x_2072_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2008_, v_x_2009_, v_as_2010_, v_sz_2011_, v___x_2071_, v___x_2069_, v___y_2014_);
return v___x_2072_;
}
else
{
lean_dec(v_x_2009_);
goto v___jp_2036_;
}
}
else
{
lean_dec(v_x_2009_);
goto v___jp_2036_;
}
v___jp_2036_:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2038_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2037_, v___f_2035_, v___y_2014_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2057_; 
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; 
v_unused_2058_ = lean_ctor_get(v___x_2038_, 0);
lean_dec(v_unused_2058_);
v___x_2040_ = v___x_2038_;
v_isShared_2041_ = v_isSharedCheck_2057_;
goto v_resetjp_2039_;
}
else
{
lean_dec(v___x_2038_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2057_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2050_; 
v___x_2042_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0);
lean_inc_ref(v_p_2031_);
v___x_2043_ = l_Int_Internal_Linear_Poly_addConst(v_p_2031_, v___x_2042_);
lean_inc(v_a_2032_);
v___x_2044_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_2044_, 0, v_c_2008_);
lean_ctor_set(v___x_2044_, 1, v_a_2032_);
v___x_2045_ = lean_box(0);
v___x_2046_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2043_);
lean_ctor_set(v___x_2046_, 1, v___x_2044_);
lean_ctor_set(v___x_2046_, 2, v___x_2045_);
v___x_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
v___x_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2047_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 1, v___x_2034_);
lean_ctor_set(v___x_2029_, 0, v___x_2048_);
v___x_2050_ = v___x_2029_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2048_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v___x_2034_);
v___x_2050_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2054_; 
v___x_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
v___x_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
lean_ctor_set(v___x_2052_, 1, v_snd_2027_);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 0, v___x_2052_);
v___x_2054_ = v___x_2040_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_del_object(v___x_2029_);
lean_dec(v_snd_2027_);
lean_dec_ref(v_c_2008_);
v_a_2059_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2038_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2038_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___boxed(lean_object** _args){
lean_object* v_c_2075_ = _args[0];
lean_object* v_x_2076_ = _args[1];
lean_object* v_as_2077_ = _args[2];
lean_object* v_sz_2078_ = _args[3];
lean_object* v_i_2079_ = _args[4];
lean_object* v_b_2080_ = _args[5];
lean_object* v___y_2081_ = _args[6];
lean_object* v___y_2082_ = _args[7];
lean_object* v___y_2083_ = _args[8];
lean_object* v___y_2084_ = _args[9];
lean_object* v___y_2085_ = _args[10];
lean_object* v___y_2086_ = _args[11];
lean_object* v___y_2087_ = _args[12];
lean_object* v___y_2088_ = _args[13];
lean_object* v___y_2089_ = _args[14];
lean_object* v___y_2090_ = _args[15];
lean_object* v___y_2091_ = _args[16];
_start:
{
size_t v_sz_boxed_2092_; size_t v_i_boxed_2093_; lean_object* v_res_2094_; 
v_sz_boxed_2092_ = lean_unbox_usize(v_sz_2078_);
lean_dec(v_sz_2078_);
v_i_boxed_2093_ = lean_unbox_usize(v_i_2079_);
lean_dec(v_i_2079_);
v_res_2094_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_2075_, v_x_2076_, v_as_2077_, v_sz_boxed_2092_, v_i_boxed_2093_, v_b_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
lean_dec(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec_ref(v_as_2077_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(lean_object* v_c_2101_, lean_object* v_x_2102_, lean_object* v_as_2103_, size_t v_sz_2104_, size_t v_i_2105_, lean_object* v_b_2106_, lean_object* v___y_2107_){
_start:
{
uint8_t v___x_2109_; 
v___x_2109_ = lean_usize_dec_lt(v_i_2105_, v_sz_2104_);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; 
lean_dec(v_x_2102_);
lean_dec_ref(v_c_2101_);
v___x_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2110_, 0, v_b_2106_);
return v___x_2110_;
}
else
{
lean_object* v_snd_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2158_; 
v_snd_2111_ = lean_ctor_get(v_b_2106_, 1);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_b_2106_);
if (v_isSharedCheck_2158_ == 0)
{
lean_object* v_unused_2159_; 
v_unused_2159_ = lean_ctor_get(v_b_2106_, 0);
lean_dec(v_unused_2159_);
v___x_2113_ = v_b_2106_;
v_isShared_2114_ = v_isSharedCheck_2158_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_snd_2111_);
lean_dec(v_b_2106_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2158_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v_p_2115_; lean_object* v_a_2116_; lean_object* v_p_2117_; lean_object* v___x_2118_; lean_object* v___f_2119_; uint8_t v___x_2152_; 
v_p_2115_ = lean_ctor_get(v_c_2101_, 0);
v_a_2116_ = lean_array_uget_borrowed(v_as_2103_, v_i_2105_);
v_p_2117_ = lean_ctor_get(v_a_2116_, 0);
v___x_2118_ = lean_box(0);
lean_inc(v_x_2102_);
lean_inc_ref(v_p_2117_);
v___f_2119_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2119_, 0, v_p_2117_);
lean_closure_set(v___f_2119_, 1, v_x_2102_);
v___x_2152_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_2115_, v_p_2117_);
if (v___x_2152_ == 0)
{
uint8_t v___x_2153_; 
v___x_2153_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_2115_, v_p_2117_);
if (v___x_2153_ == 0)
{
lean_object* v___x_2154_; size_t v___x_2155_; size_t v___x_2156_; 
lean_dec_ref(v___f_2119_);
lean_del_object(v___x_2113_);
lean_dec(v_snd_2111_);
v___x_2154_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__1));
v___x_2155_ = ((size_t)1ULL);
v___x_2156_ = lean_usize_add(v_i_2105_, v___x_2155_);
v_i_2105_ = v___x_2156_;
v_b_2106_ = v___x_2154_;
goto _start;
}
else
{
lean_dec(v_x_2102_);
goto v___jp_2120_;
}
}
else
{
lean_dec(v_x_2102_);
goto v___jp_2120_;
}
v___jp_2120_:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2122_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2121_, v___f_2119_, v___y_2107_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2142_; 
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2142_ == 0)
{
lean_object* v_unused_2143_; 
v_unused_2143_ = lean_ctor_get(v___x_2122_, 0);
lean_dec(v_unused_2143_);
v___x_2124_ = v___x_2122_;
v_isShared_2125_ = v_isSharedCheck_2142_;
goto v_resetjp_2123_;
}
else
{
lean_dec(v___x_2122_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2142_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2134_; 
v___x_2126_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0);
lean_inc_ref(v_p_2115_);
v___x_2127_ = l_Int_Internal_Linear_Poly_addConst(v_p_2115_, v___x_2126_);
lean_inc(v_a_2116_);
v___x_2128_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_2128_, 0, v_c_2101_);
lean_ctor_set(v___x_2128_, 1, v_a_2116_);
v___x_2129_ = lean_box(0);
v___x_2130_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2127_);
lean_ctor_set(v___x_2130_, 1, v___x_2128_);
lean_ctor_set(v___x_2130_, 2, v___x_2129_);
v___x_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
v___x_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 1, v___x_2118_);
lean_ctor_set(v___x_2113_, 0, v___x_2132_);
v___x_2134_ = v___x_2113_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2132_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v___x_2118_);
v___x_2134_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2139_; 
v___x_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2134_);
v___x_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
v___x_2137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2136_);
lean_ctor_set(v___x_2137_, 1, v_snd_2111_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2137_);
v___x_2139_ = v___x_2124_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_del_object(v___x_2113_);
lean_dec(v_snd_2111_);
lean_dec_ref(v_c_2101_);
v_a_2144_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2122_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2122_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___boxed(lean_object* v_c_2160_, lean_object* v_x_2161_, lean_object* v_as_2162_, lean_object* v_sz_2163_, lean_object* v_i_2164_, lean_object* v_b_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
size_t v_sz_boxed_2168_; size_t v_i_boxed_2169_; lean_object* v_res_2170_; 
v_sz_boxed_2168_ = lean_unbox_usize(v_sz_2163_);
lean_dec(v_sz_2163_);
v_i_boxed_2169_ = lean_unbox_usize(v_i_2164_);
lean_dec(v_i_2164_);
v_res_2170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2160_, v_x_2161_, v_as_2162_, v_sz_boxed_2168_, v_i_boxed_2169_, v_b_2165_, v___y_2166_);
lean_dec(v___y_2166_);
lean_dec_ref(v_as_2162_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(lean_object* v_c_2174_, lean_object* v_x_2175_, lean_object* v_as_2176_, size_t v_sz_2177_, size_t v_i_2178_, lean_object* v_b_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
uint8_t v___x_2191_; 
v___x_2191_ = lean_usize_dec_lt(v_i_2178_, v_sz_2177_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; 
lean_dec(v_x_2175_);
lean_dec_ref(v_c_2174_);
v___x_2192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2192_, 0, v_b_2179_);
return v___x_2192_;
}
else
{
lean_object* v_snd_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2240_; 
v_snd_2193_ = lean_ctor_get(v_b_2179_, 1);
v_isSharedCheck_2240_ = !lean_is_exclusive(v_b_2179_);
if (v_isSharedCheck_2240_ == 0)
{
lean_object* v_unused_2241_; 
v_unused_2241_ = lean_ctor_get(v_b_2179_, 0);
lean_dec(v_unused_2241_);
v___x_2195_ = v_b_2179_;
v_isShared_2196_ = v_isSharedCheck_2240_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_snd_2193_);
lean_dec(v_b_2179_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2240_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v_p_2197_; lean_object* v_a_2198_; lean_object* v_p_2199_; lean_object* v___x_2200_; lean_object* v___f_2201_; uint8_t v___x_2234_; 
v_p_2197_ = lean_ctor_get(v_c_2174_, 0);
v_a_2198_ = lean_array_uget_borrowed(v_as_2176_, v_i_2178_);
v_p_2199_ = lean_ctor_get(v_a_2198_, 0);
v___x_2200_ = lean_box(0);
lean_inc(v_x_2175_);
lean_inc_ref(v_p_2199_);
v___f_2201_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2201_, 0, v_p_2199_);
lean_closure_set(v___f_2201_, 1, v_x_2175_);
v___x_2234_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_2197_, v_p_2199_);
if (v___x_2234_ == 0)
{
uint8_t v___x_2235_; 
v___x_2235_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_2197_, v_p_2199_);
if (v___x_2235_ == 0)
{
lean_object* v___x_2236_; size_t v___x_2237_; size_t v___x_2238_; lean_object* v___x_2239_; 
lean_dec_ref(v___f_2201_);
lean_del_object(v___x_2195_);
lean_dec(v_snd_2193_);
v___x_2236_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___closed__0));
v___x_2237_ = ((size_t)1ULL);
v___x_2238_ = lean_usize_add(v_i_2178_, v___x_2237_);
v___x_2239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2174_, v_x_2175_, v_as_2176_, v_sz_2177_, v___x_2238_, v___x_2236_, v___y_2180_);
return v___x_2239_;
}
else
{
lean_dec(v_x_2175_);
goto v___jp_2202_;
}
}
else
{
lean_dec(v_x_2175_);
goto v___jp_2202_;
}
v___jp_2202_:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2204_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2203_, v___f_2201_, v___y_2180_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2224_; 
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2224_ == 0)
{
lean_object* v_unused_2225_; 
v_unused_2225_ = lean_ctor_get(v___x_2204_, 0);
lean_dec(v_unused_2225_);
v___x_2206_ = v___x_2204_;
v_isShared_2207_ = v_isSharedCheck_2224_;
goto v_resetjp_2205_;
}
else
{
lean_dec(v___x_2204_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2224_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2216_; 
v___x_2208_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0);
lean_inc_ref(v_p_2197_);
v___x_2209_ = l_Int_Internal_Linear_Poly_addConst(v_p_2197_, v___x_2208_);
lean_inc(v_a_2198_);
v___x_2210_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v___x_2210_, 0, v_c_2174_);
lean_ctor_set(v___x_2210_, 1, v_a_2198_);
v___x_2211_ = lean_box(0);
v___x_2212_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2209_);
lean_ctor_set(v___x_2212_, 1, v___x_2210_);
lean_ctor_set(v___x_2212_, 2, v___x_2211_);
v___x_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
v___x_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 1, v___x_2200_);
lean_ctor_set(v___x_2195_, 0, v___x_2214_);
v___x_2216_ = v___x_2195_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2214_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v___x_2200_);
v___x_2216_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2221_; 
v___x_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
v___x_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
v___x_2219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
lean_ctor_set(v___x_2219_, 1, v_snd_2193_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v___x_2219_);
v___x_2221_ = v___x_2206_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2219_);
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
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_del_object(v___x_2195_);
lean_dec(v_snd_2193_);
lean_dec_ref(v_c_2174_);
v_a_2226_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2204_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2204_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___boxed(lean_object** _args){
lean_object* v_c_2242_ = _args[0];
lean_object* v_x_2243_ = _args[1];
lean_object* v_as_2244_ = _args[2];
lean_object* v_sz_2245_ = _args[3];
lean_object* v_i_2246_ = _args[4];
lean_object* v_b_2247_ = _args[5];
lean_object* v___y_2248_ = _args[6];
lean_object* v___y_2249_ = _args[7];
lean_object* v___y_2250_ = _args[8];
lean_object* v___y_2251_ = _args[9];
lean_object* v___y_2252_ = _args[10];
lean_object* v___y_2253_ = _args[11];
lean_object* v___y_2254_ = _args[12];
lean_object* v___y_2255_ = _args[13];
lean_object* v___y_2256_ = _args[14];
lean_object* v___y_2257_ = _args[15];
lean_object* v___y_2258_ = _args[16];
_start:
{
size_t v_sz_boxed_2259_; size_t v_i_boxed_2260_; lean_object* v_res_2261_; 
v_sz_boxed_2259_ = lean_unbox_usize(v_sz_2245_);
lean_dec(v_sz_2245_);
v_i_boxed_2260_ = lean_unbox_usize(v_i_2246_);
lean_dec(v_i_2246_);
v_res_2261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_2242_, v_x_2243_, v_as_2244_, v_sz_boxed_2259_, v_i_boxed_2260_, v_b_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v_as_2244_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(lean_object* v_init_2262_, lean_object* v_c_2263_, lean_object* v_x_2264_, lean_object* v_n_2265_, lean_object* v_b_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
if (lean_obj_tag(v_n_2265_) == 0)
{
lean_object* v_cs_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; size_t v_sz_2281_; size_t v___x_2282_; lean_object* v___x_2283_; 
v_cs_2278_ = lean_ctor_get(v_n_2265_, 0);
v___x_2279_ = lean_box(0);
v___x_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
lean_ctor_set(v___x_2280_, 1, v_b_2266_);
v_sz_2281_ = lean_array_size(v_cs_2278_);
v___x_2282_ = ((size_t)0ULL);
v___x_2283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_init_2262_, v_c_2263_, v_x_2264_, v_cs_2278_, v_sz_2281_, v___x_2282_, v___x_2280_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2298_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2286_ = v___x_2283_;
v_isShared_2287_ = v_isSharedCheck_2298_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2283_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2298_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v_fst_2288_; 
v_fst_2288_ = lean_ctor_get(v_a_2284_, 0);
if (lean_obj_tag(v_fst_2288_) == 0)
{
lean_object* v_snd_2289_; lean_object* v___x_2290_; lean_object* v___x_2292_; 
v_snd_2289_ = lean_ctor_get(v_a_2284_, 1);
lean_inc(v_snd_2289_);
lean_dec(v_a_2284_);
v___x_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2290_, 0, v_snd_2289_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v___x_2290_);
v___x_2292_ = v___x_2286_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2290_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
else
{
lean_object* v_val_2294_; lean_object* v___x_2296_; 
lean_inc_ref(v_fst_2288_);
lean_dec(v_a_2284_);
v_val_2294_ = lean_ctor_get(v_fst_2288_, 0);
lean_inc(v_val_2294_);
lean_dec_ref_known(v_fst_2288_, 1);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v_val_2294_);
v___x_2296_ = v___x_2286_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_val_2294_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
v_a_2299_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2283_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2283_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
else
{
lean_object* v_vs_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; size_t v_sz_2310_; size_t v___x_2311_; lean_object* v___x_2312_; 
v_vs_2307_ = lean_ctor_get(v_n_2265_, 0);
v___x_2308_ = lean_box(0);
v___x_2309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
lean_ctor_set(v___x_2309_, 1, v_b_2266_);
v_sz_2310_ = lean_array_size(v_vs_2307_);
v___x_2311_ = ((size_t)0ULL);
v___x_2312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_2263_, v_x_2264_, v_vs_2307_, v_sz_2310_, v___x_2311_, v___x_2309_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2327_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2315_ = v___x_2312_;
v_isShared_2316_ = v_isSharedCheck_2327_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2327_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v_fst_2317_; 
v_fst_2317_ = lean_ctor_get(v_a_2313_, 0);
if (lean_obj_tag(v_fst_2317_) == 0)
{
lean_object* v_snd_2318_; lean_object* v___x_2319_; lean_object* v___x_2321_; 
v_snd_2318_ = lean_ctor_get(v_a_2313_, 1);
lean_inc(v_snd_2318_);
lean_dec(v_a_2313_);
v___x_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2319_, 0, v_snd_2318_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v___x_2319_);
v___x_2321_ = v___x_2315_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2319_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
else
{
lean_object* v_val_2323_; lean_object* v___x_2325_; 
lean_inc_ref(v_fst_2317_);
lean_dec(v_a_2313_);
v_val_2323_ = lean_ctor_get(v_fst_2317_, 0);
lean_inc(v_val_2323_);
lean_dec_ref_known(v_fst_2317_, 1);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v_val_2323_);
v___x_2325_ = v___x_2315_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_val_2323_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
v_a_2328_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2312_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2312_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(lean_object* v_init_2336_, lean_object* v_c_2337_, lean_object* v_x_2338_, lean_object* v_as_2339_, size_t v_sz_2340_, size_t v_i_2341_, lean_object* v_b_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
uint8_t v___x_2354_; 
v___x_2354_ = lean_usize_dec_lt(v_i_2341_, v_sz_2340_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; 
lean_dec(v_x_2338_);
lean_dec_ref(v_c_2337_);
v___x_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2355_, 0, v_b_2342_);
return v___x_2355_;
}
else
{
lean_object* v_snd_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2390_; 
v_snd_2356_ = lean_ctor_get(v_b_2342_, 1);
v_isSharedCheck_2390_ = !lean_is_exclusive(v_b_2342_);
if (v_isSharedCheck_2390_ == 0)
{
lean_object* v_unused_2391_; 
v_unused_2391_ = lean_ctor_get(v_b_2342_, 0);
lean_dec(v_unused_2391_);
v___x_2358_ = v_b_2342_;
v_isShared_2359_ = v_isSharedCheck_2390_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_snd_2356_);
lean_dec(v_b_2342_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2390_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2360_; lean_object* v_a_2361_; lean_object* v___x_2362_; 
v___x_2360_ = lean_box(0);
v_a_2361_ = lean_array_uget_borrowed(v_as_2339_, v_i_2341_);
lean_inc(v_snd_2356_);
lean_inc(v_x_2338_);
lean_inc_ref(v_c_2337_);
v___x_2362_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2336_, v_c_2337_, v_x_2338_, v_a_2361_, v_snd_2356_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2381_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2365_ = v___x_2362_;
v_isShared_2366_ = v_isSharedCheck_2381_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2362_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2381_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
if (lean_obj_tag(v_a_2363_) == 0)
{
lean_object* v___x_2367_; lean_object* v___x_2369_; 
lean_dec(v_x_2338_);
lean_dec_ref(v_c_2337_);
v___x_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2367_, 0, v_a_2363_);
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 0, v___x_2367_);
v___x_2369_ = v___x_2358_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2367_);
lean_ctor_set(v_reuseFailAlloc_2373_, 1, v_snd_2356_);
v___x_2369_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2371_; 
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 0, v___x_2369_);
v___x_2371_ = v___x_2365_;
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
lean_object* v_a_2374_; lean_object* v___x_2376_; 
lean_del_object(v___x_2365_);
lean_dec(v_snd_2356_);
v_a_2374_ = lean_ctor_get(v_a_2363_, 0);
lean_inc(v_a_2374_);
lean_dec_ref_known(v_a_2363_, 1);
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 1, v_a_2374_);
lean_ctor_set(v___x_2358_, 0, v___x_2360_);
v___x_2376_ = v___x_2358_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2360_);
lean_ctor_set(v_reuseFailAlloc_2380_, 1, v_a_2374_);
v___x_2376_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
size_t v___x_2377_; size_t v___x_2378_; 
v___x_2377_ = ((size_t)1ULL);
v___x_2378_ = lean_usize_add(v_i_2341_, v___x_2377_);
v_i_2341_ = v___x_2378_;
v_b_2342_ = v___x_2376_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
lean_del_object(v___x_2358_);
lean_dec(v_snd_2356_);
lean_dec(v_x_2338_);
lean_dec_ref(v_c_2337_);
v_a_2382_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2362_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2362_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2382_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8___boxed(lean_object** _args){
lean_object* v_init_2392_ = _args[0];
lean_object* v_c_2393_ = _args[1];
lean_object* v_x_2394_ = _args[2];
lean_object* v_as_2395_ = _args[3];
lean_object* v_sz_2396_ = _args[4];
lean_object* v_i_2397_ = _args[5];
lean_object* v_b_2398_ = _args[6];
lean_object* v___y_2399_ = _args[7];
lean_object* v___y_2400_ = _args[8];
lean_object* v___y_2401_ = _args[9];
lean_object* v___y_2402_ = _args[10];
lean_object* v___y_2403_ = _args[11];
lean_object* v___y_2404_ = _args[12];
lean_object* v___y_2405_ = _args[13];
lean_object* v___y_2406_ = _args[14];
lean_object* v___y_2407_ = _args[15];
lean_object* v___y_2408_ = _args[16];
lean_object* v___y_2409_ = _args[17];
_start:
{
size_t v_sz_boxed_2410_; size_t v_i_boxed_2411_; lean_object* v_res_2412_; 
v_sz_boxed_2410_ = lean_unbox_usize(v_sz_2396_);
lean_dec(v_sz_2396_);
v_i_boxed_2411_ = lean_unbox_usize(v_i_2397_);
lean_dec(v_i_2397_);
v_res_2412_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_init_2392_, v_c_2393_, v_x_2394_, v_as_2395_, v_sz_boxed_2410_, v_i_boxed_2411_, v_b_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v_as_2395_);
lean_dec_ref(v_init_2392_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6___boxed(lean_object* v_init_2413_, lean_object* v_c_2414_, lean_object* v_x_2415_, lean_object* v_n_2416_, lean_object* v_b_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2413_, v_c_2414_, v_x_2415_, v_n_2416_, v_b_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec_ref(v_n_2416_);
lean_dec_ref(v_init_2413_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(lean_object* v_c_2430_, lean_object* v_x_2431_, lean_object* v_t_2432_, lean_object* v_init_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v_root_2445_; lean_object* v_tail_2446_; lean_object* v___x_2447_; 
v_root_2445_ = lean_ctor_get(v_t_2432_, 0);
v_tail_2446_ = lean_ctor_get(v_t_2432_, 1);
lean_inc(v_x_2431_);
lean_inc_ref(v_c_2430_);
lean_inc_ref(v_init_2433_);
v___x_2447_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2433_, v_c_2430_, v_x_2431_, v_root_2445_, v_init_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
lean_dec_ref(v_init_2433_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2484_; 
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2450_ = v___x_2447_;
v_isShared_2451_ = v_isSharedCheck_2484_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2447_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2484_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
if (lean_obj_tag(v_a_2448_) == 0)
{
lean_object* v_a_2452_; lean_object* v___x_2454_; 
lean_dec(v_x_2431_);
lean_dec_ref(v_c_2430_);
v_a_2452_ = lean_ctor_get(v_a_2448_, 0);
lean_inc(v_a_2452_);
lean_dec_ref_known(v_a_2448_, 1);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 0, v_a_2452_);
v___x_2454_ = v___x_2450_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2452_);
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
lean_object* v_a_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; size_t v_sz_2459_; size_t v___x_2460_; lean_object* v___x_2461_; 
lean_del_object(v___x_2450_);
v_a_2456_ = lean_ctor_get(v_a_2448_, 0);
lean_inc(v_a_2456_);
lean_dec_ref_known(v_a_2448_, 1);
v___x_2457_ = lean_box(0);
v___x_2458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
lean_ctor_set(v___x_2458_, 1, v_a_2456_);
v_sz_2459_ = lean_array_size(v_tail_2446_);
v___x_2460_ = ((size_t)0ULL);
v___x_2461_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_2430_, v_x_2431_, v_tail_2446_, v_sz_2459_, v___x_2460_, v___x_2458_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2475_; 
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2464_ = v___x_2461_;
v_isShared_2465_ = v_isSharedCheck_2475_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2461_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2475_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v_fst_2466_; 
v_fst_2466_ = lean_ctor_get(v_a_2462_, 0);
if (lean_obj_tag(v_fst_2466_) == 0)
{
lean_object* v_snd_2467_; lean_object* v___x_2469_; 
v_snd_2467_ = lean_ctor_get(v_a_2462_, 1);
lean_inc(v_snd_2467_);
lean_dec(v_a_2462_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v_snd_2467_);
v___x_2469_ = v___x_2464_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_snd_2467_);
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
lean_object* v_val_2471_; lean_object* v___x_2473_; 
lean_inc_ref(v_fst_2466_);
lean_dec(v_a_2462_);
v_val_2471_ = lean_ctor_get(v_fst_2466_, 0);
lean_inc(v_val_2471_);
lean_dec_ref_known(v_fst_2466_, 1);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v_val_2471_);
v___x_2473_ = v___x_2464_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_val_2471_);
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
else
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
v_a_2476_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2461_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2461_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
}
}
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_dec(v_x_2431_);
lean_dec_ref(v_c_2430_);
v_a_2485_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2447_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2447_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2___boxed(lean_object* v_c_2493_, lean_object* v_x_2494_, lean_object* v_t_2495_, lean_object* v_init_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_2493_, v_x_2494_, v_t_2495_, v_init_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec_ref(v_t_2495_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(lean_object* v_x_2509_, lean_object* v_c_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
v___x_2523_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2511_, v_a_2519_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; lean_object* v___y_2526_; lean_object* v_diseqs_2551_; lean_object* v_size_2552_; uint8_t v___x_2553_; 
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2524_);
lean_dec_ref_known(v___x_2523_, 1);
v_diseqs_2551_ = lean_ctor_get(v_a_2524_, 8);
lean_inc_ref(v_diseqs_2551_);
lean_dec(v_a_2524_);
v_size_2552_ = lean_ctor_get(v_diseqs_2551_, 2);
v___x_2553_ = lean_nat_dec_lt(v_x_2509_, v_size_2552_);
if (v___x_2553_ == 0)
{
lean_object* v___x_2554_; 
lean_dec_ref(v_diseqs_2551_);
v___x_2554_ = l_outOfBounds___redArg(v___x_2522_);
v___y_2526_ = v___x_2554_;
goto v___jp_2525_;
}
else
{
lean_object* v___x_2555_; 
v___x_2555_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2522_, v_diseqs_2551_, v_x_2509_);
lean_dec_ref(v_diseqs_2551_);
v___y_2526_ = v___x_2555_;
goto v___jp_2525_;
}
v___jp_2525_:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2527_ = lean_box(0);
v___x_2528_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__0));
v___x_2529_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_2510_, v_x_2509_, v___y_2526_, v___x_2528_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
lean_dec_ref(v___y_2526_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2542_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2532_ = v___x_2529_;
v_isShared_2533_ = v_isSharedCheck_2542_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2529_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2542_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v_fst_2534_; 
v_fst_2534_ = lean_ctor_get(v_a_2530_, 0);
lean_inc(v_fst_2534_);
lean_dec(v_a_2530_);
if (lean_obj_tag(v_fst_2534_) == 0)
{
lean_object* v___x_2536_; 
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v___x_2527_);
v___x_2536_ = v___x_2532_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v___x_2527_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
else
{
lean_object* v_val_2538_; lean_object* v___x_2540_; 
v_val_2538_ = lean_ctor_get(v_fst_2534_, 0);
lean_inc(v_val_2538_);
lean_dec_ref_known(v_fst_2534_, 1);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v_val_2538_);
v___x_2540_ = v___x_2532_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_val_2538_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
v_a_2543_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2529_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2529_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
lean_dec_ref(v_c_2510_);
lean_dec(v_x_2509_);
v_a_2556_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2523_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2523_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___boxed(lean_object* v_x_2564_, lean_object* v_c_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_x_2564_, v_c_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_);
lean_dec(v_a_2575_);
lean_dec_ref(v_a_2574_);
lean_dec(v_a_2573_);
lean_dec_ref(v_a_2572_);
lean_dec(v_a_2571_);
lean_dec_ref(v_a_2570_);
lean_dec(v_a_2569_);
lean_dec_ref(v_a_2568_);
lean_dec(v_a_2567_);
lean_dec(v_a_2566_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(lean_object* v_c_2578_, lean_object* v_x_2579_, lean_object* v_as_2580_, size_t v_sz_2581_, size_t v_i_2582_, lean_object* v_b_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v___x_2595_; 
v___x_2595_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2578_, v_x_2579_, v_as_2580_, v_sz_2581_, v_i_2582_, v_b_2583_, v___y_2584_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___boxed(lean_object** _args){
lean_object* v_c_2596_ = _args[0];
lean_object* v_x_2597_ = _args[1];
lean_object* v_as_2598_ = _args[2];
lean_object* v_sz_2599_ = _args[3];
lean_object* v_i_2600_ = _args[4];
lean_object* v_b_2601_ = _args[5];
lean_object* v___y_2602_ = _args[6];
lean_object* v___y_2603_ = _args[7];
lean_object* v___y_2604_ = _args[8];
lean_object* v___y_2605_ = _args[9];
lean_object* v___y_2606_ = _args[10];
lean_object* v___y_2607_ = _args[11];
lean_object* v___y_2608_ = _args[12];
lean_object* v___y_2609_ = _args[13];
lean_object* v___y_2610_ = _args[14];
lean_object* v___y_2611_ = _args[15];
lean_object* v___y_2612_ = _args[16];
_start:
{
size_t v_sz_boxed_2613_; size_t v_i_boxed_2614_; lean_object* v_res_2615_; 
v_sz_boxed_2613_ = lean_unbox_usize(v_sz_2599_);
lean_dec(v_sz_2599_);
v_i_boxed_2614_ = lean_unbox_usize(v_i_2600_);
lean_dec(v_i_2600_);
v_res_2615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(v_c_2596_, v_x_2597_, v_as_2598_, v_sz_boxed_2613_, v_i_boxed_2614_, v_b_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v_as_2598_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(lean_object* v_c_2616_, lean_object* v_x_2617_, lean_object* v_as_2618_, size_t v_sz_2619_, size_t v_i_2620_, lean_object* v_b_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2616_, v_x_2617_, v_as_2618_, v_sz_2619_, v_i_2620_, v_b_2621_, v___y_2622_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___boxed(lean_object** _args){
lean_object* v_c_2634_ = _args[0];
lean_object* v_x_2635_ = _args[1];
lean_object* v_as_2636_ = _args[2];
lean_object* v_sz_2637_ = _args[3];
lean_object* v_i_2638_ = _args[4];
lean_object* v_b_2639_ = _args[5];
lean_object* v___y_2640_ = _args[6];
lean_object* v___y_2641_ = _args[7];
lean_object* v___y_2642_ = _args[8];
lean_object* v___y_2643_ = _args[9];
lean_object* v___y_2644_ = _args[10];
lean_object* v___y_2645_ = _args[11];
lean_object* v___y_2646_ = _args[12];
lean_object* v___y_2647_ = _args[13];
lean_object* v___y_2648_ = _args[14];
lean_object* v___y_2649_ = _args[15];
lean_object* v___y_2650_ = _args[16];
_start:
{
size_t v_sz_boxed_2651_; size_t v_i_boxed_2652_; lean_object* v_res_2653_; 
v_sz_boxed_2651_ = lean_unbox_usize(v_sz_2637_);
lean_dec(v_sz_2637_);
v_i_boxed_2652_ = lean_unbox_usize(v_i_2638_);
lean_dec(v_i_2638_);
v_res_2653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(v_c_2634_, v_x_2635_, v_as_2636_, v_sz_boxed_2651_, v_i_boxed_2652_, v_b_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec_ref(v_as_2636_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(lean_object* v_v_2654_, lean_object* v_a_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v_snd_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2698_; 
v_snd_2667_ = lean_ctor_get(v_a_2655_, 1);
v_isSharedCheck_2698_ = !lean_is_exclusive(v_a_2655_);
if (v_isSharedCheck_2698_ == 0)
{
lean_object* v_unused_2699_; 
v_unused_2699_ = lean_ctor_get(v_a_2655_, 0);
lean_dec(v_unused_2699_);
v___x_2669_ = v_a_2655_;
v_isShared_2670_ = v_isSharedCheck_2698_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_snd_2667_);
lean_dec(v_a_2655_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2698_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2671_ = lean_box(0);
lean_inc(v_snd_2667_);
lean_inc(v_v_2654_);
v___x_2672_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_v_2654_, v_snd_2667_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2689_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2675_ = v___x_2672_;
v_isShared_2676_ = v_isSharedCheck_2689_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2672_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2689_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
if (lean_obj_tag(v_a_2673_) == 1)
{
lean_object* v_val_2677_; lean_object* v___x_2679_; 
lean_del_object(v___x_2675_);
lean_dec(v_snd_2667_);
v_val_2677_ = lean_ctor_get(v_a_2673_, 0);
lean_inc(v_val_2677_);
lean_dec_ref_known(v_a_2673_, 1);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 1, v_val_2677_);
lean_ctor_set(v___x_2669_, 0, v___x_2671_);
v___x_2679_ = v___x_2669_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2671_);
lean_ctor_set(v_reuseFailAlloc_2681_, 1, v_val_2677_);
v___x_2679_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
v_a_2655_ = v___x_2679_;
goto _start;
}
}
else
{
lean_object* v___x_2682_; lean_object* v___x_2684_; 
lean_dec(v_a_2673_);
lean_dec(v_v_2654_);
lean_inc(v_snd_2667_);
v___x_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2682_, 0, v_snd_2667_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v___x_2682_);
v___x_2684_ = v___x_2669_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2682_);
lean_ctor_set(v_reuseFailAlloc_2688_, 1, v_snd_2667_);
v___x_2684_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
lean_object* v___x_2686_; 
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 0, v___x_2684_);
v___x_2686_ = v___x_2675_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2684_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
}
}
else
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
lean_del_object(v___x_2669_);
lean_dec(v_snd_2667_);
lean_dec(v_v_2654_);
v_a_2690_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2672_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2672_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg___boxed(lean_object* v_v_2700_, lean_object* v_a_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(v_v_2700_, v_a_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec(v___y_2702_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(lean_object* v_c_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_){
_start:
{
lean_object* v_p_2726_; 
v_p_2726_ = lean_ctor_get(v_c_2714_, 0);
if (lean_obj_tag(v_p_2726_) == 1)
{
lean_object* v_v_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v_v_2727_ = lean_ctor_get(v_p_2726_, 1);
lean_inc(v_v_2727_);
v___x_2728_ = lean_box(0);
v___x_2729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2728_);
lean_ctor_set(v___x_2729_, 1, v_c_2714_);
v___x_2730_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(v_v_2727_, v___x_2729_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2744_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2733_ = v___x_2730_;
v_isShared_2734_ = v_isSharedCheck_2744_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2730_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2744_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v_fst_2735_; 
v_fst_2735_ = lean_ctor_get(v_a_2731_, 0);
if (lean_obj_tag(v_fst_2735_) == 0)
{
lean_object* v_snd_2736_; lean_object* v___x_2738_; 
v_snd_2736_ = lean_ctor_get(v_a_2731_, 1);
lean_inc(v_snd_2736_);
lean_dec(v_a_2731_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 0, v_snd_2736_);
v___x_2738_ = v___x_2733_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_snd_2736_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
else
{
lean_object* v_val_2740_; lean_object* v___x_2742_; 
lean_inc_ref(v_fst_2735_);
lean_dec(v_a_2731_);
v_val_2740_ = lean_ctor_get(v_fst_2735_, 0);
lean_inc(v_val_2740_);
lean_dec_ref_known(v_fst_2735_, 1);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 0, v_val_2740_);
v___x_2742_ = v___x_2733_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_val_2740_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
else
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
v_a_2745_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2730_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2730_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2745_);
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
else
{
lean_object* v___x_2753_; 
v___x_2753_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_2714_, v_a_2715_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_);
return v___x_2753_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq___boxed(lean_object* v_c_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_c_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_);
lean_dec(v_a_2764_);
lean_dec_ref(v_a_2763_);
lean_dec(v_a_2762_);
lean_dec_ref(v_a_2761_);
lean_dec(v_a_2760_);
lean_dec_ref(v_a_2759_);
lean_dec(v_a_2758_);
lean_dec_ref(v_a_2757_);
lean_dec(v_a_2756_);
lean_dec(v_a_2755_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(lean_object* v_v_2767_, lean_object* v_inst_2768_, lean_object* v_a_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v___x_2781_; 
v___x_2781_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(v_v_2767_, v_a_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___boxed(lean_object* v_v_2782_, lean_object* v_inst_2783_, lean_object* v_a_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(v_v_2782_, v_inst_2783_, v_a_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec(v___y_2785_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(lean_object* v_a_2797_, lean_object* v_x_2798_, size_t v_x_2799_, size_t v_x_2800_){
_start:
{
if (lean_obj_tag(v_x_2798_) == 0)
{
lean_object* v_cs_2801_; size_t v_j_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; uint8_t v___x_2805_; 
v_cs_2801_ = lean_ctor_get(v_x_2798_, 0);
v_j_2802_ = lean_usize_shift_right(v_x_2799_, v_x_2800_);
v___x_2803_ = lean_usize_to_nat(v_j_2802_);
v___x_2804_ = lean_array_get_size(v_cs_2801_);
v___x_2805_ = lean_nat_dec_lt(v___x_2803_, v___x_2804_);
if (v___x_2805_ == 0)
{
lean_dec(v___x_2803_);
lean_dec_ref(v_a_2797_);
return v_x_2798_;
}
else
{
lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2823_; 
lean_inc_ref(v_cs_2801_);
v_isSharedCheck_2823_ = !lean_is_exclusive(v_x_2798_);
if (v_isSharedCheck_2823_ == 0)
{
lean_object* v_unused_2824_; 
v_unused_2824_ = lean_ctor_get(v_x_2798_, 0);
lean_dec(v_unused_2824_);
v___x_2807_ = v_x_2798_;
v_isShared_2808_ = v_isSharedCheck_2823_;
goto v_resetjp_2806_;
}
else
{
lean_dec(v_x_2798_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2823_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
size_t v___x_2809_; size_t v___x_2810_; size_t v___x_2811_; size_t v_i_2812_; size_t v___x_2813_; size_t v_shift_2814_; lean_object* v_v_2815_; lean_object* v___x_2816_; lean_object* v_xs_x27_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2821_; 
v___x_2809_ = ((size_t)1ULL);
v___x_2810_ = lean_usize_shift_left(v___x_2809_, v_x_2800_);
v___x_2811_ = lean_usize_sub(v___x_2810_, v___x_2809_);
v_i_2812_ = lean_usize_land(v_x_2799_, v___x_2811_);
v___x_2813_ = ((size_t)5ULL);
v_shift_2814_ = lean_usize_sub(v_x_2800_, v___x_2813_);
v_v_2815_ = lean_array_fget(v_cs_2801_, v___x_2803_);
v___x_2816_ = lean_box(0);
v_xs_x27_2817_ = lean_array_fset(v_cs_2801_, v___x_2803_, v___x_2816_);
v___x_2818_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2797_, v_v_2815_, v_i_2812_, v_shift_2814_);
v___x_2819_ = lean_array_fset(v_xs_x27_2817_, v___x_2803_, v___x_2818_);
lean_dec(v___x_2803_);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 0, v___x_2819_);
v___x_2821_ = v___x_2807_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_vs_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; 
v_vs_2825_ = lean_ctor_get(v_x_2798_, 0);
v___x_2826_ = lean_usize_to_nat(v_x_2799_);
v___x_2827_ = lean_array_get_size(v_vs_2825_);
v___x_2828_ = lean_nat_dec_lt(v___x_2826_, v___x_2827_);
if (v___x_2828_ == 0)
{
lean_dec(v___x_2826_);
lean_dec_ref(v_a_2797_);
return v_x_2798_;
}
else
{
lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2840_; 
lean_inc_ref(v_vs_2825_);
v_isSharedCheck_2840_ = !lean_is_exclusive(v_x_2798_);
if (v_isSharedCheck_2840_ == 0)
{
lean_object* v_unused_2841_; 
v_unused_2841_ = lean_ctor_get(v_x_2798_, 0);
lean_dec(v_unused_2841_);
v___x_2830_ = v_x_2798_;
v_isShared_2831_ = v_isSharedCheck_2840_;
goto v_resetjp_2829_;
}
else
{
lean_dec(v_x_2798_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2840_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v_v_2832_; lean_object* v___x_2833_; lean_object* v_xs_x27_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2838_; 
v_v_2832_ = lean_array_fget(v_vs_2825_, v___x_2826_);
v___x_2833_ = lean_box(0);
v_xs_x27_2834_ = lean_array_fset(v_vs_2825_, v___x_2826_, v___x_2833_);
v___x_2835_ = l_Lean_PersistentArray_push___redArg(v_v_2832_, v_a_2797_);
v___x_2836_ = lean_array_fset(v_xs_x27_2834_, v___x_2826_, v___x_2835_);
lean_dec(v___x_2826_);
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 0, v___x_2836_);
v___x_2838_ = v___x_2830_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2836_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___boxed(lean_object* v_a_2842_, lean_object* v_x_2843_, lean_object* v_x_2844_, lean_object* v_x_2845_){
_start:
{
size_t v_x_68151__boxed_2846_; size_t v_x_68152__boxed_2847_; lean_object* v_res_2848_; 
v_x_68151__boxed_2846_ = lean_unbox_usize(v_x_2844_);
lean_dec(v_x_2844_);
v_x_68152__boxed_2847_ = lean_unbox_usize(v_x_2845_);
lean_dec(v_x_2845_);
v_res_2848_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2842_, v_x_2843_, v_x_68151__boxed_2846_, v_x_68152__boxed_2847_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(lean_object* v_a_2849_, lean_object* v_t_2850_, lean_object* v_i_2851_){
_start:
{
lean_object* v_root_2852_; lean_object* v_tail_2853_; lean_object* v_size_2854_; size_t v_shift_2855_; lean_object* v_tailOff_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2880_; 
v_root_2852_ = lean_ctor_get(v_t_2850_, 0);
v_tail_2853_ = lean_ctor_get(v_t_2850_, 1);
v_size_2854_ = lean_ctor_get(v_t_2850_, 2);
v_shift_2855_ = lean_ctor_get_usize(v_t_2850_, 4);
v_tailOff_2856_ = lean_ctor_get(v_t_2850_, 3);
v_isSharedCheck_2880_ = !lean_is_exclusive(v_t_2850_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2858_ = v_t_2850_;
v_isShared_2859_ = v_isSharedCheck_2880_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_tailOff_2856_);
lean_inc(v_size_2854_);
lean_inc(v_tail_2853_);
lean_inc(v_root_2852_);
lean_dec(v_t_2850_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2880_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
uint8_t v___x_2860_; 
v___x_2860_ = lean_nat_dec_le(v_tailOff_2856_, v_i_2851_);
if (v___x_2860_ == 0)
{
size_t v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2864_; 
v___x_2861_ = lean_usize_of_nat(v_i_2851_);
v___x_2862_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2849_, v_root_2852_, v___x_2861_, v_shift_2855_);
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 0, v___x_2862_);
v___x_2864_ = v___x_2858_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v___x_2862_);
lean_ctor_set(v_reuseFailAlloc_2865_, 1, v_tail_2853_);
lean_ctor_set(v_reuseFailAlloc_2865_, 2, v_size_2854_);
lean_ctor_set(v_reuseFailAlloc_2865_, 3, v_tailOff_2856_);
lean_ctor_set_usize(v_reuseFailAlloc_2865_, 4, v_shift_2855_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
else
{
lean_object* v___x_2866_; lean_object* v___x_2867_; uint8_t v___x_2868_; 
v___x_2866_ = lean_nat_sub(v_i_2851_, v_tailOff_2856_);
v___x_2867_ = lean_array_get_size(v_tail_2853_);
v___x_2868_ = lean_nat_dec_lt(v___x_2866_, v___x_2867_);
if (v___x_2868_ == 0)
{
lean_object* v___x_2870_; 
lean_dec(v___x_2866_);
lean_dec_ref(v_a_2849_);
if (v_isShared_2859_ == 0)
{
v___x_2870_ = v___x_2858_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_root_2852_);
lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_tail_2853_);
lean_ctor_set(v_reuseFailAlloc_2871_, 2, v_size_2854_);
lean_ctor_set(v_reuseFailAlloc_2871_, 3, v_tailOff_2856_);
lean_ctor_set_usize(v_reuseFailAlloc_2871_, 4, v_shift_2855_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
else
{
lean_object* v_v_2872_; lean_object* v___x_2873_; lean_object* v_xs_x27_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2878_; 
v_v_2872_ = lean_array_fget(v_tail_2853_, v___x_2866_);
v___x_2873_ = lean_box(0);
v_xs_x27_2874_ = lean_array_fset(v_tail_2853_, v___x_2866_, v___x_2873_);
v___x_2875_ = l_Lean_PersistentArray_push___redArg(v_v_2872_, v_a_2849_);
v___x_2876_ = lean_array_fset(v_xs_x27_2874_, v___x_2866_, v___x_2875_);
lean_dec(v___x_2866_);
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 1, v___x_2876_);
v___x_2878_ = v___x_2858_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_root_2852_);
lean_ctor_set(v_reuseFailAlloc_2879_, 1, v___x_2876_);
lean_ctor_set(v_reuseFailAlloc_2879_, 2, v_size_2854_);
lean_ctor_set(v_reuseFailAlloc_2879_, 3, v_tailOff_2856_);
lean_ctor_set_usize(v_reuseFailAlloc_2879_, 4, v_shift_2855_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0___boxed(lean_object* v_a_2881_, lean_object* v_t_2882_, lean_object* v_i_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2881_, v_t_2882_, v_i_2883_);
lean_dec(v_i_2883_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(lean_object* v_a_2885_, lean_object* v_v_2886_, lean_object* v_s_2887_){
_start:
{
lean_object* v_vars_2888_; lean_object* v_varMap_2889_; lean_object* v_varsHistory_2890_; lean_object* v_natToIntMap_2891_; lean_object* v_natDef_2892_; lean_object* v_dvds_2893_; lean_object* v_lowers_2894_; lean_object* v_uppers_2895_; lean_object* v_diseqs_2896_; lean_object* v_elimEqs_2897_; lean_object* v_active_2898_; lean_object* v_elimStack_2899_; lean_object* v_occurs_2900_; lean_object* v_assignment_2901_; lean_object* v_nextCnstrId_2902_; uint8_t v_caseSplits_2903_; lean_object* v_steps_2904_; lean_object* v_penalties_2905_; lean_object* v_numReorderRequests_2906_; lean_object* v_conflict_x3f_2907_; lean_object* v_diseqSplits_2908_; lean_object* v_divMod_2909_; uint8_t v_usedCommRing_2910_; lean_object* v_nonlinearOccs_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2919_; 
v_vars_2888_ = lean_ctor_get(v_s_2887_, 0);
v_varMap_2889_ = lean_ctor_get(v_s_2887_, 1);
v_varsHistory_2890_ = lean_ctor_get(v_s_2887_, 2);
v_natToIntMap_2891_ = lean_ctor_get(v_s_2887_, 3);
v_natDef_2892_ = lean_ctor_get(v_s_2887_, 4);
v_dvds_2893_ = lean_ctor_get(v_s_2887_, 5);
v_lowers_2894_ = lean_ctor_get(v_s_2887_, 6);
v_uppers_2895_ = lean_ctor_get(v_s_2887_, 7);
v_diseqs_2896_ = lean_ctor_get(v_s_2887_, 8);
v_elimEqs_2897_ = lean_ctor_get(v_s_2887_, 9);
v_active_2898_ = lean_ctor_get(v_s_2887_, 10);
v_elimStack_2899_ = lean_ctor_get(v_s_2887_, 11);
v_occurs_2900_ = lean_ctor_get(v_s_2887_, 12);
v_assignment_2901_ = lean_ctor_get(v_s_2887_, 13);
v_nextCnstrId_2902_ = lean_ctor_get(v_s_2887_, 14);
v_caseSplits_2903_ = lean_ctor_get_uint8(v_s_2887_, sizeof(void*)*22);
v_steps_2904_ = lean_ctor_get(v_s_2887_, 15);
v_penalties_2905_ = lean_ctor_get(v_s_2887_, 16);
v_numReorderRequests_2906_ = lean_ctor_get(v_s_2887_, 17);
v_conflict_x3f_2907_ = lean_ctor_get(v_s_2887_, 18);
v_diseqSplits_2908_ = lean_ctor_get(v_s_2887_, 19);
v_divMod_2909_ = lean_ctor_get(v_s_2887_, 20);
v_usedCommRing_2910_ = lean_ctor_get_uint8(v_s_2887_, sizeof(void*)*22 + 1);
v_nonlinearOccs_2911_ = lean_ctor_get(v_s_2887_, 21);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_s_2887_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2913_ = v_s_2887_;
v_isShared_2914_ = v_isSharedCheck_2919_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_nonlinearOccs_2911_);
lean_inc(v_divMod_2909_);
lean_inc(v_diseqSplits_2908_);
lean_inc(v_conflict_x3f_2907_);
lean_inc(v_numReorderRequests_2906_);
lean_inc(v_penalties_2905_);
lean_inc(v_steps_2904_);
lean_inc(v_nextCnstrId_2902_);
lean_inc(v_assignment_2901_);
lean_inc(v_occurs_2900_);
lean_inc(v_elimStack_2899_);
lean_inc(v_active_2898_);
lean_inc(v_elimEqs_2897_);
lean_inc(v_diseqs_2896_);
lean_inc(v_uppers_2895_);
lean_inc(v_lowers_2894_);
lean_inc(v_dvds_2893_);
lean_inc(v_natDef_2892_);
lean_inc(v_natToIntMap_2891_);
lean_inc(v_varsHistory_2890_);
lean_inc(v_varMap_2889_);
lean_inc(v_vars_2888_);
lean_dec(v_s_2887_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2919_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2915_; lean_object* v___x_2917_; 
v___x_2915_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2885_, v_lowers_2894_, v_v_2886_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 6, v___x_2915_);
v___x_2917_ = v___x_2913_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_vars_2888_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_varMap_2889_);
lean_ctor_set(v_reuseFailAlloc_2918_, 2, v_varsHistory_2890_);
lean_ctor_set(v_reuseFailAlloc_2918_, 3, v_natToIntMap_2891_);
lean_ctor_set(v_reuseFailAlloc_2918_, 4, v_natDef_2892_);
lean_ctor_set(v_reuseFailAlloc_2918_, 5, v_dvds_2893_);
lean_ctor_set(v_reuseFailAlloc_2918_, 6, v___x_2915_);
lean_ctor_set(v_reuseFailAlloc_2918_, 7, v_uppers_2895_);
lean_ctor_set(v_reuseFailAlloc_2918_, 8, v_diseqs_2896_);
lean_ctor_set(v_reuseFailAlloc_2918_, 9, v_elimEqs_2897_);
lean_ctor_set(v_reuseFailAlloc_2918_, 10, v_active_2898_);
lean_ctor_set(v_reuseFailAlloc_2918_, 11, v_elimStack_2899_);
lean_ctor_set(v_reuseFailAlloc_2918_, 12, v_occurs_2900_);
lean_ctor_set(v_reuseFailAlloc_2918_, 13, v_assignment_2901_);
lean_ctor_set(v_reuseFailAlloc_2918_, 14, v_nextCnstrId_2902_);
lean_ctor_set(v_reuseFailAlloc_2918_, 15, v_steps_2904_);
lean_ctor_set(v_reuseFailAlloc_2918_, 16, v_penalties_2905_);
lean_ctor_set(v_reuseFailAlloc_2918_, 17, v_numReorderRequests_2906_);
lean_ctor_set(v_reuseFailAlloc_2918_, 18, v_conflict_x3f_2907_);
lean_ctor_set(v_reuseFailAlloc_2918_, 19, v_diseqSplits_2908_);
lean_ctor_set(v_reuseFailAlloc_2918_, 20, v_divMod_2909_);
lean_ctor_set(v_reuseFailAlloc_2918_, 21, v_nonlinearOccs_2911_);
lean_ctor_set_uint8(v_reuseFailAlloc_2918_, sizeof(void*)*22, v_caseSplits_2903_);
lean_ctor_set_uint8(v_reuseFailAlloc_2918_, sizeof(void*)*22 + 1, v_usedCommRing_2910_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed(lean_object* v_a_2920_, lean_object* v_v_2921_, lean_object* v_s_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(v_a_2920_, v_v_2921_, v_s_2922_);
lean_dec(v_v_2921_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(lean_object* v_a_2924_, lean_object* v_v_2925_, lean_object* v_s_2926_){
_start:
{
lean_object* v_vars_2927_; lean_object* v_varMap_2928_; lean_object* v_varsHistory_2929_; lean_object* v_natToIntMap_2930_; lean_object* v_natDef_2931_; lean_object* v_dvds_2932_; lean_object* v_lowers_2933_; lean_object* v_uppers_2934_; lean_object* v_diseqs_2935_; lean_object* v_elimEqs_2936_; lean_object* v_active_2937_; lean_object* v_elimStack_2938_; lean_object* v_occurs_2939_; lean_object* v_assignment_2940_; lean_object* v_nextCnstrId_2941_; uint8_t v_caseSplits_2942_; lean_object* v_steps_2943_; lean_object* v_penalties_2944_; lean_object* v_numReorderRequests_2945_; lean_object* v_conflict_x3f_2946_; lean_object* v_diseqSplits_2947_; lean_object* v_divMod_2948_; uint8_t v_usedCommRing_2949_; lean_object* v_nonlinearOccs_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2958_; 
v_vars_2927_ = lean_ctor_get(v_s_2926_, 0);
v_varMap_2928_ = lean_ctor_get(v_s_2926_, 1);
v_varsHistory_2929_ = lean_ctor_get(v_s_2926_, 2);
v_natToIntMap_2930_ = lean_ctor_get(v_s_2926_, 3);
v_natDef_2931_ = lean_ctor_get(v_s_2926_, 4);
v_dvds_2932_ = lean_ctor_get(v_s_2926_, 5);
v_lowers_2933_ = lean_ctor_get(v_s_2926_, 6);
v_uppers_2934_ = lean_ctor_get(v_s_2926_, 7);
v_diseqs_2935_ = lean_ctor_get(v_s_2926_, 8);
v_elimEqs_2936_ = lean_ctor_get(v_s_2926_, 9);
v_active_2937_ = lean_ctor_get(v_s_2926_, 10);
v_elimStack_2938_ = lean_ctor_get(v_s_2926_, 11);
v_occurs_2939_ = lean_ctor_get(v_s_2926_, 12);
v_assignment_2940_ = lean_ctor_get(v_s_2926_, 13);
v_nextCnstrId_2941_ = lean_ctor_get(v_s_2926_, 14);
v_caseSplits_2942_ = lean_ctor_get_uint8(v_s_2926_, sizeof(void*)*22);
v_steps_2943_ = lean_ctor_get(v_s_2926_, 15);
v_penalties_2944_ = lean_ctor_get(v_s_2926_, 16);
v_numReorderRequests_2945_ = lean_ctor_get(v_s_2926_, 17);
v_conflict_x3f_2946_ = lean_ctor_get(v_s_2926_, 18);
v_diseqSplits_2947_ = lean_ctor_get(v_s_2926_, 19);
v_divMod_2948_ = lean_ctor_get(v_s_2926_, 20);
v_usedCommRing_2949_ = lean_ctor_get_uint8(v_s_2926_, sizeof(void*)*22 + 1);
v_nonlinearOccs_2950_ = lean_ctor_get(v_s_2926_, 21);
v_isSharedCheck_2958_ = !lean_is_exclusive(v_s_2926_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2952_ = v_s_2926_;
v_isShared_2953_ = v_isSharedCheck_2958_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_nonlinearOccs_2950_);
lean_inc(v_divMod_2948_);
lean_inc(v_diseqSplits_2947_);
lean_inc(v_conflict_x3f_2946_);
lean_inc(v_numReorderRequests_2945_);
lean_inc(v_penalties_2944_);
lean_inc(v_steps_2943_);
lean_inc(v_nextCnstrId_2941_);
lean_inc(v_assignment_2940_);
lean_inc(v_occurs_2939_);
lean_inc(v_elimStack_2938_);
lean_inc(v_active_2937_);
lean_inc(v_elimEqs_2936_);
lean_inc(v_diseqs_2935_);
lean_inc(v_uppers_2934_);
lean_inc(v_lowers_2933_);
lean_inc(v_dvds_2932_);
lean_inc(v_natDef_2931_);
lean_inc(v_natToIntMap_2930_);
lean_inc(v_varsHistory_2929_);
lean_inc(v_varMap_2928_);
lean_inc(v_vars_2927_);
lean_dec(v_s_2926_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2958_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2954_; lean_object* v___x_2956_; 
v___x_2954_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2924_, v_uppers_2934_, v_v_2925_);
if (v_isShared_2953_ == 0)
{
lean_ctor_set(v___x_2952_, 7, v___x_2954_);
v___x_2956_ = v___x_2952_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_vars_2927_);
lean_ctor_set(v_reuseFailAlloc_2957_, 1, v_varMap_2928_);
lean_ctor_set(v_reuseFailAlloc_2957_, 2, v_varsHistory_2929_);
lean_ctor_set(v_reuseFailAlloc_2957_, 3, v_natToIntMap_2930_);
lean_ctor_set(v_reuseFailAlloc_2957_, 4, v_natDef_2931_);
lean_ctor_set(v_reuseFailAlloc_2957_, 5, v_dvds_2932_);
lean_ctor_set(v_reuseFailAlloc_2957_, 6, v_lowers_2933_);
lean_ctor_set(v_reuseFailAlloc_2957_, 7, v___x_2954_);
lean_ctor_set(v_reuseFailAlloc_2957_, 8, v_diseqs_2935_);
lean_ctor_set(v_reuseFailAlloc_2957_, 9, v_elimEqs_2936_);
lean_ctor_set(v_reuseFailAlloc_2957_, 10, v_active_2937_);
lean_ctor_set(v_reuseFailAlloc_2957_, 11, v_elimStack_2938_);
lean_ctor_set(v_reuseFailAlloc_2957_, 12, v_occurs_2939_);
lean_ctor_set(v_reuseFailAlloc_2957_, 13, v_assignment_2940_);
lean_ctor_set(v_reuseFailAlloc_2957_, 14, v_nextCnstrId_2941_);
lean_ctor_set(v_reuseFailAlloc_2957_, 15, v_steps_2943_);
lean_ctor_set(v_reuseFailAlloc_2957_, 16, v_penalties_2944_);
lean_ctor_set(v_reuseFailAlloc_2957_, 17, v_numReorderRequests_2945_);
lean_ctor_set(v_reuseFailAlloc_2957_, 18, v_conflict_x3f_2946_);
lean_ctor_set(v_reuseFailAlloc_2957_, 19, v_diseqSplits_2947_);
lean_ctor_set(v_reuseFailAlloc_2957_, 20, v_divMod_2948_);
lean_ctor_set(v_reuseFailAlloc_2957_, 21, v_nonlinearOccs_2950_);
lean_ctor_set_uint8(v_reuseFailAlloc_2957_, sizeof(void*)*22, v_caseSplits_2942_);
lean_ctor_set_uint8(v_reuseFailAlloc_2957_, sizeof(void*)*22 + 1, v_usedCommRing_2949_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed(lean_object* v_a_2959_, lean_object* v_v_2960_, lean_object* v_s_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(v_a_2959_, v_v_2960_, v_s_2961_);
lean_dec(v_v_2960_);
return v_res_2962_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3(void){
_start:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2970_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2));
v___x_2971_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_2972_ = l_Lean_Name_append(v___x_2971_, v___x_2970_);
return v___x_2972_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6(void){
_start:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2979_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5));
v___x_2980_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_2981_ = l_Lean_Name_append(v___x_2980_, v___x_2979_);
return v___x_2981_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9(void){
_start:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2988_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8));
v___x_2989_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_2990_ = l_Lean_Name_append(v___x_2989_, v___x_2988_);
return v___x_2990_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11(void){
_start:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2995_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10));
v___x_2996_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_2997_ = l_Lean_Name_append(v___x_2996_, v___x_2995_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* lean_grind_cutsat_assert_le(lean_object* v_c_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_){
_start:
{
lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___x_3082_; 
v___x_3082_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_2999_, v_a_3007_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3233_; 
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3085_ = v___x_3082_;
v_isShared_3086_ = v_isSharedCheck_3233_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3082_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3233_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
uint8_t v___x_3087_; 
v___x_3087_ = lean_unbox(v_a_3083_);
lean_dec(v_a_3083_);
if (v___x_3087_ == 0)
{
lean_object* v_toCold_3088_; lean_object* v_options_3089_; lean_object* v_inheritedTraceOptions_3090_; uint8_t v_hasTrace_3091_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; 
lean_del_object(v___x_3085_);
v_toCold_3088_ = lean_ctor_get(v_a_3007_, 0);
v_options_3089_ = lean_ctor_get(v_toCold_3088_, 2);
v_inheritedTraceOptions_3090_ = lean_ctor_get(v_toCold_3088_, 11);
v_hasTrace_3091_ = lean_ctor_get_uint8(v_options_3089_, sizeof(void*)*1);
if (v_hasTrace_3091_ == 0)
{
v___y_3093_ = v_a_2999_;
v___y_3094_ = v_a_3000_;
v___y_3095_ = v_a_3001_;
v___y_3096_ = v_a_3002_;
v___y_3097_ = v_a_3003_;
v___y_3098_ = v_a_3004_;
v___y_3099_ = v_a_3005_;
v___y_3100_ = v_a_3006_;
v___y_3101_ = v_a_3007_;
v___y_3102_ = v_a_3008_;
goto v___jp_3092_;
}
else
{
lean_object* v___x_3215_; lean_object* v___x_3216_; uint8_t v___x_3217_; 
v___x_3215_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10));
v___x_3216_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11);
v___x_3217_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3090_, v_options_3089_, v___x_3216_);
if (v___x_3217_ == 0)
{
v___y_3093_ = v_a_2999_;
v___y_3094_ = v_a_3000_;
v___y_3095_ = v_a_3001_;
v___y_3096_ = v_a_3002_;
v___y_3097_ = v_a_3003_;
v___y_3098_ = v_a_3004_;
v___y_3099_ = v_a_3005_;
v___y_3100_ = v_a_3006_;
v___y_3101_ = v_a_3007_;
v___y_3102_ = v_a_3008_;
goto v___jp_3092_;
}
else
{
lean_object* v___x_3218_; 
lean_inc_ref(v_c_2998_);
v___x_3218_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_2998_, v_a_2999_, v_a_3007_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v_a_3219_; lean_object* v___x_3220_; 
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_a_3219_);
lean_dec_ref_known(v___x_3218_, 1);
v___x_3220_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3215_, v_a_3219_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_dec_ref_known(v___x_3220_, 1);
v___y_3093_ = v_a_2999_;
v___y_3094_ = v_a_3000_;
v___y_3095_ = v_a_3001_;
v___y_3096_ = v_a_3002_;
v___y_3097_ = v_a_3003_;
v___y_3098_ = v_a_3004_;
v___y_3099_ = v_a_3005_;
v___y_3100_ = v_a_3006_;
v___y_3101_ = v_a_3007_;
v___y_3102_ = v_a_3008_;
goto v___jp_3092_;
}
else
{
lean_dec(v_a_3008_);
lean_dec_ref(v_a_3007_);
lean_dec(v_a_3006_);
lean_dec_ref(v_a_3005_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec(v_a_3000_);
lean_dec(v_a_2999_);
lean_dec_ref(v_c_2998_);
return v___x_3220_;
}
}
else
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
lean_dec(v_a_3008_);
lean_dec_ref(v_a_3007_);
lean_dec(v_a_3006_);
lean_dec_ref(v_a_3005_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec(v_a_3000_);
lean_dec(v_a_2999_);
lean_dec_ref(v_c_2998_);
v_a_3221_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3223_ = v___x_3218_;
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3218_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3226_; 
if (v_isShared_3224_ == 0)
{
v___x_3226_ = v___x_3223_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
}
v___jp_3092_:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3103_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(v_c_2998_);
lean_inc_ref(v___y_3101_);
v___x_3104_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(v___x_3103_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v_p_3106_; uint8_t v___x_3107_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc(v_a_3105_);
lean_dec_ref_known(v___x_3104_, 1);
v_p_3106_ = lean_ctor_get(v_a_3105_, 0);
v___x_3107_ = l_Int_Internal_Linear_Poly_isUnsatLe(v_p_3106_);
if (v___x_3107_ == 0)
{
uint8_t v___x_3108_; 
v___x_3108_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_a_3105_);
if (v___x_3108_ == 0)
{
if (lean_obj_tag(v_p_3106_) == 1)
{
lean_object* v_k_3109_; lean_object* v_v_3110_; lean_object* v___x_3111_; 
v_k_3109_ = lean_ctor_get(v_p_3106_, 0);
lean_inc(v_k_3109_);
v_v_3110_ = lean_ctor_get(v_p_3106_, 1);
lean_inc(v_v_3110_);
lean_inc(v_a_3105_);
v___x_3111_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_a_3105_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3161_; 
v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3114_ = v___x_3111_;
v_isShared_3115_ = v_isSharedCheck_3161_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3111_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3161_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
uint8_t v___x_3116_; 
v___x_3116_ = lean_unbox(v_a_3112_);
lean_dec(v_a_3112_);
if (v___x_3116_ == 0)
{
lean_object* v___x_3117_; 
lean_del_object(v___x_3114_);
v___x_3117_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_a_3105_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; lean_object* v___x_3119_; 
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_a_3118_);
lean_dec_ref_known(v___x_3117_, 1);
v___x_3119_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_markStored___redArg(v_a_3118_, v___y_3093_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v_toCold_3120_; lean_object* v_options_3121_; lean_object* v_a_3122_; lean_object* v_inheritedTraceOptions_3123_; uint8_t v_hasTrace_3124_; lean_object* v___f_3125_; lean_object* v___f_3126_; 
v_toCold_3120_ = lean_ctor_get(v___y_3101_, 0);
v_options_3121_ = lean_ctor_get(v_toCold_3120_, 2);
v_a_3122_ = lean_ctor_get(v___x_3119_, 0);
lean_inc_n(v_a_3122_, 3);
lean_dec_ref_known(v___x_3119_, 1);
v_inheritedTraceOptions_3123_ = lean_ctor_get(v_toCold_3120_, 11);
v_hasTrace_3124_ = lean_ctor_get_uint8(v_options_3121_, sizeof(void*)*1);
lean_inc_n(v_v_3110_, 2);
v___f_3125_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3125_, 0, v_a_3122_);
lean_closure_set(v___f_3125_, 1, v_v_3110_);
v___f_3126_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3126_, 0, v_a_3122_);
lean_closure_set(v___f_3126_, 1, v_v_3110_);
if (v_hasTrace_3124_ == 0)
{
v___y_3041_ = v_k_3109_;
v___y_3042_ = v_v_3110_;
v___y_3043_ = v_a_3122_;
v___y_3044_ = v___f_3126_;
v___y_3045_ = v___f_3125_;
v___y_3046_ = v___y_3093_;
v___y_3047_ = v___y_3099_;
v___y_3048_ = v___y_3100_;
v___y_3049_ = v___y_3101_;
v___y_3050_ = v___y_3102_;
goto v___jp_3040_;
}
else
{
lean_object* v___x_3127_; lean_object* v___x_3128_; uint8_t v___x_3129_; 
v___x_3127_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2));
v___x_3128_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3);
v___x_3129_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3123_, v_options_3121_, v___x_3128_);
if (v___x_3129_ == 0)
{
v___y_3041_ = v_k_3109_;
v___y_3042_ = v_v_3110_;
v___y_3043_ = v_a_3122_;
v___y_3044_ = v___f_3126_;
v___y_3045_ = v___f_3125_;
v___y_3046_ = v___y_3093_;
v___y_3047_ = v___y_3099_;
v___y_3048_ = v___y_3100_;
v___y_3049_ = v___y_3101_;
v___y_3050_ = v___y_3102_;
goto v___jp_3040_;
}
else
{
lean_object* v___x_3130_; 
lean_inc(v_a_3122_);
v___x_3130_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3122_, v___y_3093_, v___y_3101_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3131_; lean_object* v___x_3132_; 
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_a_3131_);
lean_dec_ref_known(v___x_3130_, 1);
v___x_3132_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3127_, v_a_3131_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_dec_ref_known(v___x_3132_, 1);
v___y_3041_ = v_k_3109_;
v___y_3042_ = v_v_3110_;
v___y_3043_ = v_a_3122_;
v___y_3044_ = v___f_3126_;
v___y_3045_ = v___f_3125_;
v___y_3046_ = v___y_3093_;
v___y_3047_ = v___y_3099_;
v___y_3048_ = v___y_3100_;
v___y_3049_ = v___y_3101_;
v___y_3050_ = v___y_3102_;
goto v___jp_3040_;
}
else
{
lean_dec_ref(v___f_3126_);
lean_dec_ref(v___f_3125_);
lean_dec(v_a_3122_);
lean_dec(v_v_3110_);
lean_dec(v_k_3109_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3093_);
return v___x_3132_;
}
}
else
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
lean_dec_ref(v___f_3126_);
lean_dec_ref(v___f_3125_);
lean_dec(v_a_3122_);
lean_dec(v_v_3110_);
lean_dec(v_k_3109_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3093_);
v_a_3133_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v___x_3130_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3130_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_3133_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
}
}
else
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
lean_dec(v_v_3110_);
lean_dec(v_k_3109_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3093_);
v_a_3141_ = lean_ctor_get(v___x_3119_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3119_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3119_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
else
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
lean_dec(v_v_3110_);
lean_dec(v_k_3109_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3093_);
v_a_3149_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3151_ = v___x_3117_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_3117_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
else
{
lean_object* v___x_3157_; lean_object* v___x_3159_; 
lean_dec(v_v_3110_);
lean_dec(v_k_3109_);
lean_dec(v_a_3105_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec(v___y_3093_);
v___x_3157_ = lean_box(0);
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 0, v___x_3157_);
v___x_3159_ = v___x_3114_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3157_);
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
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_dec(v_v_3110_);
lean_dec(v_k_3109_);
lean_dec(v_a_3105_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec(v___y_3093_);
v_a_3162_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3111_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3111_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
else
{
lean_object* v___x_3170_; 
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
v___x_3170_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_a_3105_, v___y_3093_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3093_);
return v___x_3170_;
}
}
else
{
lean_object* v_toCold_3171_; lean_object* v_options_3172_; uint8_t v_hasTrace_3173_; 
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
v_toCold_3171_ = lean_ctor_get(v___y_3101_, 0);
v_options_3172_ = lean_ctor_get(v_toCold_3171_, 2);
v_hasTrace_3173_ = lean_ctor_get_uint8(v_options_3172_, sizeof(void*)*1);
if (v_hasTrace_3173_ == 0)
{
lean_dec(v_a_3105_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3093_);
goto v___jp_3010_;
}
else
{
lean_object* v_inheritedTraceOptions_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; uint8_t v___x_3177_; 
v_inheritedTraceOptions_3174_ = lean_ctor_get(v_toCold_3171_, 11);
v___x_3175_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5));
v___x_3176_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6);
v___x_3177_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3174_, v_options_3172_, v___x_3176_);
if (v___x_3177_ == 0)
{
lean_dec(v_a_3105_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3093_);
goto v___jp_3010_;
}
else
{
lean_object* v___x_3178_; 
v___x_3178_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3105_, v___y_3093_, v___y_3101_);
lean_dec(v___y_3093_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_object* v_a_3179_; lean_object* v___x_3180_; 
v_a_3179_ = lean_ctor_get(v___x_3178_, 0);
lean_inc(v_a_3179_);
lean_dec_ref_known(v___x_3178_, 1);
v___x_3180_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3175_, v_a_3179_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_dec_ref_known(v___x_3180_, 1);
goto v___jp_3010_;
}
else
{
return v___x_3180_;
}
}
else
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
v_a_3181_ = lean_ctor_get(v___x_3178_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_3178_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3178_);
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
}
}
else
{
lean_object* v_toCold_3189_; lean_object* v_options_3190_; uint8_t v_hasTrace_3191_; 
v_toCold_3189_ = lean_ctor_get(v___y_3101_, 0);
v_options_3190_ = lean_ctor_get(v_toCold_3189_, 2);
v_hasTrace_3191_ = lean_ctor_get_uint8(v_options_3190_, sizeof(void*)*1);
if (v_hasTrace_3191_ == 0)
{
v___y_3060_ = v_a_3105_;
v___y_3061_ = v___y_3093_;
v___y_3062_ = v___y_3094_;
v___y_3063_ = v___y_3095_;
v___y_3064_ = v___y_3096_;
v___y_3065_ = v___y_3097_;
v___y_3066_ = v___y_3098_;
v___y_3067_ = v___y_3099_;
v___y_3068_ = v___y_3100_;
v___y_3069_ = v___y_3101_;
v___y_3070_ = v___y_3102_;
goto v___jp_3059_;
}
else
{
lean_object* v_inheritedTraceOptions_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; uint8_t v___x_3195_; 
v_inheritedTraceOptions_3192_ = lean_ctor_get(v_toCold_3189_, 11);
v___x_3193_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8));
v___x_3194_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9);
v___x_3195_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3192_, v_options_3190_, v___x_3194_);
if (v___x_3195_ == 0)
{
v___y_3060_ = v_a_3105_;
v___y_3061_ = v___y_3093_;
v___y_3062_ = v___y_3094_;
v___y_3063_ = v___y_3095_;
v___y_3064_ = v___y_3096_;
v___y_3065_ = v___y_3097_;
v___y_3066_ = v___y_3098_;
v___y_3067_ = v___y_3099_;
v___y_3068_ = v___y_3100_;
v___y_3069_ = v___y_3101_;
v___y_3070_ = v___y_3102_;
goto v___jp_3059_;
}
else
{
lean_object* v___x_3196_; 
lean_inc(v_a_3105_);
v___x_3196_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3105_, v___y_3093_, v___y_3101_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_a_3197_; lean_object* v___x_3198_; 
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_a_3197_);
lean_dec_ref_known(v___x_3196_, 1);
v___x_3198_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3193_, v_a_3197_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_dec_ref_known(v___x_3198_, 1);
v___y_3060_ = v_a_3105_;
v___y_3061_ = v___y_3093_;
v___y_3062_ = v___y_3094_;
v___y_3063_ = v___y_3095_;
v___y_3064_ = v___y_3096_;
v___y_3065_ = v___y_3097_;
v___y_3066_ = v___y_3098_;
v___y_3067_ = v___y_3099_;
v___y_3068_ = v___y_3100_;
v___y_3069_ = v___y_3101_;
v___y_3070_ = v___y_3102_;
goto v___jp_3059_;
}
else
{
lean_dec(v_a_3105_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec(v___y_3093_);
return v___x_3198_;
}
}
else
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
lean_dec(v_a_3105_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec(v___y_3093_);
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
}
else
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3214_; 
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec(v___y_3093_);
v_a_3207_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3209_ = v___x_3104_;
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3104_);
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
}
else
{
lean_object* v___x_3229_; lean_object* v___x_3231_; 
lean_dec(v_a_3008_);
lean_dec_ref(v_a_3007_);
lean_dec(v_a_3006_);
lean_dec_ref(v_a_3005_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec(v_a_3000_);
lean_dec(v_a_2999_);
lean_dec_ref(v_c_2998_);
v___x_3229_ = lean_box(0);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 0, v___x_3229_);
v___x_3231_ = v___x_3085_;
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
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec(v_a_3008_);
lean_dec_ref(v_a_3007_);
lean_dec(v_a_3006_);
lean_dec_ref(v_a_3005_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec(v_a_3000_);
lean_dec(v_a_2999_);
lean_dec_ref(v_c_2998_);
v_a_3234_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3082_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3082_);
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
v___jp_3010_:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3011_ = lean_box(0);
v___x_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3011_);
return v___x_3012_;
}
v___jp_3013_:
{
lean_object* v___x_3018_; 
v___x_3018_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v___y_3015_, v___y_3016_, v___y_3017_);
lean_dec_ref(v___y_3017_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3031_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3021_ = v___x_3018_;
v_isShared_3022_ = v_isSharedCheck_3031_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3018_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3031_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
uint8_t v___x_3023_; uint8_t v___x_3024_; uint8_t v___x_3025_; 
v___x_3023_ = 0;
v___x_3024_ = lean_unbox(v_a_3019_);
lean_dec(v_a_3019_);
v___x_3025_ = l_Lean_instBEqLBool_beq(v___x_3024_, v___x_3023_);
if (v___x_3025_ == 0)
{
lean_object* v___x_3026_; lean_object* v___x_3028_; 
lean_dec(v___y_3016_);
lean_dec(v___y_3014_);
v___x_3026_ = lean_box(0);
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 0, v___x_3026_);
v___x_3028_ = v___x_3021_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v___x_3026_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
else
{
lean_object* v___x_3030_; 
lean_del_object(v___x_3021_);
v___x_3030_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v___y_3014_, v___y_3016_);
lean_dec(v___y_3016_);
return v___x_3030_;
}
}
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
lean_dec(v___y_3016_);
lean_dec(v___y_3014_);
v_a_3032_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_3018_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3018_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
v___jp_3040_:
{
lean_object* v_p_3051_; lean_object* v___x_3052_; 
v_p_3051_ = lean_ctor_get(v___y_3043_, 0);
lean_inc_ref(v_p_3051_);
v___x_3052_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_3051_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
lean_dec(v___y_3050_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v___x_3053_; uint8_t v___x_3054_; 
lean_dec_ref_known(v___x_3052_, 1);
v___x_3053_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_3054_ = lean_int_dec_lt(v___y_3041_, v___x_3053_);
lean_dec(v___y_3041_);
if (v___x_3054_ == 0)
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
lean_dec_ref(v___y_3045_);
v___x_3055_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3056_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3055_, v___y_3044_, v___y_3046_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_dec_ref_known(v___x_3056_, 1);
v___y_3014_ = v___y_3042_;
v___y_3015_ = v___y_3043_;
v___y_3016_ = v___y_3046_;
v___y_3017_ = v___y_3049_;
goto v___jp_3013_;
}
else
{
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3043_);
lean_dec(v___y_3042_);
return v___x_3056_;
}
}
else
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
lean_dec_ref(v___y_3044_);
v___x_3057_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3058_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3057_, v___y_3045_, v___y_3046_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_dec_ref_known(v___x_3058_, 1);
v___y_3014_ = v___y_3042_;
v___y_3015_ = v___y_3043_;
v___y_3016_ = v___y_3046_;
v___y_3017_ = v___y_3049_;
goto v___jp_3013_;
}
else
{
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3043_);
lean_dec(v___y_3042_);
return v___x_3058_;
}
}
}
else
{
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec_ref(v___y_3043_);
lean_dec(v___y_3042_);
lean_dec(v___y_3041_);
return v___x_3052_;
}
}
v___jp_3059_:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3071_, 0, v___y_3060_);
v___x_3072_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(v___x_3071_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec(v___y_3062_);
lean_dec(v___y_3061_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3080_; 
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3080_ == 0)
{
lean_object* v_unused_3081_; 
v_unused_3081_ = lean_ctor_get(v___x_3072_, 0);
lean_dec(v_unused_3081_);
v___x_3074_ = v___x_3072_;
v_isShared_3075_ = v_isSharedCheck_3080_;
goto v_resetjp_3073_;
}
else
{
lean_dec(v___x_3072_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3080_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3076_; lean_object* v___x_3078_; 
v___x_3076_ = lean_box(0);
if (v_isShared_3075_ == 0)
{
lean_ctor_set(v___x_3074_, 0, v___x_3076_);
v___x_3078_ = v___x_3074_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3076_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
else
{
return v___x_3072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___boxed(lean_object* v_c_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = lean_grind_cutsat_assert_le(v_c_3242_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(lean_object* v_c_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_){
_start:
{
lean_object* v_p_3267_; lean_object* v___x_3268_; 
v_p_3267_ = lean_ctor_get(v_c_3255_, 0);
lean_inc_ref(v_p_3267_);
v___x_3268_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_3267_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3269_);
lean_dec_ref_known(v___x_3268_, 1);
if (lean_obj_tag(v_a_3269_) == 1)
{
lean_object* v_val_3270_; lean_object* v_snd_3271_; lean_object* v_fst_3272_; lean_object* v_fst_3273_; lean_object* v_snd_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; 
v_val_3270_ = lean_ctor_get(v_a_3269_, 0);
lean_inc(v_val_3270_);
lean_dec_ref_known(v_a_3269_, 1);
v_snd_3271_ = lean_ctor_get(v_val_3270_, 1);
lean_inc(v_snd_3271_);
v_fst_3272_ = lean_ctor_get(v_val_3270_, 0);
lean_inc(v_fst_3272_);
lean_dec(v_val_3270_);
v_fst_3273_ = lean_ctor_get(v_snd_3271_, 0);
lean_inc(v_fst_3273_);
v_snd_3274_ = lean_ctor_get(v_snd_3271_, 1);
lean_inc(v_snd_3274_);
lean_dec(v_snd_3271_);
v___x_3275_ = lean_alloc_ctor(19, 3, 0);
lean_ctor_set(v___x_3275_, 0, v_c_3255_);
lean_ctor_set(v___x_3275_, 1, v_fst_3272_);
lean_ctor_set(v___x_3275_, 2, v_fst_3273_);
v___x_3276_ = lean_box(0);
v___x_3277_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3277_, 0, v_snd_3274_);
lean_ctor_set(v___x_3277_, 1, v___x_3275_);
lean_ctor_set(v___x_3277_, 2, v___x_3276_);
lean_inc(v_a_3265_);
lean_inc_ref(v_a_3264_);
lean_inc(v_a_3263_);
lean_inc_ref(v_a_3262_);
lean_inc(v_a_3261_);
lean_inc_ref(v_a_3260_);
lean_inc(v_a_3259_);
lean_inc_ref(v_a_3258_);
lean_inc(v_a_3257_);
lean_inc(v_a_3256_);
v___x_3278_ = lean_grind_cutsat_assert_le(v___x_3277_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_);
return v___x_3278_;
}
else
{
lean_object* v___x_3279_; 
lean_dec(v_a_3269_);
lean_inc(v_a_3265_);
lean_inc_ref(v_a_3264_);
lean_inc(v_a_3263_);
lean_inc_ref(v_a_3262_);
lean_inc(v_a_3261_);
lean_inc_ref(v_a_3260_);
lean_inc(v_a_3259_);
lean_inc_ref(v_a_3258_);
lean_inc(v_a_3257_);
lean_inc(v_a_3256_);
v___x_3279_ = lean_grind_cutsat_assert_le(v_c_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_);
return v___x_3279_;
}
}
else
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
lean_dec_ref(v_c_3255_);
v_a_3280_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3282_ = v___x_3268_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v___x_3268_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3280_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore___boxed(lean_object* v_c_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v_c_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_);
lean_dec(v_a_3298_);
lean_dec_ref(v_a_3297_);
lean_dec(v_a_3296_);
lean_dec_ref(v_a_3295_);
lean_dec(v_a_3294_);
lean_dec_ref(v_a_3293_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec(v_a_3289_);
return v_res_3300_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__3(void){
_start:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3306_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0);
v___x_3307_ = lean_int_neg(v___x_3306_);
return v___x_3307_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__6(void){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3314_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__5));
v___x_3315_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_3316_ = l_Lean_Name_append(v___x_3315_, v___x_3314_);
return v___x_3316_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__8(void){
_start:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3318_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__7));
v___x_3319_ = l_Lean_stringToMessageData(v___x_3318_);
return v___x_3319_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__10(void){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3321_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__9));
v___x_3322_ = l_Lean_stringToMessageData(v___x_3321_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(lean_object* v_e_3323_, uint8_t v_eqTrue_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_){
_start:
{
lean_object* v_c_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___x_3379_; 
lean_inc_ref(v_e_3323_);
v___x_3379_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3323_, v_a_3332_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_object* v_a_3380_; lean_object* v___x_3381_; uint8_t v___x_3382_; 
v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
lean_inc(v_a_3380_);
lean_dec_ref_known(v___x_3379_, 1);
v___x_3381_ = l_Lean_Expr_cleanupAnnotations(v_a_3380_);
lean_dec(v_a_3380_);
v___x_3382_ = l_Lean_Expr_isApp(v___x_3381_);
if (v___x_3382_ == 0)
{
lean_dec_ref(v___x_3381_);
lean_dec_ref(v_e_3323_);
goto v___jp_3358_;
}
else
{
lean_object* v___x_3383_; uint8_t v___x_3384_; 
v___x_3383_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3381_);
v___x_3384_ = l_Lean_Expr_isApp(v___x_3383_);
if (v___x_3384_ == 0)
{
lean_dec_ref(v___x_3383_);
lean_dec_ref(v___x_3381_);
lean_dec_ref(v_e_3323_);
goto v___jp_3358_;
}
else
{
lean_object* v___x_3385_; uint8_t v___x_3386_; 
v___x_3385_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3383_);
v___x_3386_ = l_Lean_Expr_isApp(v___x_3385_);
if (v___x_3386_ == 0)
{
lean_dec_ref(v___x_3385_);
lean_dec_ref(v___x_3383_);
lean_dec_ref(v___x_3381_);
lean_dec_ref(v_e_3323_);
goto v___jp_3358_;
}
else
{
lean_object* v___x_3387_; uint8_t v___x_3388_; 
v___x_3387_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3385_);
v___x_3388_ = l_Lean_Expr_isApp(v___x_3387_);
if (v___x_3388_ == 0)
{
lean_dec_ref(v___x_3387_);
lean_dec_ref(v___x_3385_);
lean_dec_ref(v___x_3383_);
lean_dec_ref(v___x_3381_);
lean_dec_ref(v_e_3323_);
goto v___jp_3358_;
}
else
{
lean_object* v___x_3389_; lean_object* v___x_3390_; uint8_t v___x_3391_; 
v___x_3389_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3387_);
lean_dec_ref(v___x_3387_);
v___x_3390_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__2));
v___x_3391_ = l_Lean_Expr_isConstOf(v___x_3389_, v___x_3390_);
lean_dec_ref(v___x_3389_);
if (v___x_3391_ == 0)
{
lean_dec_ref(v___x_3385_);
lean_dec_ref(v___x_3383_);
lean_dec_ref(v___x_3381_);
lean_dec_ref(v_e_3323_);
goto v___jp_3358_;
}
else
{
lean_object* v_arg_3392_; lean_object* v_arg_3393_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v_arg_3463_; lean_object* v___x_3464_; 
v_arg_3392_ = lean_ctor_get(v___x_3381_, 1);
lean_inc_ref(v_arg_3392_);
lean_dec_ref(v___x_3381_);
v_arg_3393_ = lean_ctor_get(v___x_3383_, 1);
lean_inc_ref(v_arg_3393_);
lean_dec_ref(v___x_3383_);
v_arg_3463_ = lean_ctor_get(v___x_3385_, 1);
lean_inc_ref(v_arg_3463_);
lean_dec_ref(v___x_3385_);
v___x_3464_ = l_Lean_Meta_Structural_isInstLEInt___redArg(v_arg_3463_, v_a_3332_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3536_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3467_ = v___x_3464_;
v_isShared_3468_ = v_isSharedCheck_3536_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3464_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3536_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
uint8_t v___x_3469_; 
v___x_3469_ = lean_unbox(v_a_3465_);
lean_dec(v_a_3465_);
if (v___x_3469_ == 0)
{
lean_object* v___x_3470_; lean_object* v___x_3472_; 
lean_dec_ref(v_arg_3393_);
lean_dec_ref(v_arg_3392_);
lean_dec_ref(v_e_3323_);
v___x_3470_ = lean_box(0);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 0, v___x_3470_);
v___x_3472_ = v___x_3467_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3470_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
else
{
lean_object* v___x_3474_; 
lean_del_object(v___x_3467_);
lean_inc_ref(v_arg_3392_);
v___x_3474_ = l_Lean_Meta_getIntValue_x3f(v_arg_3392_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3475_; 
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_a_3475_);
lean_dec_ref_known(v___x_3474_, 1);
if (lean_obj_tag(v_a_3475_) == 1)
{
lean_object* v_val_3476_; lean_object* v___x_3477_; uint8_t v___x_3478_; 
v_val_3476_ = lean_ctor_get(v_a_3475_, 0);
lean_inc(v_val_3476_);
lean_dec_ref_known(v_a_3475_, 1);
v___x_3477_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_3478_ = lean_int_dec_eq(v_val_3476_, v___x_3477_);
lean_dec(v_val_3476_);
if (v___x_3478_ == 0)
{
v___y_3442_ = v_a_3325_;
v___y_3443_ = v_a_3326_;
v___y_3444_ = v_a_3327_;
v___y_3445_ = v_a_3328_;
v___y_3446_ = v_a_3329_;
v___y_3447_ = v_a_3330_;
v___y_3448_ = v_a_3331_;
v___y_3449_ = v_a_3332_;
v___y_3450_ = v_a_3333_;
v___y_3451_ = v_a_3334_;
goto v___jp_3441_;
}
else
{
lean_object* v___x_3479_; 
lean_inc_ref(v_arg_3393_);
v___x_3479_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly_x3f(v_arg_3393_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; 
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_a_3480_);
lean_dec_ref_known(v___x_3479_, 1);
if (lean_obj_tag(v_a_3480_) == 1)
{
lean_object* v_val_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3519_; 
lean_dec_ref(v_arg_3393_);
lean_dec_ref(v_arg_3392_);
v_val_3481_ = lean_ctor_get(v_a_3480_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v_a_3480_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3483_ = v_a_3480_;
v_isShared_3484_ = v_isSharedCheck_3519_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_val_3481_);
lean_dec(v_a_3480_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3519_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v_toCold_3508_; lean_object* v_options_3509_; uint8_t v_hasTrace_3510_; 
v_toCold_3508_ = lean_ctor_get(v_a_3333_, 0);
v_options_3509_ = lean_ctor_get(v_toCold_3508_, 2);
v_hasTrace_3510_ = lean_ctor_get_uint8(v_options_3509_, sizeof(void*)*1);
if (v_hasTrace_3510_ == 0)
{
v___y_3486_ = v_a_3325_;
v___y_3487_ = v_a_3326_;
v___y_3488_ = v_a_3327_;
v___y_3489_ = v_a_3328_;
v___y_3490_ = v_a_3329_;
v___y_3491_ = v_a_3330_;
v___y_3492_ = v_a_3331_;
v___y_3493_ = v_a_3332_;
v___y_3494_ = v_a_3333_;
v___y_3495_ = v_a_3334_;
goto v___jp_3485_;
}
else
{
lean_object* v_inheritedTraceOptions_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; uint8_t v___x_3514_; 
v_inheritedTraceOptions_3511_ = lean_ctor_get(v_toCold_3508_, 11);
v___x_3512_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__5));
v___x_3513_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__6);
v___x_3514_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3511_, v_options_3509_, v___x_3513_);
if (v___x_3514_ == 0)
{
v___y_3486_ = v_a_3325_;
v___y_3487_ = v_a_3326_;
v___y_3488_ = v_a_3327_;
v___y_3489_ = v_a_3328_;
v___y_3490_ = v_a_3329_;
v___y_3491_ = v_a_3330_;
v___y_3492_ = v_a_3331_;
v___y_3493_ = v_a_3332_;
v___y_3494_ = v_a_3333_;
v___y_3495_ = v_a_3334_;
goto v___jp_3485_;
}
else
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3515_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__10);
lean_inc_ref(v_e_3323_);
v___x_3516_ = l_Lean_MessageData_ofExpr(v_e_3323_);
v___x_3517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3515_);
lean_ctor_set(v___x_3517_, 1, v___x_3516_);
v___x_3518_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3512_, v___x_3517_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_dec_ref_known(v___x_3518_, 1);
v___y_3486_ = v_a_3325_;
v___y_3487_ = v_a_3326_;
v___y_3488_ = v_a_3327_;
v___y_3489_ = v_a_3328_;
v___y_3490_ = v_a_3329_;
v___y_3491_ = v_a_3330_;
v___y_3492_ = v_a_3331_;
v___y_3493_ = v_a_3332_;
v___y_3494_ = v_a_3333_;
v___y_3495_ = v_a_3334_;
goto v___jp_3485_;
}
else
{
lean_del_object(v___x_3483_);
lean_dec(v_val_3481_);
lean_dec_ref(v_e_3323_);
return v___x_3518_;
}
}
}
v___jp_3485_:
{
if (v_eqTrue_3324_ == 0)
{
lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
lean_del_object(v___x_3483_);
v___x_3496_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0);
v___x_3497_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__3);
lean_inc(v_val_3481_);
v___x_3498_ = l_Int_Internal_Linear_Poly_mul(v_val_3481_, v___x_3497_);
v___x_3499_ = l_Int_Internal_Linear_Poly_addConst(v___x_3498_, v___x_3496_);
v___x_3500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3500_, 0, v_e_3323_);
lean_ctor_set(v___x_3500_, 1, v_val_3481_);
v___x_3501_ = lean_box(0);
v___x_3502_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3499_);
lean_ctor_set(v___x_3502_, 1, v___x_3500_);
lean_ctor_set(v___x_3502_, 2, v___x_3501_);
v_c_3337_ = v___x_3502_;
v___y_3338_ = v___y_3486_;
v___y_3339_ = v___y_3487_;
v___y_3340_ = v___y_3488_;
v___y_3341_ = v___y_3489_;
v___y_3342_ = v___y_3490_;
v___y_3343_ = v___y_3491_;
v___y_3344_ = v___y_3492_;
v___y_3345_ = v___y_3493_;
v___y_3346_ = v___y_3494_;
v___y_3347_ = v___y_3495_;
goto v___jp_3336_;
}
else
{
lean_object* v___x_3504_; 
if (v_isShared_3484_ == 0)
{
lean_ctor_set_tag(v___x_3483_, 0);
lean_ctor_set(v___x_3483_, 0, v_e_3323_);
v___x_3504_ = v___x_3483_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_e_3323_);
v___x_3504_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3505_ = lean_box(0);
v___x_3506_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3506_, 0, v_val_3481_);
lean_ctor_set(v___x_3506_, 1, v___x_3504_);
lean_ctor_set(v___x_3506_, 2, v___x_3505_);
v_c_3337_ = v___x_3506_;
v___y_3338_ = v___y_3486_;
v___y_3339_ = v___y_3487_;
v___y_3340_ = v___y_3488_;
v___y_3341_ = v___y_3489_;
v___y_3342_ = v___y_3490_;
v___y_3343_ = v___y_3491_;
v___y_3344_ = v___y_3492_;
v___y_3345_ = v___y_3493_;
v___y_3346_ = v___y_3494_;
v___y_3347_ = v___y_3495_;
goto v___jp_3336_;
}
}
}
}
}
else
{
lean_dec(v_a_3480_);
v___y_3442_ = v_a_3325_;
v___y_3443_ = v_a_3326_;
v___y_3444_ = v_a_3327_;
v___y_3445_ = v_a_3328_;
v___y_3446_ = v_a_3329_;
v___y_3447_ = v_a_3330_;
v___y_3448_ = v_a_3331_;
v___y_3449_ = v_a_3332_;
v___y_3450_ = v_a_3333_;
v___y_3451_ = v_a_3334_;
goto v___jp_3441_;
}
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
lean_dec_ref(v_arg_3393_);
lean_dec_ref(v_arg_3392_);
lean_dec_ref(v_e_3323_);
v_a_3520_ = lean_ctor_get(v___x_3479_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3479_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3479_);
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
}
}
else
{
lean_dec(v_a_3475_);
v___y_3442_ = v_a_3325_;
v___y_3443_ = v_a_3326_;
v___y_3444_ = v_a_3327_;
v___y_3445_ = v_a_3328_;
v___y_3446_ = v_a_3329_;
v___y_3447_ = v_a_3330_;
v___y_3448_ = v_a_3331_;
v___y_3449_ = v_a_3332_;
v___y_3450_ = v_a_3333_;
v___y_3451_ = v_a_3334_;
goto v___jp_3441_;
}
}
else
{
lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3535_; 
lean_dec_ref(v_arg_3393_);
lean_dec_ref(v_arg_3392_);
lean_dec_ref(v_e_3323_);
v_a_3528_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3530_ = v___x_3474_;
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_3474_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
if (v_isShared_3531_ == 0)
{
v___x_3533_ = v___x_3530_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_a_3528_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
}
}
else
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3544_; 
lean_dec_ref(v_arg_3393_);
lean_dec_ref(v_arg_3392_);
lean_dec_ref(v_e_3323_);
v_a_3537_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3539_ = v___x_3464_;
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3464_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3542_; 
if (v_isShared_3540_ == 0)
{
v___x_3542_ = v___x_3539_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_a_3537_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
v___jp_3394_:
{
lean_object* v___x_3405_; 
v___x_3405_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3323_, v___y_3395_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; lean_object* v___x_3407_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc_n(v_a_3406_, 2);
lean_dec_ref_known(v___x_3405_, 1);
v___x_3407_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_arg_3393_, v_a_3406_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; lean_object* v___x_3409_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3408_);
lean_dec_ref_known(v___x_3407_, 1);
v___x_3409_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_arg_3392_, v_a_3406_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v_a_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v_a_3410_ = lean_ctor_get(v___x_3409_, 0);
lean_inc_n(v_a_3410_, 2);
lean_dec_ref_known(v___x_3409_, 1);
lean_inc(v_a_3408_);
v___x_3411_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3411_, 0, v_a_3408_);
lean_ctor_set(v___x_3411_, 1, v_a_3410_);
v___x_3412_ = l_Int_Internal_Linear_Expr_norm(v___x_3411_);
lean_dec_ref_known(v___x_3411_, 2);
if (v_eqTrue_3324_ == 0)
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3413_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0);
v___x_3414_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__3);
v___x_3415_ = l_Int_Internal_Linear_Poly_mul(v___x_3412_, v___x_3414_);
v___x_3416_ = l_Int_Internal_Linear_Poly_addConst(v___x_3415_, v___x_3413_);
v___y_3362_ = v___y_3395_;
v___y_3363_ = v___y_3402_;
v___y_3364_ = v___y_3398_;
v___y_3365_ = v_a_3408_;
v___y_3366_ = v_a_3410_;
v___y_3367_ = v___y_3396_;
v___y_3368_ = v___y_3397_;
v___y_3369_ = v___y_3400_;
v___y_3370_ = v___y_3403_;
v___y_3371_ = v___y_3399_;
v___y_3372_ = v___y_3401_;
v___y_3373_ = v___y_3404_;
v___y_3374_ = v___x_3416_;
goto v___jp_3361_;
}
else
{
v___y_3362_ = v___y_3395_;
v___y_3363_ = v___y_3402_;
v___y_3364_ = v___y_3398_;
v___y_3365_ = v_a_3408_;
v___y_3366_ = v_a_3410_;
v___y_3367_ = v___y_3396_;
v___y_3368_ = v___y_3397_;
v___y_3369_ = v___y_3400_;
v___y_3370_ = v___y_3403_;
v___y_3371_ = v___y_3399_;
v___y_3372_ = v___y_3401_;
v___y_3373_ = v___y_3404_;
v___y_3374_ = v___x_3412_;
goto v___jp_3361_;
}
}
else
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
lean_dec(v_a_3408_);
lean_dec_ref(v_e_3323_);
v_a_3417_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3419_ = v___x_3409_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3409_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3417_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
else
{
lean_object* v_a_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3432_; 
lean_dec(v_a_3406_);
lean_dec_ref(v_arg_3392_);
lean_dec_ref(v_e_3323_);
v_a_3425_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3427_ = v___x_3407_;
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_a_3425_);
lean_dec(v___x_3407_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3430_; 
if (v_isShared_3428_ == 0)
{
v___x_3430_ = v___x_3427_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_a_3425_);
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
lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3440_; 
lean_dec_ref(v_arg_3393_);
lean_dec_ref(v_arg_3392_);
lean_dec_ref(v_e_3323_);
v_a_3433_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3435_ = v___x_3405_;
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3405_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3438_; 
if (v_isShared_3436_ == 0)
{
v___x_3438_ = v___x_3435_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_a_3433_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
}
v___jp_3441_:
{
lean_object* v_toCold_3452_; lean_object* v_options_3453_; uint8_t v_hasTrace_3454_; 
v_toCold_3452_ = lean_ctor_get(v___y_3450_, 0);
v_options_3453_ = lean_ctor_get(v_toCold_3452_, 2);
v_hasTrace_3454_ = lean_ctor_get_uint8(v_options_3453_, sizeof(void*)*1);
if (v_hasTrace_3454_ == 0)
{
v___y_3395_ = v___y_3442_;
v___y_3396_ = v___y_3443_;
v___y_3397_ = v___y_3444_;
v___y_3398_ = v___y_3445_;
v___y_3399_ = v___y_3446_;
v___y_3400_ = v___y_3447_;
v___y_3401_ = v___y_3448_;
v___y_3402_ = v___y_3449_;
v___y_3403_ = v___y_3450_;
v___y_3404_ = v___y_3451_;
goto v___jp_3394_;
}
else
{
lean_object* v_inheritedTraceOptions_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; uint8_t v___x_3458_; 
v_inheritedTraceOptions_3455_ = lean_ctor_get(v_toCold_3452_, 11);
v___x_3456_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__5));
v___x_3457_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__6);
v___x_3458_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3455_, v_options_3453_, v___x_3457_);
if (v___x_3458_ == 0)
{
v___y_3395_ = v___y_3442_;
v___y_3396_ = v___y_3443_;
v___y_3397_ = v___y_3444_;
v___y_3398_ = v___y_3445_;
v___y_3399_ = v___y_3446_;
v___y_3400_ = v___y_3447_;
v___y_3401_ = v___y_3448_;
v___y_3402_ = v___y_3449_;
v___y_3403_ = v___y_3450_;
v___y_3404_ = v___y_3451_;
goto v___jp_3394_;
}
else
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; 
v___x_3459_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__8);
lean_inc_ref(v_e_3323_);
v___x_3460_ = l_Lean_MessageData_ofExpr(v_e_3323_);
v___x_3461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3459_);
lean_ctor_set(v___x_3461_, 1, v___x_3460_);
v___x_3462_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3456_, v___x_3461_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_dec_ref_known(v___x_3462_, 1);
v___y_3395_ = v___y_3442_;
v___y_3396_ = v___y_3443_;
v___y_3397_ = v___y_3444_;
v___y_3398_ = v___y_3445_;
v___y_3399_ = v___y_3446_;
v___y_3400_ = v___y_3447_;
v___y_3401_ = v___y_3448_;
v___y_3402_ = v___y_3449_;
v___y_3403_ = v___y_3450_;
v___y_3404_ = v___y_3451_;
goto v___jp_3394_;
}
else
{
lean_dec_ref(v_arg_3393_);
lean_dec_ref(v_arg_3392_);
lean_dec_ref(v_e_3323_);
return v___x_3462_;
}
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
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
lean_dec_ref(v_e_3323_);
v_a_3545_ = lean_ctor_get(v___x_3379_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3379_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3547_ = v___x_3379_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3379_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
if (v_isShared_3548_ == 0)
{
v___x_3550_ = v___x_3547_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3545_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
v___jp_3336_:
{
lean_object* v___x_3348_; 
v___x_3348_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v_c_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3356_; 
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3356_ == 0)
{
lean_object* v_unused_3357_; 
v_unused_3357_ = lean_ctor_get(v___x_3348_, 0);
lean_dec(v_unused_3357_);
v___x_3350_ = v___x_3348_;
v_isShared_3351_ = v_isSharedCheck_3356_;
goto v_resetjp_3349_;
}
else
{
lean_dec(v___x_3348_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3356_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3352_; lean_object* v___x_3354_; 
v___x_3352_ = lean_box(0);
if (v_isShared_3351_ == 0)
{
lean_ctor_set(v___x_3350_, 0, v___x_3352_);
v___x_3354_ = v___x_3350_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3352_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
else
{
return v___x_3348_;
}
}
v___jp_3358_:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3359_ = lean_box(0);
v___x_3360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3359_);
return v___x_3360_;
}
v___jp_3361_:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3375_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_3375_, 0, v_e_3323_);
lean_ctor_set(v___x_3375_, 1, v___y_3365_);
lean_ctor_set(v___x_3375_, 2, v___y_3366_);
lean_ctor_set_uint8(v___x_3375_, sizeof(void*)*3, v_eqTrue_3324_);
v___x_3376_ = lean_box(0);
v___x_3377_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3377_, 0, v___y_3374_);
lean_ctor_set(v___x_3377_, 1, v___x_3375_);
lean_ctor_set(v___x_3377_, 2, v___x_3376_);
v___x_3378_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3377_, v___y_3362_, v___y_3367_, v___y_3368_, v___y_3364_, v___y_3371_, v___y_3369_, v___y_3372_, v___y_3363_, v___y_3370_, v___y_3373_);
return v___x_3378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___boxed(lean_object* v_e_3553_, lean_object* v_eqTrue_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_){
_start:
{
uint8_t v_eqTrue_boxed_3566_; lean_object* v_res_3567_; 
v_eqTrue_boxed_3566_ = lean_unbox(v_eqTrue_3554_);
v_res_3567_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(v_e_3553_, v_eqTrue_boxed_3566_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_);
lean_dec(v_a_3564_);
lean_dec_ref(v_a_3563_);
lean_dec(v_a_3562_);
lean_dec_ref(v_a_3561_);
lean_dec(v_a_3560_);
lean_dec_ref(v_a_3559_);
lean_dec(v_a_3558_);
lean_dec_ref(v_a_3557_);
lean_dec(v_a_3556_);
lean_dec(v_a_3555_);
return v_res_3567_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0(void){
_start:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3568_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0);
v___x_3569_ = l_Lean_mkIntLit(v___x_3568_);
return v___x_3569_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5(void){
_start:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3577_ = lean_box(0);
v___x_3578_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4));
v___x_3579_ = l_Lean_mkConst(v___x_3578_, v___x_3577_);
return v___x_3579_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8(void){
_start:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3585_ = lean_box(0);
v___x_3586_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7));
v___x_3587_ = l_Lean_mkConst(v___x_3586_, v___x_3585_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(lean_object* v_e_3588_, uint8_t v_eqTrue_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_){
_start:
{
lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v_fst_3604_; lean_object* v_snd_3605_; lean_object* v___x_3635_; uint8_t v___x_3636_; 
v___x_3635_ = l_Lean_Expr_cleanupAnnotations(v_e_3588_);
v___x_3636_ = l_Lean_Expr_isApp(v___x_3635_);
if (v___x_3636_ == 0)
{
lean_dec_ref(v___x_3635_);
lean_dec_ref(v_e_3588_);
goto v___jp_3632_;
}
else
{
lean_object* v___x_3637_; uint8_t v___x_3638_; 
v___x_3637_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3635_);
v___x_3638_ = l_Lean_Expr_isApp(v___x_3637_);
if (v___x_3638_ == 0)
{
lean_dec_ref(v___x_3637_);
lean_dec_ref(v___x_3635_);
lean_dec_ref(v_e_3588_);
goto v___jp_3632_;
}
else
{
lean_object* v___x_3639_; uint8_t v___x_3640_; 
v___x_3639_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3637_);
v___x_3640_ = l_Lean_Expr_isApp(v___x_3639_);
if (v___x_3640_ == 0)
{
lean_dec_ref(v___x_3639_);
lean_dec_ref(v___x_3637_);
lean_dec_ref(v___x_3635_);
lean_dec_ref(v_e_3588_);
goto v___jp_3632_;
}
else
{
lean_object* v___x_3641_; uint8_t v___x_3642_; 
v___x_3641_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3639_);
lean_dec_ref(v___x_3639_);
v___x_3642_ = l_Lean_Expr_isApp(v___x_3641_);
if (v___x_3642_ == 0)
{
lean_dec_ref(v___x_3641_);
lean_dec_ref(v___x_3637_);
lean_dec_ref(v___x_3635_);
lean_dec_ref(v_e_3588_);
goto v___jp_3632_;
}
else
{
lean_object* v___x_3643_; lean_object* v___x_3644_; uint8_t v___x_3645_; 
v___x_3643_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3641_);
lean_dec_ref(v___x_3641_);
v___x_3644_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__2));
v___x_3645_ = l_Lean_Expr_isConstOf(v___x_3643_, v___x_3644_);
lean_dec_ref(v___x_3643_);
if (v___x_3645_ == 0)
{
lean_dec_ref(v___x_3637_);
lean_dec_ref(v___x_3635_);
lean_dec_ref(v_e_3588_);
goto v___jp_3632_;
}
else
{
lean_object* v_arg_3646_; lean_object* v_arg_3647_; lean_object* v___y_3649_; 
v_arg_3646_ = lean_ctor_get(v___x_3635_, 1);
lean_inc_ref(v_arg_3646_);
lean_dec_ref(v___x_3635_);
v_arg_3647_ = lean_ctor_get(v___x_3637_, 1);
lean_inc_ref(v_arg_3647_);
lean_dec_ref(v___x_3637_);
if (v_eqTrue_3589_ == 0)
{
lean_object* v___x_3687_; 
v___x_3687_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5);
v___y_3649_ = v___x_3687_;
goto v___jp_3648_;
}
else
{
lean_object* v___x_3688_; 
v___x_3688_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8);
v___y_3649_ = v___x_3688_;
goto v___jp_3648_;
}
v___jp_3648_:
{
lean_object* v___x_3650_; 
v___x_3650_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3588_, v_a_3590_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v_a_3651_; lean_object* v___x_3652_; 
v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
lean_inc(v_a_3651_);
lean_dec_ref_known(v___x_3650_, 1);
lean_inc_ref(v_arg_3647_);
v___x_3652_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_3647_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v_a_3653_; lean_object* v_fst_3654_; lean_object* v_snd_3655_; lean_object* v___x_3656_; 
v_a_3653_ = lean_ctor_get(v___x_3652_, 0);
lean_inc(v_a_3653_);
lean_dec_ref_known(v___x_3652_, 1);
v_fst_3654_ = lean_ctor_get(v_a_3653_, 0);
lean_inc(v_fst_3654_);
v_snd_3655_ = lean_ctor_get(v_a_3653_, 1);
lean_inc(v_snd_3655_);
lean_dec(v_a_3653_);
lean_inc_ref(v_arg_3646_);
v___x_3656_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_3646_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_);
if (lean_obj_tag(v___x_3656_) == 0)
{
lean_object* v_a_3657_; lean_object* v_fst_3658_; lean_object* v_snd_3659_; lean_object* v___x_3660_; 
v_a_3657_ = lean_ctor_get(v___x_3656_, 0);
lean_inc(v_a_3657_);
lean_dec_ref_known(v___x_3656_, 1);
v_fst_3658_ = lean_ctor_get(v_a_3657_, 0);
lean_inc_n(v_fst_3658_, 2);
v_snd_3659_ = lean_ctor_get(v_a_3657_, 1);
lean_inc(v_snd_3659_);
lean_dec(v_a_3657_);
lean_inc(v_fst_3654_);
lean_inc_ref(v___y_3649_);
v___x_3660_ = l_Lean_mkApp6(v___y_3649_, v_arg_3647_, v_arg_3646_, v_fst_3654_, v_fst_3658_, v_snd_3655_, v_snd_3659_);
if (v_eqTrue_3589_ == 0)
{
lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3661_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
v___x_3662_ = l_Lean_mkIntAdd(v_fst_3658_, v___x_3661_);
v___y_3602_ = v___x_3660_;
v___y_3603_ = v_a_3651_;
v_fst_3604_ = v___x_3662_;
v_snd_3605_ = v_fst_3654_;
goto v___jp_3601_;
}
else
{
v___y_3602_ = v___x_3660_;
v___y_3603_ = v_a_3651_;
v_fst_3604_ = v_fst_3654_;
v_snd_3605_ = v_fst_3658_;
goto v___jp_3601_;
}
}
else
{
lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3670_; 
lean_dec(v_snd_3655_);
lean_dec(v_fst_3654_);
lean_dec(v_a_3651_);
lean_dec_ref(v_arg_3647_);
lean_dec_ref(v_arg_3646_);
lean_dec_ref(v_e_3588_);
v_a_3663_ = lean_ctor_get(v___x_3656_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3665_ = v___x_3656_;
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v___x_3656_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3668_; 
if (v_isShared_3666_ == 0)
{
v___x_3668_ = v___x_3665_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3663_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
}
else
{
lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3678_; 
lean_dec(v_a_3651_);
lean_dec_ref(v_arg_3647_);
lean_dec_ref(v_arg_3646_);
lean_dec_ref(v_e_3588_);
v_a_3671_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3673_ = v___x_3652_;
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v___x_3652_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3676_; 
if (v_isShared_3674_ == 0)
{
v___x_3676_ = v___x_3673_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_a_3671_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
}
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
lean_dec_ref(v_arg_3647_);
lean_dec_ref(v_arg_3646_);
lean_dec_ref(v_e_3588_);
v_a_3679_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3650_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3650_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
}
}
}
}
}
v___jp_3601_:
{
lean_object* v___x_3606_; 
lean_inc(v___y_3603_);
v___x_3606_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_3604_, v___y_3603_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; lean_object* v___x_3608_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
lean_inc(v_a_3607_);
lean_dec_ref_known(v___x_3606_, 1);
v___x_3608_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_snd_3605_, v___y_3603_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v_a_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc_n(v_a_3609_, 2);
lean_dec_ref_known(v___x_3608_, 1);
lean_inc(v_a_3607_);
v___x_3610_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3610_, 0, v_a_3607_);
lean_ctor_set(v___x_3610_, 1, v_a_3609_);
v___x_3611_ = l_Int_Internal_Linear_Expr_norm(v___x_3610_);
lean_dec_ref_known(v___x_3610_, 2);
v___x_3612_ = lean_alloc_ctor(2, 4, 1);
lean_ctor_set(v___x_3612_, 0, v_e_3588_);
lean_ctor_set(v___x_3612_, 1, v___y_3602_);
lean_ctor_set(v___x_3612_, 2, v_a_3607_);
lean_ctor_set(v___x_3612_, 3, v_a_3609_);
lean_ctor_set_uint8(v___x_3612_, sizeof(void*)*4, v_eqTrue_3589_);
v___x_3613_ = lean_box(0);
v___x_3614_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3611_);
lean_ctor_set(v___x_3614_, 1, v___x_3612_);
lean_ctor_set(v___x_3614_, 2, v___x_3613_);
v___x_3615_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3614_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_);
return v___x_3615_;
}
else
{
lean_object* v_a_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3623_; 
lean_dec(v_a_3607_);
lean_dec_ref(v___y_3602_);
lean_dec_ref(v_e_3588_);
v_a_3616_ = lean_ctor_get(v___x_3608_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3618_ = v___x_3608_;
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_a_3616_);
lean_dec(v___x_3608_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3621_; 
if (v_isShared_3619_ == 0)
{
v___x_3621_ = v___x_3618_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_a_3616_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
}
else
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
lean_dec_ref(v_snd_3605_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
lean_dec_ref(v_e_3588_);
v_a_3624_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3606_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3606_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
}
v___jp_3632_:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3633_ = lean_box(0);
v___x_3634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3633_);
return v___x_3634_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___boxed(lean_object* v_e_3689_, lean_object* v_eqTrue_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_){
_start:
{
uint8_t v_eqTrue_boxed_3702_; lean_object* v_res_3703_; 
v_eqTrue_boxed_3702_ = lean_unbox(v_eqTrue_3690_);
v_res_3703_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(v_e_3689_, v_eqTrue_boxed_3702_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_, v_a_3700_);
lean_dec(v_a_3700_);
lean_dec_ref(v_a_3699_);
lean_dec(v_a_3698_);
lean_dec_ref(v_a_3697_);
lean_dec(v_a_3696_);
lean_dec_ref(v_a_3695_);
lean_dec(v_a_3694_);
lean_dec_ref(v_a_3693_);
lean_dec(v_a_3692_);
lean_dec(v_a_3691_);
return v_res_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(lean_object* v_e_3709_, uint8_t v_eqTrue_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_){
_start:
{
lean_object* v___x_3725_; 
v___x_3725_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3713_);
if (lean_obj_tag(v___x_3725_) == 0)
{
lean_object* v_a_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3757_; 
v_a_3726_ = lean_ctor_get(v___x_3725_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3725_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3728_ = v___x_3725_;
v_isShared_3729_ = v_isSharedCheck_3757_;
goto v_resetjp_3727_;
}
else
{
lean_inc(v_a_3726_);
lean_dec(v___x_3725_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3757_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
uint8_t v_lia_3730_; 
v_lia_3730_ = lean_ctor_get_uint8(v_a_3726_, sizeof(void*)*18 + 24);
lean_dec(v_a_3726_);
if (v_lia_3730_ == 0)
{
lean_object* v___x_3731_; lean_object* v___x_3733_; 
lean_dec_ref(v_e_3709_);
v___x_3731_ = lean_box(0);
if (v_isShared_3729_ == 0)
{
lean_ctor_set(v___x_3728_, 0, v___x_3731_);
v___x_3733_ = v___x_3728_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___x_3731_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
else
{
lean_object* v___x_3735_; uint8_t v___x_3736_; 
v___x_3735_ = l_Lean_Expr_cleanupAnnotations(v_e_3709_);
v___x_3736_ = l_Lean_Expr_isApp(v___x_3735_);
if (v___x_3736_ == 0)
{
lean_dec_ref(v___x_3735_);
lean_del_object(v___x_3728_);
lean_dec_ref(v_e_3709_);
goto v___jp_3722_;
}
else
{
lean_object* v___x_3737_; uint8_t v___x_3738_; 
v___x_3737_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3735_);
lean_dec_ref(v___x_3735_);
v___x_3738_ = l_Lean_Expr_isApp(v___x_3737_);
if (v___x_3738_ == 0)
{
lean_dec_ref(v___x_3737_);
lean_del_object(v___x_3728_);
lean_dec_ref(v_e_3709_);
goto v___jp_3722_;
}
else
{
lean_object* v___x_3739_; uint8_t v___x_3740_; 
v___x_3739_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3737_);
lean_dec_ref(v___x_3737_);
v___x_3740_ = l_Lean_Expr_isApp(v___x_3739_);
if (v___x_3740_ == 0)
{
lean_dec_ref(v___x_3739_);
lean_del_object(v___x_3728_);
lean_dec_ref(v_e_3709_);
goto v___jp_3722_;
}
else
{
lean_object* v___x_3741_; uint8_t v___x_3742_; 
v___x_3741_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3739_);
lean_dec_ref(v___x_3739_);
v___x_3742_ = l_Lean_Expr_isApp(v___x_3741_);
if (v___x_3742_ == 0)
{
lean_dec_ref(v___x_3741_);
lean_del_object(v___x_3728_);
lean_dec_ref(v_e_3709_);
goto v___jp_3722_;
}
else
{
lean_object* v___x_3743_; lean_object* v___x_3744_; uint8_t v___x_3745_; 
v___x_3743_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3741_);
v___x_3744_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__2));
v___x_3745_ = l_Lean_Expr_isConstOf(v___x_3743_, v___x_3744_);
lean_dec_ref(v___x_3743_);
if (v___x_3745_ == 0)
{
lean_dec_ref(v___x_3741_);
lean_del_object(v___x_3728_);
lean_dec_ref(v_e_3709_);
goto v___jp_3722_;
}
else
{
lean_object* v_arg_3746_; lean_object* v___x_3747_; uint8_t v___x_3748_; 
v_arg_3746_ = lean_ctor_get(v___x_3741_, 1);
lean_inc_ref(v_arg_3746_);
lean_dec_ref(v___x_3741_);
v___x_3747_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0));
v___x_3748_ = l_Lean_Expr_isConstOf(v_arg_3746_, v___x_3747_);
if (v___x_3748_ == 0)
{
lean_object* v___x_3749_; uint8_t v___x_3750_; 
v___x_3749_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2));
v___x_3750_ = l_Lean_Expr_isConstOf(v_arg_3746_, v___x_3749_);
lean_dec_ref(v_arg_3746_);
if (v___x_3750_ == 0)
{
lean_object* v___x_3751_; lean_object* v___x_3753_; 
lean_dec_ref(v_e_3709_);
v___x_3751_ = lean_box(0);
if (v_isShared_3729_ == 0)
{
lean_ctor_set(v___x_3728_, 0, v___x_3751_);
v___x_3753_ = v___x_3728_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v___x_3751_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
else
{
lean_object* v___x_3755_; 
lean_del_object(v___x_3728_);
v___x_3755_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(v_e_3709_, v_eqTrue_3710_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_);
return v___x_3755_;
}
}
else
{
lean_object* v___x_3756_; 
lean_dec_ref(v_arg_3746_);
lean_del_object(v___x_3728_);
v___x_3756_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(v_e_3709_, v_eqTrue_3710_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_);
return v___x_3756_;
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
lean_object* v_a_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3765_; 
lean_dec_ref(v_e_3709_);
v_a_3758_ = lean_ctor_get(v___x_3725_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3725_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3760_ = v___x_3725_;
v_isShared_3761_ = v_isSharedCheck_3765_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_a_3758_);
lean_dec(v___x_3725_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3765_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v___x_3763_; 
if (v_isShared_3761_ == 0)
{
v___x_3763_ = v___x_3760_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_a_3758_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
return v___x_3763_;
}
}
}
v___jp_3722_:
{
lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3723_ = lean_box(0);
v___x_3724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3723_);
return v___x_3724_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___boxed(lean_object* v_e_3766_, lean_object* v_eqTrue_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_){
_start:
{
uint8_t v_eqTrue_boxed_3779_; lean_object* v_res_3780_; 
v_eqTrue_boxed_3779_ = lean_unbox(v_eqTrue_3767_);
v_res_3780_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(v_e_3766_, v_eqTrue_boxed_3779_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_);
lean_dec(v_a_3777_);
lean_dec_ref(v_a_3776_);
lean_dec(v_a_3775_);
lean_dec_ref(v_a_3774_);
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
lean_dec(v_a_3771_);
lean_dec_ref(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec(v_a_3768_);
return v_res_3780_;
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
