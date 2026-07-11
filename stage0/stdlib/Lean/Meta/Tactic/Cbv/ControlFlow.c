// Lean compiler output
// Module: Lean.Meta.Tactic.Cbv.ControlFlow
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Sym.Simp.Result import Lean.Meta.Sym.Simp.Rewrite import Lean.Meta.Sym.Simp.ControlFlow import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.InferType import Lean.Meta.Sym.Simp.App import Lean.Meta.SynthInstance import Lean.Meta.WHNF import Lean.Meta.AppBuilder import Init.Sym.Lemmas import Lean.Meta.Tactic.Cbv.TheoremsLookup import Lean.Meta.Tactic.Cbv.Opaque import Lean.Meta.Tactic.Cbv.CbvEvalExt import Lean.Compiler.NoncomputableAttr import Init.CbvSimproc import Lean.Meta.Tactic.Cbv.CbvSimproc
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
lean_object* l_Lean_Meta_Tactic_Cbv_getMatchTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpCond___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_getReducibilityStatusCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_getCbvEvalLemmas___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_noncomputableExt;
uint8_t l_Lean_isNoncomputable(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkRflResult(uint8_t, uint8_t);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getBoundedAppFn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Expr_replaceFn(lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(lean_object*, lean_object*);
uint8_t l_Lean_instBEqReducibilityStatus_beq(uint8_t, uint8_t);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpCond(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_isCbvNoncomputable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_isCbvNoncomputable___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_isCbvNoncomputable(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_isCbvNoncomputable___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isFalse"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__0_value),LEAN_SCALAR_PTR_LITERAL(21, 55, 194, 143, 15, 194, 124, 204)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isTrue"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__2_value),LEAN_SCALAR_PTR_LITERAL(9, 43, 53, 182, 5, 16, 39, 1)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ite_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6_value),LEAN_SCALAR_PTR_LITERAL(168, 126, 169, 138, 86, 190, 160, 178)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ite_false"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value),LEAN_SCALAR_PTR_LITERAL(101, 74, 75, 252, 5, 15, 175, 246)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ite_true_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 140, 45, 159, 71, 73, 13, 89)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "ite_false_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(132, 158, 180, 207, 199, 71, 79, 30)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ite_cond_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 115, 5, 135, 85, 70, 205, 95)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value),LEAN_SCALAR_PTR_LITERAL(217, 231, 214, 152, 207, 100, 121, 38)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6_value),LEAN_SCALAR_PTR_LITERAL(28, 219, 17, 217, 43, 100, 109, 98)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "decidable_of_decidable_of_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(124, 56, 184, 219, 10, 120, 143, 114)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ite_cond_eq_false"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__7_value),LEAN_SCALAR_PTR_LITERAL(4, 35, 104, 204, 105, 138, 171, 217)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ite_cond_eq_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__9_value),LEAN_SCALAR_PTR_LITERAL(217, 214, 153, 207, 191, 74, 245, 103)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Cbv"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(93, 144, 236, 69, 149, 78, 215, 228)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__9_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ControlFlow"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__9_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__9_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__10_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__9_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(153, 75, 2, 199, 142, 91, 93, 201)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__10_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__10_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__11_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__10_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(252, 60, 118, 117, 62, 213, 206, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__11_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__11_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__12_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__11_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value),LEAN_SCALAR_PTR_LITERAL(157, 4, 12, 27, 152, 101, 133, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__12_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__12_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__13_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__12_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(245, 145, 82, 72, 75, 94, 216, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__13_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__13_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__14_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__13_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value),LEAN_SCALAR_PTR_LITERAL(144, 2, 145, 22, 246, 43, 198, 251)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__14_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__14_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__15_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__15_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__15_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__14_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__15_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(124, 100, 175, 78, 162, 84, 105, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__17_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "simpIteCbv"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__17_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__17_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__17_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(74, 233, 198, 147, 223, 175, 34, 106)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__19_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__1_value),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__19_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__19_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__20_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__19_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__20_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__20_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_18____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "dite_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 79, 213, 134, 118, 203, 8, 228)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "dite_false"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__2_value),LEAN_SCALAR_PTR_LITERAL(26, 82, 15, 17, 1, 91, 226, 1)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mpr_prop"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(169, 177, 76, 157, 211, 15, 217, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "dite_true_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(120, 185, 89, 138, 56, 95, 240, 189)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mpr_not"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(121, 56, 250, 51, 9, 123, 141, 181)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__8;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "dite_false_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__9_value),LEAN_SCALAR_PTR_LITERAL(200, 44, 51, 241, 184, 46, 57, 25)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "dite_cond_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(72, 238, 116, 219, 106, 19, 52, 46)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_false"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 21, 178, 198, 97, 164, 246, 137)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 119, 178, 178, 249, 126, 188, 7)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(177, 152, 123, 219, 220, 182, 189, 250)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 218, 189, 96, 14, 237, 238, 210)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "dite_cond_eq_false"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(153, 159, 146, 90, 178, 85, 98, 212)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "dite_cond_eq_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(13, 104, 142, 126, 111, 138, 152, 2)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "simpDIteCbv"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(190, 122, 172, 160, 23, 10, 186, 34)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1_value),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_18____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "decide_isTrue"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__0_value),LEAN_SCALAR_PTR_LITERAL(128, 238, 232, 136, 147, 64, 116, 79)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "decide_isFalse"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__3_value),LEAN_SCALAR_PTR_LITERAL(30, 93, 112, 198, 213, 0, 204, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "decide_isTrue_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 46, 253, 225, 97, 126, 88, 158)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "decide_isFalse_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(210, 108, 78, 146, 25, 88, 128, 244)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "congr_simp"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(16, 96, 65, 173, 152, 155, 4, 222)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "decide_false"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(71, 46, 65, 221, 159, 136, 150, 89)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "decide_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(205, 8, 17, 237, 36, 213, 18, 105)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "decide_prop_eq_false"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(55, 242, 168, 209, 35, 165, 174, 215)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "decide_prop_eq_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(91, 57, 77, 17, 146, 195, 162, 163)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "simpDecideCbv"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(115, 206, 175, 80, 231, 183, 173, 95)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_simpCond___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__13_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(76, 195, 71, 185, 148, 180, 220, 212)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(30, 114, 151, 242, 65, 185, 169, 185)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "simpCbvCond"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value),LEAN_SCALAR_PTR_LITERAL(159, 133, 67, 239, 99, 33, 147, 98)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cbv"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "rewrite"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__0_value),LEAN_SCALAR_PTR_LITERAL(180, 58, 216, 170, 2, 199, 127, 134)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__1_value),LEAN_SCALAR_PTR_LITERAL(174, 58, 109, 183, 100, 138, 243, 210)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "recMatcher:"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\n==>"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "simpDecidableRec"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(80, 52, 244, 154, 141, 147, 125, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rec"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(158, 146, 92, 125, 27, 135, 153, 152)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_19____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_dischargeNone___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "controlFlow"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__0_value),LEAN_SCALAR_PTR_LITERAL(180, 58, 216, 170, 2, 199, 127, 134)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 7, 140, 41, 97, 241, 74, 13)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "match `"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`:"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_isCbvNoncomputable___redArg(lean_object* v_p_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = l_Lean_Meta_Tactic_Cbv_getCbvEvalLemmas___redArg(v_p_1_, v_a_2_);
if (lean_obj_tag(v___x_4_) == 0)
{
lean_object* v_a_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_24_; 
v_a_5_ = lean_ctor_get(v___x_4_, 0);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_4_);
if (v_isSharedCheck_24_ == 0)
{
v___x_7_ = v___x_4_;
v_isShared_8_ = v_isSharedCheck_24_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_a_5_);
lean_dec(v___x_4_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_24_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_9_; 
v___x_9_ = lean_st_ref_get(v_a_2_);
if (lean_obj_tag(v_a_5_) == 0)
{
lean_object* v_env_10_; lean_object* v___x_11_; lean_object* v_toEnvExtension_12_; lean_object* v_asyncMode_13_; uint8_t v___x_14_; lean_object* v___x_15_; lean_object* v___x_17_; 
v_env_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_env_10_);
lean_dec(v___x_9_);
v___x_11_ = l_Lean_noncomputableExt;
v_toEnvExtension_12_ = lean_ctor_get(v___x_11_, 0);
v_asyncMode_13_ = lean_ctor_get(v_toEnvExtension_12_, 2);
v___x_14_ = l_Lean_isNoncomputable(v_env_10_, v_p_1_, v_asyncMode_13_);
v___x_15_ = lean_box(v___x_14_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 0, v___x_15_);
v___x_17_ = v___x_7_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
else
{
uint8_t v___x_19_; lean_object* v___x_20_; lean_object* v___x_22_; 
lean_dec_ref_known(v_a_5_, 1);
lean_dec(v___x_9_);
lean_dec(v_p_1_);
v___x_19_ = 0;
v___x_20_ = lean_box(v___x_19_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 0, v___x_20_);
v___x_22_ = v___x_7_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v___x_20_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
}
}
else
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_dec(v_p_1_);
v_a_25_ = lean_ctor_get(v___x_4_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_4_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_4_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_4_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_isCbvNoncomputable___redArg___boxed(lean_object* v_p_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_isCbvNoncomputable___redArg(v_p_33_, v_a_34_);
lean_dec(v_a_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_isCbvNoncomputable(lean_object* v_p_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_isCbvNoncomputable___redArg(v_p_37_, v_a_39_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_isCbvNoncomputable___boxed(lean_object* v_p_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_isCbvNoncomputable(v_p_42_, v_a_43_, v_a_44_);
lean_dec(v_a_44_);
lean_dec_ref(v_a_43_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0___redArg(lean_object* v_as_47_, size_t v_i_48_, size_t v_stop_49_, lean_object* v___y_50_){
_start:
{
uint8_t v___x_52_; 
v___x_52_ = lean_usize_dec_eq(v_i_48_, v_stop_49_);
if (v___x_52_ == 0)
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_array_uget_borrowed(v_as_47_, v_i_48_);
lean_inc(v___x_53_);
v___x_54_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_isCbvNoncomputable___redArg(v___x_53_, v___y_50_);
if (lean_obj_tag(v___x_54_) == 0)
{
lean_object* v_a_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_66_; 
v_a_55_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_66_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_66_ == 0)
{
v___x_57_ = v___x_54_;
v_isShared_58_ = v_isSharedCheck_66_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_a_55_);
lean_dec(v___x_54_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_66_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
uint8_t v___x_59_; 
v___x_59_ = lean_unbox(v_a_55_);
if (v___x_59_ == 0)
{
size_t v___x_60_; size_t v___x_61_; 
lean_del_object(v___x_57_);
lean_dec(v_a_55_);
v___x_60_ = ((size_t)1ULL);
v___x_61_ = lean_usize_add(v_i_48_, v___x_60_);
v_i_48_ = v___x_61_;
goto _start;
}
else
{
lean_object* v___x_64_; 
if (v_isShared_58_ == 0)
{
v___x_64_ = v___x_57_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_a_55_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
}
}
else
{
return v___x_54_;
}
}
else
{
uint8_t v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = 0;
v___x_68_ = lean_box(v___x_67_);
v___x_69_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0___redArg___boxed(lean_object* v_as_70_, lean_object* v_i_71_, lean_object* v_stop_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
size_t v_i_boxed_75_; size_t v_stop_boxed_76_; lean_object* v_res_77_; 
v_i_boxed_75_ = lean_unbox_usize(v_i_71_);
lean_dec(v_i_71_);
v_stop_boxed_76_ = lean_unbox_usize(v_stop_72_);
lean_dec(v_stop_72_);
v_res_77_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0___redArg(v_as_70_, v_i_boxed_75_, v_stop_boxed_76_, v___y_73_);
lean_dec(v___y_73_);
lean_dec_ref(v_as_70_);
return v_res_77_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__2(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_81_ = lean_box(0);
v___x_82_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__1));
v___x_83_ = l_Lean_mkConst(v___x_82_, v___x_81_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance(lean_object* v_p_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_92_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__2);
v___x_93_ = l_Lean_Expr_app___override(v___x_92_, v_p_84_);
v___x_94_ = lean_box(0);
v___x_95_ = l_Lean_Meta_trySynthInstance(v___x_93_, v___x_94_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_153_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_153_ == 0)
{
v___x_98_ = v___x_95_;
v_isShared_99_ = v_isSharedCheck_153_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_95_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_153_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
if (lean_obj_tag(v_a_96_) == 1)
{
lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_149_; 
lean_del_object(v___x_98_);
v_a_100_ = lean_ctor_get(v_a_96_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v_a_96_);
if (v_isSharedCheck_149_ == 0)
{
v___x_102_ = v_a_96_;
v_isShared_103_ = v_isSharedCheck_149_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v_a_96_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_149_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
lean_inc(v_a_100_);
v___x_125_ = l_Lean_Expr_getUsedConstants(v_a_100_);
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_array_get_size(v___x_125_);
v___x_128_ = lean_nat_dec_lt(v___x_126_, v___x_127_);
if (v___x_128_ == 0)
{
lean_dec_ref(v___x_125_);
goto v___jp_104_;
}
else
{
if (v___x_128_ == 0)
{
lean_dec_ref(v___x_125_);
goto v___jp_104_;
}
else
{
size_t v___x_129_; size_t v___x_130_; lean_object* v___x_131_; 
v___x_129_ = ((size_t)0ULL);
v___x_130_ = lean_usize_of_nat(v___x_127_);
v___x_131_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0___redArg(v___x_125_, v___x_129_, v___x_130_, v_a_90_);
lean_dec_ref(v___x_125_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_140_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_140_ == 0)
{
v___x_134_ = v___x_131_;
v_isShared_135_ = v_isSharedCheck_140_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_131_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_140_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
uint8_t v___x_136_; 
v___x_136_ = lean_unbox(v_a_132_);
lean_dec(v_a_132_);
if (v___x_136_ == 0)
{
lean_del_object(v___x_134_);
goto v___jp_104_;
}
else
{
lean_object* v___x_138_; 
lean_del_object(v___x_102_);
lean_dec(v_a_100_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 0, v___x_94_);
v___x_138_ = v___x_134_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_94_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
else
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_148_; 
lean_del_object(v___x_102_);
lean_dec(v_a_100_);
v_a_141_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_148_ == 0)
{
v___x_143_ = v___x_131_;
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_131_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_a_141_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
}
v___jp_104_:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_Meta_Sym_shareCommon(v_a_100_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_116_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_116_ == 0)
{
v___x_108_ = v___x_105_;
v_isShared_109_ = v_isSharedCheck_116_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_105_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_116_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 0, v_a_106_);
v___x_111_ = v___x_102_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_a_106_);
v___x_111_ = v_reuseFailAlloc_115_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
lean_object* v___x_113_; 
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 0, v___x_111_);
v___x_113_ = v___x_108_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
else
{
lean_object* v_a_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_124_; 
lean_del_object(v___x_102_);
v_a_117_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_124_ == 0)
{
v___x_119_ = v___x_105_;
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_a_117_);
lean_dec(v___x_105_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_122_; 
if (v_isShared_120_ == 0)
{
v___x_122_ = v___x_119_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_a_117_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
}
}
else
{
lean_object* v___x_151_; 
lean_dec(v_a_96_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_94_);
v___x_151_ = v___x_98_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v___x_94_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
v_a_154_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_95_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_95_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___boxed(lean_object* v_p_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance(v_p_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_);
lean_dec(v_a_168_);
lean_dec_ref(v_a_167_);
lean_dec(v_a_166_);
lean_dec_ref(v_a_165_);
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0(lean_object* v_as_171_, size_t v_i_172_, size_t v_stop_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0___redArg(v_as_171_, v_i_172_, v_stop_173_, v___y_179_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0___boxed(lean_object* v_as_182_, lean_object* v_i_183_, lean_object* v_stop_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
size_t v_i_boxed_192_; size_t v_stop_boxed_193_; lean_object* v_res_194_; 
v_i_boxed_192_ = lean_unbox_usize(v_i_183_);
lean_dec(v_i_183_);
v_stop_boxed_193_ = lean_unbox_usize(v_stop_184_);
lean_dec(v_stop_184_);
v_res_194_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0(v_as_182_, v_i_boxed_192_, v_stop_boxed_193_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec_ref(v_as_182_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable(lean_object* v_f_215_, lean_object* v_00_u03b1_216_, lean_object* v_c_217_, lean_object* v_inst_218_, lean_object* v_a_219_, lean_object* v_b_220_, lean_object* v_instToMatch_221_, lean_object* v_fallback_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_instToMatch_221_, v_a_229_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_268_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_268_ == 0)
{
v___x_236_ = v___x_233_;
v_isShared_237_ = v_isSharedCheck_268_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_233_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_268_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_238_ = l_Lean_Expr_cleanupAnnotations(v_a_234_);
v___x_239_ = l_Lean_Expr_isApp(v___x_238_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; 
lean_dec_ref(v___x_238_);
lean_del_object(v___x_236_);
lean_dec_ref(v_b_220_);
lean_dec_ref(v_a_219_);
lean_dec_ref(v_inst_218_);
lean_dec_ref(v_c_217_);
lean_dec_ref(v_00_u03b1_216_);
lean_inc(v_a_231_);
lean_inc_ref(v_a_230_);
lean_inc(v_a_229_);
lean_inc_ref(v_a_228_);
lean_inc(v_a_227_);
lean_inc_ref(v_a_226_);
lean_inc(v_a_225_);
lean_inc_ref(v_a_224_);
lean_inc(v_a_223_);
v___x_240_ = lean_apply_10(v_fallback_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, lean_box(0));
return v___x_240_;
}
else
{
lean_object* v_arg_241_; lean_object* v___x_242_; uint8_t v___x_243_; 
v_arg_241_ = lean_ctor_get(v___x_238_, 1);
lean_inc_ref(v_arg_241_);
v___x_242_ = l_Lean_Expr_appFnCleanup___redArg(v___x_238_);
v___x_243_ = l_Lean_Expr_isApp(v___x_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; 
lean_dec_ref(v___x_242_);
lean_dec_ref(v_arg_241_);
lean_del_object(v___x_236_);
lean_dec_ref(v_b_220_);
lean_dec_ref(v_a_219_);
lean_dec_ref(v_inst_218_);
lean_dec_ref(v_c_217_);
lean_dec_ref(v_00_u03b1_216_);
lean_inc(v_a_231_);
lean_inc_ref(v_a_230_);
lean_inc(v_a_229_);
lean_inc_ref(v_a_228_);
lean_inc(v_a_227_);
lean_inc_ref(v_a_226_);
lean_inc(v_a_225_);
lean_inc_ref(v_a_224_);
lean_inc(v_a_223_);
v___x_244_ = lean_apply_10(v_fallback_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, lean_box(0));
return v___x_244_;
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_245_ = l_Lean_Expr_appFnCleanup___redArg(v___x_242_);
v___x_246_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_247_ = l_Lean_Expr_isConstOf(v___x_245_, v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_248_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3));
v___x_249_ = l_Lean_Expr_isConstOf(v___x_245_, v___x_248_);
lean_dec_ref(v___x_245_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; 
lean_dec_ref(v_arg_241_);
lean_del_object(v___x_236_);
lean_dec_ref(v_b_220_);
lean_dec_ref(v_a_219_);
lean_dec_ref(v_inst_218_);
lean_dec_ref(v_c_217_);
lean_dec_ref(v_00_u03b1_216_);
lean_inc(v_a_231_);
lean_inc_ref(v_a_230_);
lean_inc(v_a_229_);
lean_inc_ref(v_a_228_);
lean_inc(v_a_227_);
lean_inc_ref(v_a_226_);
lean_inc(v_a_225_);
lean_inc_ref(v_a_224_);
lean_inc(v_a_223_);
v___x_250_ = lean_apply_10(v_fallback_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, lean_box(0));
return v___x_250_;
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_257_; 
lean_dec_ref(v_fallback_222_);
v___x_251_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7));
v___x_252_ = l_Lean_Expr_constLevels_x21(v_f_215_);
v___x_253_ = l_Lean_mkConst(v___x_251_, v___x_252_);
lean_inc_ref(v_a_219_);
v___x_254_ = l_Lean_mkApp6(v___x_253_, v_00_u03b1_216_, v_c_217_, v_inst_218_, v_a_219_, v_b_220_, v_arg_241_);
v___x_255_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_255_, 0, v_a_219_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
lean_ctor_set_uint8(v___x_255_, sizeof(void*)*2, v___x_247_);
lean_ctor_set_uint8(v___x_255_, sizeof(void*)*2 + 1, v___x_247_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_255_);
v___x_257_ = v___x_236_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_255_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
else
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_266_; 
lean_dec_ref(v___x_245_);
lean_dec_ref(v_fallback_222_);
v___x_259_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__9));
v___x_260_ = l_Lean_Expr_constLevels_x21(v_f_215_);
v___x_261_ = l_Lean_mkConst(v___x_259_, v___x_260_);
lean_inc_ref(v_b_220_);
v___x_262_ = l_Lean_mkApp6(v___x_261_, v_00_u03b1_216_, v_c_217_, v_inst_218_, v_a_219_, v_b_220_, v_arg_241_);
v___x_263_ = 0;
v___x_264_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_264_, 0, v_b_220_);
lean_ctor_set(v___x_264_, 1, v___x_262_);
lean_ctor_set_uint8(v___x_264_, sizeof(void*)*2, v___x_263_);
lean_ctor_set_uint8(v___x_264_, sizeof(void*)*2 + 1, v___x_263_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_264_);
v___x_266_ = v___x_236_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec_ref(v_fallback_222_);
lean_dec_ref(v_b_220_);
lean_dec_ref(v_a_219_);
lean_dec_ref(v_inst_218_);
lean_dec_ref(v_c_217_);
lean_dec_ref(v_00_u03b1_216_);
v_a_269_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_233_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_233_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___boxed(lean_object** _args){
lean_object* v_f_277_ = _args[0];
lean_object* v_00_u03b1_278_ = _args[1];
lean_object* v_c_279_ = _args[2];
lean_object* v_inst_280_ = _args[3];
lean_object* v_a_281_ = _args[4];
lean_object* v_b_282_ = _args[5];
lean_object* v_instToMatch_283_ = _args[6];
lean_object* v_fallback_284_ = _args[7];
lean_object* v_a_285_ = _args[8];
lean_object* v_a_286_ = _args[9];
lean_object* v_a_287_ = _args[10];
lean_object* v_a_288_ = _args[11];
lean_object* v_a_289_ = _args[12];
lean_object* v_a_290_ = _args[13];
lean_object* v_a_291_ = _args[14];
lean_object* v_a_292_ = _args[15];
lean_object* v_a_293_ = _args[16];
lean_object* v_a_294_ = _args[17];
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable(v_f_277_, v_00_u03b1_278_, v_c_279_, v_inst_280_, v_a_281_, v_b_282_, v_instToMatch_283_, v_fallback_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
lean_dec(v_a_293_);
lean_dec_ref(v_a_292_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
lean_dec(v_a_285_);
lean_dec_ref(v_f_277_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(lean_object* v_f_306_, lean_object* v_00_u03b1_307_, lean_object* v_c_308_, lean_object* v_inst_309_, lean_object* v_a_310_, lean_object* v_b_311_, lean_object* v_c_x27_312_, lean_object* v_h_313_, lean_object* v_inst_x27_314_, lean_object* v_fallback_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_inst_x27_314_, v_a_322_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_361_; 
v_a_327_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_361_ == 0)
{
v___x_329_ = v___x_326_;
v_isShared_330_ = v_isSharedCheck_361_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_326_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_361_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_331_ = l_Lean_Expr_cleanupAnnotations(v_a_327_);
v___x_332_ = l_Lean_Expr_isApp(v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; 
lean_dec_ref(v___x_331_);
lean_del_object(v___x_329_);
lean_dec_ref(v_h_313_);
lean_dec_ref(v_c_x27_312_);
lean_dec_ref(v_b_311_);
lean_dec_ref(v_a_310_);
lean_dec_ref(v_inst_309_);
lean_dec_ref(v_c_308_);
lean_dec_ref(v_00_u03b1_307_);
lean_inc(v_a_324_);
lean_inc_ref(v_a_323_);
lean_inc(v_a_322_);
lean_inc_ref(v_a_321_);
lean_inc(v_a_320_);
lean_inc_ref(v_a_319_);
lean_inc(v_a_318_);
lean_inc_ref(v_a_317_);
lean_inc(v_a_316_);
v___x_333_ = lean_apply_10(v_fallback_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, lean_box(0));
return v___x_333_;
}
else
{
lean_object* v_arg_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v_arg_334_ = lean_ctor_get(v___x_331_, 1);
lean_inc_ref(v_arg_334_);
v___x_335_ = l_Lean_Expr_appFnCleanup___redArg(v___x_331_);
v___x_336_ = l_Lean_Expr_isApp(v___x_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; 
lean_dec_ref(v___x_335_);
lean_dec_ref(v_arg_334_);
lean_del_object(v___x_329_);
lean_dec_ref(v_h_313_);
lean_dec_ref(v_c_x27_312_);
lean_dec_ref(v_b_311_);
lean_dec_ref(v_a_310_);
lean_dec_ref(v_inst_309_);
lean_dec_ref(v_c_308_);
lean_dec_ref(v_00_u03b1_307_);
lean_inc(v_a_324_);
lean_inc_ref(v_a_323_);
lean_inc(v_a_322_);
lean_inc_ref(v_a_321_);
lean_inc(v_a_320_);
lean_inc_ref(v_a_319_);
lean_inc(v_a_318_);
lean_inc_ref(v_a_317_);
lean_inc(v_a_316_);
v___x_337_ = lean_apply_10(v_fallback_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, lean_box(0));
return v___x_337_;
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_338_ = l_Lean_Expr_appFnCleanup___redArg(v___x_335_);
v___x_339_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_340_ = l_Lean_Expr_isConstOf(v___x_338_, v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3));
v___x_342_ = l_Lean_Expr_isConstOf(v___x_338_, v___x_341_);
lean_dec_ref(v___x_338_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; 
lean_dec_ref(v_arg_334_);
lean_del_object(v___x_329_);
lean_dec_ref(v_h_313_);
lean_dec_ref(v_c_x27_312_);
lean_dec_ref(v_b_311_);
lean_dec_ref(v_a_310_);
lean_dec_ref(v_inst_309_);
lean_dec_ref(v_c_308_);
lean_dec_ref(v_00_u03b1_307_);
lean_inc(v_a_324_);
lean_inc_ref(v_a_323_);
lean_inc(v_a_322_);
lean_inc_ref(v_a_321_);
lean_inc(v_a_320_);
lean_inc_ref(v_a_319_);
lean_inc(v_a_318_);
lean_inc_ref(v_a_317_);
lean_inc(v_a_316_);
v___x_343_ = lean_apply_10(v_fallback_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, lean_box(0));
return v___x_343_;
}
else
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_350_; 
lean_dec_ref(v_fallback_315_);
v___x_344_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__1));
v___x_345_ = l_Lean_Expr_constLevels_x21(v_f_306_);
v___x_346_ = l_Lean_mkConst(v___x_344_, v___x_345_);
lean_inc_ref(v_a_310_);
v___x_347_ = l_Lean_mkApp8(v___x_346_, v_00_u03b1_307_, v_c_308_, v_inst_309_, v_a_310_, v_b_311_, v_c_x27_312_, v_h_313_, v_arg_334_);
v___x_348_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_348_, 0, v_a_310_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
lean_ctor_set_uint8(v___x_348_, sizeof(void*)*2, v___x_340_);
lean_ctor_set_uint8(v___x_348_, sizeof(void*)*2 + 1, v___x_340_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v___x_348_);
v___x_350_ = v___x_329_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
else
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; lean_object* v___x_357_; lean_object* v___x_359_; 
lean_dec_ref(v___x_338_);
lean_dec_ref(v_fallback_315_);
v___x_352_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__3));
v___x_353_ = l_Lean_Expr_constLevels_x21(v_f_306_);
v___x_354_ = l_Lean_mkConst(v___x_352_, v___x_353_);
lean_inc_ref(v_b_311_);
v___x_355_ = l_Lean_mkApp8(v___x_354_, v_00_u03b1_307_, v_c_308_, v_inst_309_, v_a_310_, v_b_311_, v_c_x27_312_, v_h_313_, v_arg_334_);
v___x_356_ = 0;
v___x_357_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_357_, 0, v_b_311_);
lean_ctor_set(v___x_357_, 1, v___x_355_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*2, v___x_356_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*2 + 1, v___x_356_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v___x_357_);
v___x_359_ = v___x_329_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_357_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
}
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_dec_ref(v_fallback_315_);
lean_dec_ref(v_h_313_);
lean_dec_ref(v_c_x27_312_);
lean_dec_ref(v_b_311_);
lean_dec_ref(v_a_310_);
lean_dec_ref(v_inst_309_);
lean_dec_ref(v_c_308_);
lean_dec_ref(v_00_u03b1_307_);
v_a_362_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_326_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_326_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___boxed(lean_object** _args){
lean_object* v_f_370_ = _args[0];
lean_object* v_00_u03b1_371_ = _args[1];
lean_object* v_c_372_ = _args[2];
lean_object* v_inst_373_ = _args[3];
lean_object* v_a_374_ = _args[4];
lean_object* v_b_375_ = _args[5];
lean_object* v_c_x27_376_ = _args[6];
lean_object* v_h_377_ = _args[7];
lean_object* v_inst_x27_378_ = _args[8];
lean_object* v_fallback_379_ = _args[9];
lean_object* v_a_380_ = _args[10];
lean_object* v_a_381_ = _args[11];
lean_object* v_a_382_ = _args[12];
lean_object* v_a_383_ = _args[13];
lean_object* v_a_384_ = _args[14];
lean_object* v_a_385_ = _args[15];
lean_object* v_a_386_ = _args[16];
lean_object* v_a_387_ = _args[17];
lean_object* v_a_388_ = _args[18];
lean_object* v_a_389_ = _args[19];
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(v_f_370_, v_00_u03b1_371_, v_c_372_, v_inst_373_, v_a_374_, v_b_375_, v_c_x27_376_, v_h_377_, v_inst_x27_378_, v_fallback_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_a_380_);
lean_dec_ref(v_f_370_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(lean_object* v_f_391_, lean_object* v_00_u03b1_392_, lean_object* v_c_393_, lean_object* v_inst_394_, lean_object* v_a_395_, lean_object* v_b_396_, lean_object* v_fallback_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v___x_408_; 
lean_inc(v_a_406_);
lean_inc_ref(v_a_405_);
lean_inc(v_a_404_);
lean_inc_ref(v_a_403_);
lean_inc(v_a_402_);
lean_inc_ref(v_a_401_);
lean_inc(v_a_400_);
lean_inc_ref(v_a_399_);
lean_inc(v_a_398_);
lean_inc_ref(v_inst_394_);
v___x_408_ = lean_sym_simp(v_inst_394_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_a_409_);
lean_dec_ref_known(v___x_408_, 1);
if (lean_obj_tag(v_a_409_) == 0)
{
uint8_t v_contextDependent_410_; lean_object* v___x_411_; 
v_contextDependent_410_ = lean_ctor_get_uint8(v_a_409_, 1);
lean_dec_ref_known(v_a_409_, 0);
lean_inc_ref(v_inst_394_);
v___x_411_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable(v_f_391_, v_00_u03b1_392_, v_c_393_, v_inst_394_, v_a_395_, v_b_396_, v_inst_394_, v_fallback_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; uint8_t v___y_414_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
if (v_contextDependent_410_ == 0)
{
lean_dec(v_a_412_);
return v___x_411_;
}
else
{
if (lean_obj_tag(v_a_412_) == 0)
{
uint8_t v_contextDependent_424_; uint8_t v___x_425_; 
v_contextDependent_424_ = lean_ctor_get_uint8(v_a_412_, 1);
v___x_425_ = lean_bool_not(v_contextDependent_424_);
v___y_414_ = v___x_425_;
goto v___jp_413_;
}
else
{
uint8_t v_contextDependent_426_; uint8_t v___x_427_; 
v_contextDependent_426_ = lean_ctor_get_uint8(v_a_412_, sizeof(void*)*2 + 1);
v___x_427_ = lean_bool_not(v_contextDependent_426_);
v___y_414_ = v___x_427_;
goto v___jp_413_;
}
}
v___jp_413_:
{
if (v___y_414_ == 0)
{
lean_dec(v_a_412_);
return v___x_411_;
}
else
{
lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_422_; 
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_422_ == 0)
{
lean_object* v_unused_423_; 
v_unused_423_ = lean_ctor_get(v___x_411_, 0);
lean_dec(v_unused_423_);
v___x_416_ = v___x_411_;
v_isShared_417_ = v_isSharedCheck_422_;
goto v_resetjp_415_;
}
else
{
lean_dec(v___x_411_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_422_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_418_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_412_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_418_);
v___x_420_ = v___x_416_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
else
{
return v___x_411_;
}
}
else
{
lean_object* v_e_x27_428_; uint8_t v_contextDependent_429_; lean_object* v___x_430_; 
v_e_x27_428_ = lean_ctor_get(v_a_409_, 0);
lean_inc_ref(v_e_x27_428_);
v_contextDependent_429_ = lean_ctor_get_uint8(v_a_409_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_409_, 2);
v___x_430_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable(v_f_391_, v_00_u03b1_392_, v_c_393_, v_inst_394_, v_a_395_, v_b_396_, v_e_x27_428_, v_fallback_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; uint8_t v___y_433_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_a_431_);
if (v_contextDependent_429_ == 0)
{
lean_dec(v_a_431_);
return v___x_430_;
}
else
{
if (lean_obj_tag(v_a_431_) == 0)
{
uint8_t v_contextDependent_443_; uint8_t v___x_444_; 
v_contextDependent_443_ = lean_ctor_get_uint8(v_a_431_, 1);
v___x_444_ = lean_bool_not(v_contextDependent_443_);
v___y_433_ = v___x_444_;
goto v___jp_432_;
}
else
{
uint8_t v_contextDependent_445_; uint8_t v___x_446_; 
v_contextDependent_445_ = lean_ctor_get_uint8(v_a_431_, sizeof(void*)*2 + 1);
v___x_446_ = lean_bool_not(v_contextDependent_445_);
v___y_433_ = v___x_446_;
goto v___jp_432_;
}
}
v___jp_432_:
{
if (v___y_433_ == 0)
{
lean_dec(v_a_431_);
return v___x_430_;
}
else
{
lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_441_; 
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_441_ == 0)
{
lean_object* v_unused_442_; 
v_unused_442_ = lean_ctor_get(v___x_430_, 0);
lean_dec(v_unused_442_);
v___x_435_ = v___x_430_;
v_isShared_436_ = v_isSharedCheck_441_;
goto v_resetjp_434_;
}
else
{
lean_dec(v___x_430_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_441_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_437_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_431_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v___x_437_);
v___x_439_ = v___x_435_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
}
else
{
return v___x_430_;
}
}
}
else
{
lean_dec_ref(v_fallback_397_);
lean_dec_ref(v_b_396_);
lean_dec_ref(v_a_395_);
lean_dec_ref(v_inst_394_);
lean_dec_ref(v_c_393_);
lean_dec_ref(v_00_u03b1_392_);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___boxed(lean_object** _args){
lean_object* v_f_447_ = _args[0];
lean_object* v_00_u03b1_448_ = _args[1];
lean_object* v_c_449_ = _args[2];
lean_object* v_inst_450_ = _args[3];
lean_object* v_a_451_ = _args[4];
lean_object* v_b_452_ = _args[5];
lean_object* v_fallback_453_ = _args[6];
lean_object* v_a_454_ = _args[7];
lean_object* v_a_455_ = _args[8];
lean_object* v_a_456_ = _args[9];
lean_object* v_a_457_ = _args[10];
lean_object* v_a_458_ = _args[11];
lean_object* v_a_459_ = _args[12];
lean_object* v_a_460_ = _args[13];
lean_object* v_a_461_ = _args[14];
lean_object* v_a_462_ = _args[15];
lean_object* v_a_463_ = _args[16];
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(v_f_447_, v_00_u03b1_448_, v_c_449_, v_inst_450_, v_a_451_, v_b_452_, v_fallback_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
lean_dec(v_a_462_);
lean_dec_ref(v_a_461_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
lean_dec(v_a_454_);
lean_dec_ref(v_f_447_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr(lean_object* v_f_465_, lean_object* v_00_u03b1_466_, lean_object* v_c_467_, lean_object* v_inst_468_, lean_object* v_a_469_, lean_object* v_b_470_, lean_object* v_c_x27_471_, lean_object* v_h_472_, lean_object* v_inst_x27_473_, lean_object* v_fallback_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v___x_485_; 
lean_inc(v_a_483_);
lean_inc_ref(v_a_482_);
lean_inc(v_a_481_);
lean_inc_ref(v_a_480_);
lean_inc(v_a_479_);
lean_inc_ref(v_a_478_);
lean_inc(v_a_477_);
lean_inc_ref(v_a_476_);
lean_inc(v_a_475_);
lean_inc_ref(v_inst_x27_473_);
v___x_485_ = lean_sym_simp(v_inst_x27_473_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
lean_dec_ref_known(v___x_485_, 1);
if (lean_obj_tag(v_a_486_) == 0)
{
uint8_t v_contextDependent_487_; lean_object* v___x_488_; 
v_contextDependent_487_ = lean_ctor_get_uint8(v_a_486_, 1);
lean_dec_ref_known(v_a_486_, 0);
v___x_488_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(v_f_465_, v_00_u03b1_466_, v_c_467_, v_inst_468_, v_a_469_, v_b_470_, v_c_x27_471_, v_h_472_, v_inst_x27_473_, v_fallback_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; uint8_t v___y_491_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
if (v_contextDependent_487_ == 0)
{
lean_dec(v_a_489_);
return v___x_488_;
}
else
{
if (lean_obj_tag(v_a_489_) == 0)
{
uint8_t v_contextDependent_501_; uint8_t v___x_502_; 
v_contextDependent_501_ = lean_ctor_get_uint8(v_a_489_, 1);
v___x_502_ = lean_bool_not(v_contextDependent_501_);
v___y_491_ = v___x_502_;
goto v___jp_490_;
}
else
{
uint8_t v_contextDependent_503_; uint8_t v___x_504_; 
v_contextDependent_503_ = lean_ctor_get_uint8(v_a_489_, sizeof(void*)*2 + 1);
v___x_504_ = lean_bool_not(v_contextDependent_503_);
v___y_491_ = v___x_504_;
goto v___jp_490_;
}
}
v___jp_490_:
{
if (v___y_491_ == 0)
{
lean_dec(v_a_489_);
return v___x_488_;
}
else
{
lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_499_; 
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_499_ == 0)
{
lean_object* v_unused_500_; 
v_unused_500_ = lean_ctor_get(v___x_488_, 0);
lean_dec(v_unused_500_);
v___x_493_ = v___x_488_;
v_isShared_494_ = v_isSharedCheck_499_;
goto v_resetjp_492_;
}
else
{
lean_dec(v___x_488_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_499_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_497_; 
v___x_495_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_489_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_495_);
v___x_497_ = v___x_493_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
}
else
{
return v___x_488_;
}
}
else
{
lean_object* v_e_x27_505_; uint8_t v_contextDependent_506_; lean_object* v___x_507_; 
lean_dec_ref(v_inst_x27_473_);
v_e_x27_505_ = lean_ctor_get(v_a_486_, 0);
lean_inc_ref(v_e_x27_505_);
v_contextDependent_506_ = lean_ctor_get_uint8(v_a_486_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_486_, 2);
v___x_507_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(v_f_465_, v_00_u03b1_466_, v_c_467_, v_inst_468_, v_a_469_, v_b_470_, v_c_x27_471_, v_h_472_, v_e_x27_505_, v_fallback_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; uint8_t v___y_510_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
if (v_contextDependent_506_ == 0)
{
lean_dec(v_a_508_);
return v___x_507_;
}
else
{
if (lean_obj_tag(v_a_508_) == 0)
{
uint8_t v_contextDependent_520_; uint8_t v___x_521_; 
v_contextDependent_520_ = lean_ctor_get_uint8(v_a_508_, 1);
v___x_521_ = lean_bool_not(v_contextDependent_520_);
v___y_510_ = v___x_521_;
goto v___jp_509_;
}
else
{
uint8_t v_contextDependent_522_; uint8_t v___x_523_; 
v_contextDependent_522_ = lean_ctor_get_uint8(v_a_508_, sizeof(void*)*2 + 1);
v___x_523_ = lean_bool_not(v_contextDependent_522_);
v___y_510_ = v___x_523_;
goto v___jp_509_;
}
}
v___jp_509_:
{
if (v___y_510_ == 0)
{
lean_dec(v_a_508_);
return v___x_507_;
}
else
{
lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_518_; 
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_518_ == 0)
{
lean_object* v_unused_519_; 
v_unused_519_ = lean_ctor_get(v___x_507_, 0);
lean_dec(v_unused_519_);
v___x_512_ = v___x_507_;
v_isShared_513_ = v_isSharedCheck_518_;
goto v_resetjp_511_;
}
else
{
lean_dec(v___x_507_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_518_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_514_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_508_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_514_);
v___x_516_ = v___x_512_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
else
{
return v___x_507_;
}
}
}
else
{
lean_dec_ref(v_fallback_474_);
lean_dec_ref(v_inst_x27_473_);
lean_dec_ref(v_h_472_);
lean_dec_ref(v_c_x27_471_);
lean_dec_ref(v_b_470_);
lean_dec_ref(v_a_469_);
lean_dec_ref(v_inst_468_);
lean_dec_ref(v_c_467_);
lean_dec_ref(v_00_u03b1_466_);
return v___x_485_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___boxed(lean_object** _args){
lean_object* v_f_524_ = _args[0];
lean_object* v_00_u03b1_525_ = _args[1];
lean_object* v_c_526_ = _args[2];
lean_object* v_inst_527_ = _args[3];
lean_object* v_a_528_ = _args[4];
lean_object* v_b_529_ = _args[5];
lean_object* v_c_x27_530_ = _args[6];
lean_object* v_h_531_ = _args[7];
lean_object* v_inst_x27_532_ = _args[8];
lean_object* v_fallback_533_ = _args[9];
lean_object* v_a_534_ = _args[10];
lean_object* v_a_535_ = _args[11];
lean_object* v_a_536_ = _args[12];
lean_object* v_a_537_ = _args[13];
lean_object* v_a_538_ = _args[14];
lean_object* v_a_539_ = _args[15];
lean_object* v_a_540_ = _args[16];
lean_object* v_a_541_ = _args[17];
lean_object* v_a_542_ = _args[18];
lean_object* v_a_543_ = _args[19];
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr(v_f_524_, v_00_u03b1_525_, v_c_526_, v_inst_527_, v_a_528_, v_b_529_, v_c_x27_530_, v_h_531_, v_inst_x27_532_, v_fallback_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec(v_a_534_);
lean_dec_ref(v_f_524_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0(lean_object* v___x_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_545_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed(lean_object* v___x_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0(v___x_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(lean_object* v_f_569_, lean_object* v_a_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v___y_579_; lean_object* v___x_582_; uint8_t v_debug_583_; 
v___x_582_ = lean_st_ref_get(v___y_572_);
v_debug_583_ = lean_ctor_get_uint8(v___x_582_, sizeof(void*)*11);
lean_dec(v___x_582_);
if (v_debug_583_ == 0)
{
v___y_579_ = v___y_572_;
goto v___jp_578_;
}
else
{
lean_object* v___x_584_; 
lean_inc_ref(v_f_569_);
v___x_584_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_569_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v___x_585_; 
lean_dec_ref_known(v___x_584_, 1);
lean_inc_ref(v_a_570_);
v___x_585_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_dec_ref_known(v___x_585_, 1);
v___y_579_ = v___y_572_;
goto v___jp_578_;
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_dec_ref(v_a_570_);
lean_dec_ref(v_f_569_);
v_a_586_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_585_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_dec_ref(v_a_570_);
lean_dec_ref(v_f_569_);
v_a_594_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_584_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_584_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
v___jp_578_:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = l_Lean_Expr_app___override(v_f_569_, v_a_570_);
v___x_581_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_580_, v___y_579_);
return v___x_581_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg___boxed(lean_object* v_f_602_, lean_object* v_a_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(v_f_602_, v_a_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1(lean_object* v_f_612_, lean_object* v_a_u2081_613_, lean_object* v_a_u2082_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(v_f_612_, v_a_u2081_613_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v___x_627_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_a_626_);
lean_dec_ref_known(v___x_625_, 1);
v___x_627_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(v_a_626_, v_a_u2082_614_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
return v___x_627_;
}
else
{
lean_dec_ref(v_a_u2082_614_);
return v___x_625_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___boxed(lean_object* v_f_628_, lean_object* v_a_u2081_629_, lean_object* v_a_u2082_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1(v_f_628_, v_a_u2081_629_, v_a_u2082_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(lean_object* v_f_642_, lean_object* v_a_u2081_643_, lean_object* v_a_u2082_644_, lean_object* v_a_u2083_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1(v_f_642_, v_a_u2081_643_, v_a_u2082_644_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v___x_658_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_a_657_);
lean_dec_ref_known(v___x_656_, 1);
v___x_658_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(v_a_657_, v_a_u2083_645_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
return v___x_658_;
}
else
{
lean_dec_ref(v_a_u2083_645_);
return v___x_656_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___boxed(lean_object* v_f_659_, lean_object* v_a_u2081_660_, lean_object* v_a_u2082_661_, lean_object* v_a_u2083_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(v_f_659_, v_a_u2081_660_, v_a_u2082_661_, v_a_u2083_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(lean_object* v_f_674_, lean_object* v_a_u2081_675_, lean_object* v_a_u2082_676_, lean_object* v_a_u2083_677_, lean_object* v_a_u2084_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(v_f_674_, v_a_u2081_675_, v_a_u2082_676_, v_a_u2083_677_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_691_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_a_690_);
lean_dec_ref_known(v___x_689_, 1);
v___x_691_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(v_a_690_, v_a_u2084_678_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
return v___x_691_;
}
else
{
lean_dec_ref(v_a_u2084_678_);
return v___x_689_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0___boxed(lean_object* v_f_692_, lean_object* v_a_u2081_693_, lean_object* v_a_u2082_694_, lean_object* v_a_u2083_695_, lean_object* v_a_u2084_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(v_f_692_, v_a_u2081_693_, v_a_u2082_694_, v_a_u2083_695_, v_a_u2084_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1(lean_object* v___x_713_, lean_object* v_e_x27_714_, lean_object* v___x_715_, lean_object* v_arg_716_, lean_object* v_arg_717_, lean_object* v_e_718_, lean_object* v_proof_719_, uint8_t v___x_720_, uint8_t v_contextDependent_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___x_732_; 
lean_inc_ref(v___x_715_);
lean_inc_ref(v_e_x27_714_);
v___x_732_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(v___x_713_, v_e_x27_714_, v___x_715_, v_arg_716_, v_arg_717_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_744_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_744_ == 0)
{
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_744_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_744_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__1));
v___x_738_ = l_Lean_Expr_replaceFn(v_e_718_, v___x_737_);
v___x_739_ = l_Lean_mkApp3(v___x_738_, v_e_x27_714_, v___x_715_, v_proof_719_);
v___x_740_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_740_, 0, v_a_733_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
lean_ctor_set_uint8(v___x_740_, sizeof(void*)*2, v___x_720_);
lean_ctor_set_uint8(v___x_740_, sizeof(void*)*2 + 1, v_contextDependent_721_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_740_);
v___x_742_ = v___x_735_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec_ref(v_proof_719_);
lean_dec_ref(v_e_718_);
lean_dec_ref(v___x_715_);
lean_dec_ref(v_e_x27_714_);
v_a_745_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_732_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_732_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___boxed(lean_object** _args){
lean_object* v___x_753_ = _args[0];
lean_object* v_e_x27_754_ = _args[1];
lean_object* v___x_755_ = _args[2];
lean_object* v_arg_756_ = _args[3];
lean_object* v_arg_757_ = _args[4];
lean_object* v_e_758_ = _args[5];
lean_object* v_proof_759_ = _args[6];
lean_object* v___x_760_ = _args[7];
lean_object* v_contextDependent_761_ = _args[8];
lean_object* v___y_762_ = _args[9];
lean_object* v___y_763_ = _args[10];
lean_object* v___y_764_ = _args[11];
lean_object* v___y_765_ = _args[12];
lean_object* v___y_766_ = _args[13];
lean_object* v___y_767_ = _args[14];
lean_object* v___y_768_ = _args[15];
lean_object* v___y_769_ = _args[16];
lean_object* v___y_770_ = _args[17];
lean_object* v___y_771_ = _args[18];
_start:
{
uint8_t v___x_18465__boxed_772_; uint8_t v_contextDependent_18466__boxed_773_; lean_object* v_res_774_; 
v___x_18465__boxed_772_ = lean_unbox(v___x_760_);
v_contextDependent_18466__boxed_773_ = lean_unbox(v_contextDependent_761_);
v_res_774_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1(v___x_753_, v_e_x27_754_, v___x_755_, v_arg_756_, v_arg_757_, v_e_758_, v_proof_759_, v___x_18465__boxed_772_, v_contextDependent_18466__boxed_773_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
return v_res_774_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_785_ = lean_box(0);
v___x_786_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__5));
v___x_787_ = l_Lean_mkConst(v___x_786_, v___x_785_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2(uint8_t v___x_794_, lean_object* v_e_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v___x_809_; uint8_t v___x_810_; 
lean_inc_ref(v_e_795_);
v___x_809_ = l_Lean_Expr_cleanupAnnotations(v_e_795_);
v___x_810_ = l_Lean_Expr_isApp(v___x_809_);
if (v___x_810_ == 0)
{
lean_dec_ref(v___x_809_);
lean_dec_ref(v_e_795_);
goto v___jp_806_;
}
else
{
lean_object* v_arg_811_; lean_object* v___x_812_; uint8_t v___x_813_; 
v_arg_811_ = lean_ctor_get(v___x_809_, 1);
lean_inc_ref(v_arg_811_);
v___x_812_ = l_Lean_Expr_appFnCleanup___redArg(v___x_809_);
v___x_813_ = l_Lean_Expr_isApp(v___x_812_);
if (v___x_813_ == 0)
{
lean_dec_ref(v___x_812_);
lean_dec_ref(v_arg_811_);
lean_dec_ref(v_e_795_);
goto v___jp_806_;
}
else
{
lean_object* v_arg_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v_arg_814_ = lean_ctor_get(v___x_812_, 1);
lean_inc_ref(v_arg_814_);
v___x_815_ = l_Lean_Expr_appFnCleanup___redArg(v___x_812_);
v___x_816_ = l_Lean_Expr_isApp(v___x_815_);
if (v___x_816_ == 0)
{
lean_dec_ref(v___x_815_);
lean_dec_ref(v_arg_814_);
lean_dec_ref(v_arg_811_);
lean_dec_ref(v_e_795_);
goto v___jp_806_;
}
else
{
lean_object* v_arg_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v_arg_817_ = lean_ctor_get(v___x_815_, 1);
lean_inc_ref(v_arg_817_);
v___x_818_ = l_Lean_Expr_appFnCleanup___redArg(v___x_815_);
v___x_819_ = l_Lean_Expr_isApp(v___x_818_);
if (v___x_819_ == 0)
{
lean_dec_ref(v___x_818_);
lean_dec_ref(v_arg_817_);
lean_dec_ref(v_arg_814_);
lean_dec_ref(v_arg_811_);
lean_dec_ref(v_e_795_);
goto v___jp_806_;
}
else
{
lean_object* v_arg_820_; lean_object* v___x_821_; uint8_t v___x_822_; 
v_arg_820_ = lean_ctor_get(v___x_818_, 1);
lean_inc_ref(v_arg_820_);
v___x_821_ = l_Lean_Expr_appFnCleanup___redArg(v___x_818_);
v___x_822_ = l_Lean_Expr_isApp(v___x_821_);
if (v___x_822_ == 0)
{
lean_dec_ref(v___x_821_);
lean_dec_ref(v_arg_820_);
lean_dec_ref(v_arg_817_);
lean_dec_ref(v_arg_814_);
lean_dec_ref(v_arg_811_);
lean_dec_ref(v_e_795_);
goto v___jp_806_;
}
else
{
lean_object* v_arg_823_; lean_object* v___x_824_; lean_object* v___x_825_; uint8_t v___x_826_; 
v_arg_823_ = lean_ctor_get(v___x_821_, 1);
lean_inc_ref(v_arg_823_);
v___x_824_ = l_Lean_Expr_appFnCleanup___redArg(v___x_821_);
v___x_825_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__1));
v___x_826_ = l_Lean_Expr_isConstOf(v___x_824_, v___x_825_);
if (v___x_826_ == 0)
{
lean_dec_ref(v___x_824_);
lean_dec_ref(v_arg_823_);
lean_dec_ref(v_arg_820_);
lean_dec_ref(v_arg_817_);
lean_dec_ref(v_arg_814_);
lean_dec_ref(v_arg_811_);
lean_dec_ref(v_e_795_);
goto v___jp_806_;
}
else
{
lean_object* v___x_827_; 
lean_inc(v___y_804_);
lean_inc_ref(v___y_803_);
lean_inc(v___y_802_);
lean_inc_ref(v___y_801_);
lean_inc(v___y_800_);
lean_inc_ref(v___y_799_);
lean_inc(v___y_798_);
lean_inc_ref(v___y_797_);
lean_inc(v___y_796_);
lean_inc_ref(v_arg_820_);
v___x_827_ = lean_sym_simp(v_arg_820_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
lean_dec_ref_known(v___x_827_, 1);
if (lean_obj_tag(v_a_828_) == 0)
{
uint8_t v_contextDependent_829_; lean_object* v___x_830_; 
lean_dec_ref(v_e_795_);
v_contextDependent_829_ = lean_ctor_get_uint8(v_a_828_, 1);
lean_dec_ref_known(v_a_828_, 0);
v___x_830_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_820_, v___y_799_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_871_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_871_ == 0)
{
v___x_833_ = v___x_830_;
v_isShared_834_ = v_isSharedCheck_871_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_830_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_871_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
uint8_t v___x_835_; 
v___x_835_ = lean_unbox(v_a_831_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; 
lean_del_object(v___x_833_);
v___x_836_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_820_, v___y_799_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_854_; 
v_a_837_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_854_ == 0)
{
v___x_839_ = v___x_836_;
v_isShared_840_ = v_isSharedCheck_854_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_836_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_854_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
uint8_t v___x_841_; 
v___x_841_ = lean_unbox(v_a_837_);
lean_dec(v_a_837_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; lean_object* v___f_843_; lean_object* v___x_844_; 
lean_del_object(v___x_839_);
lean_dec(v_a_831_);
v___x_842_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_826_, v_contextDependent_829_);
v___f_843_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_843_, 0, v___x_842_);
v___x_844_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(v___x_824_, v_arg_823_, v_arg_820_, v_arg_817_, v_arg_814_, v_arg_811_, v___f_843_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec_ref(v___x_824_);
return v___x_844_;
}
else
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; lean_object* v___x_852_; 
lean_dec_ref(v_arg_820_);
lean_dec_ref(v_arg_817_);
v___x_845_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__2));
v___x_846_ = l_Lean_Expr_constLevels_x21(v___x_824_);
lean_dec_ref(v___x_824_);
v___x_847_ = l_Lean_mkConst(v___x_845_, v___x_846_);
lean_inc_ref(v_arg_811_);
v___x_848_ = l_Lean_mkApp3(v___x_847_, v_arg_823_, v_arg_814_, v_arg_811_);
v___x_849_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_849_, 0, v_arg_811_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
v___x_850_ = lean_unbox(v_a_831_);
lean_dec(v_a_831_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*2, v___x_850_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*2 + 1, v_contextDependent_829_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v___x_849_);
v___x_852_ = v___x_839_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_849_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_dec(v_a_831_);
lean_dec_ref(v___x_824_);
lean_dec_ref(v_arg_823_);
lean_dec_ref(v_arg_820_);
lean_dec_ref(v_arg_817_);
lean_dec_ref(v_arg_814_);
lean_dec_ref(v_arg_811_);
v_a_855_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_836_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_836_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
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
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_869_; 
lean_dec(v_a_831_);
lean_dec_ref(v_arg_820_);
lean_dec_ref(v_arg_817_);
v___x_863_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__3));
v___x_864_ = l_Lean_Expr_constLevels_x21(v___x_824_);
lean_dec_ref(v___x_824_);
v___x_865_ = l_Lean_mkConst(v___x_863_, v___x_864_);
lean_inc_ref(v_arg_814_);
v___x_866_ = l_Lean_mkApp3(v___x_865_, v_arg_823_, v_arg_814_, v_arg_811_);
v___x_867_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_867_, 0, v_arg_814_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
lean_ctor_set_uint8(v___x_867_, sizeof(void*)*2, v___x_794_);
lean_ctor_set_uint8(v___x_867_, sizeof(void*)*2 + 1, v_contextDependent_829_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v___x_867_);
v___x_869_ = v___x_833_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec_ref(v___x_824_);
lean_dec_ref(v_arg_823_);
lean_dec_ref(v_arg_820_);
lean_dec_ref(v_arg_817_);
lean_dec_ref(v_arg_814_);
lean_dec_ref(v_arg_811_);
v_a_872_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_830_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_830_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
else
{
lean_object* v_e_x27_880_; lean_object* v_proof_881_; uint8_t v_contextDependent_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_944_; 
v_e_x27_880_ = lean_ctor_get(v_a_828_, 0);
v_proof_881_ = lean_ctor_get(v_a_828_, 1);
v_contextDependent_882_ = lean_ctor_get_uint8(v_a_828_, sizeof(void*)*2 + 1);
v_isSharedCheck_944_ = !lean_is_exclusive(v_a_828_);
if (v_isSharedCheck_944_ == 0)
{
v___x_884_ = v_a_828_;
v_isShared_885_ = v_isSharedCheck_944_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_proof_881_);
lean_inc(v_e_x27_880_);
lean_dec(v_a_828_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_944_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_880_, v___y_799_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_935_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_935_ == 0)
{
v___x_889_ = v___x_886_;
v_isShared_890_ = v_isSharedCheck_935_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_886_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_935_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
uint8_t v___x_891_; 
v___x_891_ = lean_unbox(v_a_887_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; 
lean_del_object(v___x_889_);
v___x_892_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_880_, v___y_799_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_917_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_917_ == 0)
{
v___x_895_ = v___x_892_;
v_isShared_896_ = v_isSharedCheck_917_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_892_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_917_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
uint8_t v___x_897_; 
v___x_897_ = lean_unbox(v_a_893_);
lean_dec(v_a_893_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___f_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
lean_del_object(v___x_895_);
lean_dec(v_a_887_);
lean_del_object(v___x_884_);
v___x_898_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6);
lean_inc_ref_n(v_proof_881_, 2);
lean_inc_ref_n(v_arg_817_, 2);
lean_inc_ref_n(v_e_x27_880_, 2);
lean_inc_ref_n(v_arg_820_, 2);
v___x_899_ = l_Lean_mkApp4(v___x_898_, v_arg_820_, v_e_x27_880_, v_arg_817_, v_proof_881_);
v___x_900_ = lean_unsigned_to_nat(4u);
v___x_901_ = l_Lean_Expr_getBoundedAppFn(v___x_900_, v_e_795_);
v___x_902_ = lean_box(v___x_826_);
v___x_903_ = lean_box(v_contextDependent_882_);
lean_inc_ref_n(v_arg_811_, 2);
lean_inc_ref_n(v_arg_814_, 2);
lean_inc_ref(v___x_899_);
v___f_904_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___boxed), 19, 9);
lean_closure_set(v___f_904_, 0, v___x_901_);
lean_closure_set(v___f_904_, 1, v_e_x27_880_);
lean_closure_set(v___f_904_, 2, v___x_899_);
lean_closure_set(v___f_904_, 3, v_arg_814_);
lean_closure_set(v___f_904_, 4, v_arg_811_);
lean_closure_set(v___f_904_, 5, v_e_795_);
lean_closure_set(v___f_904_, 6, v_proof_881_);
lean_closure_set(v___f_904_, 7, v___x_902_);
lean_closure_set(v___f_904_, 8, v___x_903_);
lean_inc_ref(v_arg_823_);
lean_inc_ref(v___x_824_);
v___x_905_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___boxed), 20, 10);
lean_closure_set(v___x_905_, 0, v___x_824_);
lean_closure_set(v___x_905_, 1, v_arg_823_);
lean_closure_set(v___x_905_, 2, v_arg_820_);
lean_closure_set(v___x_905_, 3, v_arg_817_);
lean_closure_set(v___x_905_, 4, v_arg_814_);
lean_closure_set(v___x_905_, 5, v_arg_811_);
lean_closure_set(v___x_905_, 6, v_e_x27_880_);
lean_closure_set(v___x_905_, 7, v_proof_881_);
lean_closure_set(v___x_905_, 8, v___x_899_);
lean_closure_set(v___x_905_, 9, v___f_904_);
v___x_906_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(v___x_824_, v_arg_823_, v_arg_820_, v_arg_817_, v_arg_814_, v_arg_811_, v___x_905_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec_ref(v___x_824_);
return v___x_906_;
}
else
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_911_; 
lean_dec_ref(v_e_x27_880_);
lean_dec_ref(v___x_824_);
lean_dec_ref(v_arg_823_);
lean_dec_ref(v_arg_820_);
lean_dec_ref(v_arg_817_);
lean_dec_ref(v_arg_814_);
v___x_907_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__8));
v___x_908_ = l_Lean_Expr_replaceFn(v_e_795_, v___x_907_);
v___x_909_ = l_Lean_Expr_app___override(v___x_908_, v_proof_881_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 1, v___x_909_);
lean_ctor_set(v___x_884_, 0, v_arg_811_);
v___x_911_ = v___x_884_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_arg_811_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v___x_909_);
v___x_911_ = v_reuseFailAlloc_916_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
uint8_t v___x_912_; lean_object* v___x_914_; 
v___x_912_ = lean_unbox(v_a_887_);
lean_dec(v_a_887_);
lean_ctor_set_uint8(v___x_911_, sizeof(void*)*2, v___x_912_);
lean_ctor_set_uint8(v___x_911_, sizeof(void*)*2 + 1, v_contextDependent_882_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 0, v___x_911_);
v___x_914_ = v___x_895_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_911_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_dec(v_a_887_);
lean_del_object(v___x_884_);
lean_dec_ref(v_proof_881_);
lean_dec_ref(v_e_x27_880_);
lean_dec_ref(v___x_824_);
lean_dec_ref(v_arg_823_);
lean_dec_ref(v_arg_820_);
lean_dec_ref(v_arg_817_);
lean_dec_ref(v_arg_814_);
lean_dec_ref(v_arg_811_);
lean_dec_ref(v_e_795_);
v_a_918_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_892_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_892_);
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
else
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_930_; 
lean_dec(v_a_887_);
lean_dec_ref(v_e_x27_880_);
lean_dec_ref(v___x_824_);
lean_dec_ref(v_arg_823_);
lean_dec_ref(v_arg_820_);
lean_dec_ref(v_arg_817_);
lean_dec_ref(v_arg_811_);
v___x_926_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__10));
v___x_927_ = l_Lean_Expr_replaceFn(v_e_795_, v___x_926_);
v___x_928_ = l_Lean_Expr_app___override(v___x_927_, v_proof_881_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 1, v___x_928_);
lean_ctor_set(v___x_884_, 0, v_arg_814_);
v___x_930_ = v___x_884_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_arg_814_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v___x_928_);
lean_ctor_set_uint8(v_reuseFailAlloc_934_, sizeof(void*)*2 + 1, v_contextDependent_882_);
v___x_930_ = v_reuseFailAlloc_934_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
lean_object* v___x_932_; 
lean_ctor_set_uint8(v___x_930_, sizeof(void*)*2, v___x_794_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_930_);
v___x_932_ = v___x_889_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_930_);
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
else
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
lean_del_object(v___x_884_);
lean_dec_ref(v_proof_881_);
lean_dec_ref(v_e_x27_880_);
lean_dec_ref(v___x_824_);
lean_dec_ref(v_arg_823_);
lean_dec_ref(v_arg_820_);
lean_dec_ref(v_arg_817_);
lean_dec_ref(v_arg_814_);
lean_dec_ref(v_arg_811_);
lean_dec_ref(v_e_795_);
v_a_936_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_886_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_886_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_824_);
lean_dec_ref(v_arg_823_);
lean_dec_ref(v_arg_820_);
lean_dec_ref(v_arg_817_);
lean_dec_ref(v_arg_814_);
lean_dec_ref(v_arg_811_);
lean_dec_ref(v_e_795_);
return v___x_827_;
}
}
}
}
}
}
}
v___jp_806_:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_807_, 0, v___x_794_);
lean_ctor_set_uint8(v___x_807_, 1, v___x_794_);
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___boxed(lean_object* v___x_945_, lean_object* v_e_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
uint8_t v___x_18600__boxed_957_; lean_object* v_res_958_; 
v___x_18600__boxed_957_ = lean_unbox(v___x_945_);
v_res_958_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2(v___x_18600__boxed_957_, v_e_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv(lean_object* v_e_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_numArgs_970_; lean_object* v___x_971_; uint8_t v___x_972_; 
v_numArgs_970_ = l_Lean_Expr_getAppNumArgs(v_e_959_);
v___x_971_ = lean_unsigned_to_nat(5u);
v___x_972_ = lean_nat_dec_lt(v_numArgs_970_, v___x_971_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; lean_object* v___f_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_973_ = lean_box(v___x_972_);
v___f_974_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___boxed), 12, 1);
lean_closure_set(v___f_974_, 0, v___x_973_);
v___x_975_ = lean_nat_sub(v_numArgs_970_, v___x_971_);
lean_dec(v_numArgs_970_);
v___x_976_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_959_, v___x_975_, v___f_974_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
lean_dec(v___x_975_);
return v___x_976_;
}
else
{
uint8_t v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
lean_dec(v_numArgs_970_);
lean_dec_ref(v_e_959_);
v___x_977_ = 0;
v___x_978_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_978_, 0, v___x_972_);
lean_ctor_set_uint8(v___x_978_, 1, v___x_977_);
v___x_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
return v___x_979_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___boxed(lean_object* v_e_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv(v_e_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_a_981_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1(lean_object* v_f_992_, lean_object* v_a_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(v_f_992_, v_a_993_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___boxed(lean_object* v_f_1005_, lean_object* v_a_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1(v_f_1005_, v_a_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1075_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_));
v___x_1076_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__20_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_));
v___x_1077_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___boxed), 11, 0);
v___x_1078_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_1075_, v___x_1076_, v___x_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16____boxed(lean_object* v_a_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_();
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_1082_; uint8_t v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1082_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_));
v___x_1083_ = 0;
v___x_1084_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___boxed), 11, 0);
v___x_1085_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_1082_, v___x_1083_, v___x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_18____boxed(lean_object* v_a_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_18_();
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(lean_object* v_f_1098_, lean_object* v_00_u03b1_1099_, lean_object* v_c_1100_, lean_object* v_inst_1101_, lean_object* v_a_1102_, lean_object* v_b_1103_, lean_object* v_instToMatch_1104_, lean_object* v_fallback_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_instToMatch_1104_, v_a_1112_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1116_, 1);
v___x_1118_ = l_Lean_Expr_cleanupAnnotations(v_a_1117_);
v___x_1119_ = l_Lean_Expr_isApp(v___x_1118_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; 
lean_dec_ref(v___x_1118_);
lean_dec_ref(v_b_1103_);
lean_dec_ref(v_a_1102_);
lean_dec_ref(v_inst_1101_);
lean_dec_ref(v_c_1100_);
lean_dec_ref(v_00_u03b1_1099_);
lean_inc(v_a_1114_);
lean_inc_ref(v_a_1113_);
lean_inc(v_a_1112_);
lean_inc_ref(v_a_1111_);
lean_inc(v_a_1110_);
lean_inc_ref(v_a_1109_);
lean_inc(v_a_1108_);
lean_inc_ref(v_a_1107_);
lean_inc(v_a_1106_);
v___x_1120_ = lean_apply_10(v_fallback_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, lean_box(0));
return v___x_1120_;
}
else
{
lean_object* v_arg_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; 
v_arg_1121_ = lean_ctor_get(v___x_1118_, 1);
lean_inc_ref(v_arg_1121_);
v___x_1122_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1118_);
v___x_1123_ = l_Lean_Expr_isApp(v___x_1122_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; 
lean_dec_ref(v___x_1122_);
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_b_1103_);
lean_dec_ref(v_a_1102_);
lean_dec_ref(v_inst_1101_);
lean_dec_ref(v_c_1100_);
lean_dec_ref(v_00_u03b1_1099_);
lean_inc(v_a_1114_);
lean_inc_ref(v_a_1113_);
lean_inc(v_a_1112_);
lean_inc_ref(v_a_1111_);
lean_inc(v_a_1110_);
lean_inc_ref(v_a_1109_);
lean_inc(v_a_1108_);
lean_inc_ref(v_a_1107_);
lean_inc(v_a_1106_);
v___x_1124_ = lean_apply_10(v_fallback_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, lean_box(0));
return v___x_1124_;
}
else
{
lean_object* v___x_1125_; lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1125_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1122_);
v___x_1126_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_1127_ = l_Lean_Expr_isConstOf(v___x_1125_, v___x_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3));
v___x_1129_ = l_Lean_Expr_isConstOf(v___x_1125_, v___x_1128_);
lean_dec_ref(v___x_1125_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; 
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_b_1103_);
lean_dec_ref(v_a_1102_);
lean_dec_ref(v_inst_1101_);
lean_dec_ref(v_c_1100_);
lean_dec_ref(v_00_u03b1_1099_);
lean_inc(v_a_1114_);
lean_inc_ref(v_a_1113_);
lean_inc(v_a_1112_);
lean_inc_ref(v_a_1111_);
lean_inc(v_a_1110_);
lean_inc_ref(v_a_1109_);
lean_inc(v_a_1108_);
lean_inc_ref(v_a_1107_);
lean_inc(v_a_1106_);
v___x_1130_ = lean_apply_10(v_fallback_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, lean_box(0));
return v___x_1130_;
}
else
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_dec_ref(v_fallback_1105_);
v___x_1131_ = lean_unsigned_to_nat(1u);
v___x_1132_ = lean_mk_empty_array_with_capacity(v___x_1131_);
lean_inc_ref(v_arg_1121_);
v___x_1133_ = lean_array_push(v___x_1132_, v_arg_1121_);
lean_inc_ref(v_a_1102_);
v___x_1134_ = l_Lean_Expr_betaRev(v_a_1102_, v___x_1133_, v___x_1127_, v___x_1127_);
lean_dec_ref(v___x_1133_);
v___x_1135_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1134_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1148_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1138_ = v___x_1135_;
v_isShared_1139_ = v_isSharedCheck_1148_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1135_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1148_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1146_; 
v___x_1140_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1));
v___x_1141_ = l_Lean_Expr_constLevels_x21(v_f_1098_);
v___x_1142_ = l_Lean_mkConst(v___x_1140_, v___x_1141_);
v___x_1143_ = l_Lean_mkApp6(v___x_1142_, v_00_u03b1_1099_, v_c_1100_, v_inst_1101_, v_a_1102_, v_b_1103_, v_arg_1121_);
v___x_1144_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1144_, 0, v_a_1136_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
lean_ctor_set_uint8(v___x_1144_, sizeof(void*)*2, v___x_1127_);
lean_ctor_set_uint8(v___x_1144_, sizeof(void*)*2 + 1, v___x_1127_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1144_);
v___x_1146_ = v___x_1138_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_b_1103_);
lean_dec_ref(v_a_1102_);
lean_dec_ref(v_inst_1101_);
lean_dec_ref(v_c_1100_);
lean_dec_ref(v_00_u03b1_1099_);
v_a_1149_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1135_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1135_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
}
else
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
lean_dec_ref(v___x_1125_);
lean_dec_ref(v_fallback_1105_);
v___x_1157_ = lean_unsigned_to_nat(1u);
v___x_1158_ = lean_mk_empty_array_with_capacity(v___x_1157_);
lean_inc_ref(v_arg_1121_);
v___x_1159_ = lean_array_push(v___x_1158_, v_arg_1121_);
v___x_1160_ = 0;
lean_inc_ref(v_b_1103_);
v___x_1161_ = l_Lean_Expr_betaRev(v_b_1103_, v___x_1159_, v___x_1160_, v___x_1160_);
lean_dec_ref(v___x_1159_);
v___x_1162_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1161_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1175_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1165_ = v___x_1162_;
v_isShared_1166_ = v_isSharedCheck_1175_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1162_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1175_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1173_; 
v___x_1167_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3));
v___x_1168_ = l_Lean_Expr_constLevels_x21(v_f_1098_);
v___x_1169_ = l_Lean_mkConst(v___x_1167_, v___x_1168_);
v___x_1170_ = l_Lean_mkApp6(v___x_1169_, v_00_u03b1_1099_, v_c_1100_, v_inst_1101_, v_a_1102_, v_b_1103_, v_arg_1121_);
v___x_1171_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1171_, 0, v_a_1163_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
lean_ctor_set_uint8(v___x_1171_, sizeof(void*)*2, v___x_1160_);
lean_ctor_set_uint8(v___x_1171_, sizeof(void*)*2 + 1, v___x_1160_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v___x_1171_);
v___x_1173_ = v___x_1165_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_b_1103_);
lean_dec_ref(v_a_1102_);
lean_dec_ref(v_inst_1101_);
lean_dec_ref(v_c_1100_);
lean_dec_ref(v_00_u03b1_1099_);
v_a_1176_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1162_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1162_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec_ref(v_fallback_1105_);
lean_dec_ref(v_b_1103_);
lean_dec_ref(v_a_1102_);
lean_dec_ref(v_inst_1101_);
lean_dec_ref(v_c_1100_);
lean_dec_ref(v_00_u03b1_1099_);
v_a_1184_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1116_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1116_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___boxed(lean_object** _args){
lean_object* v_f_1192_ = _args[0];
lean_object* v_00_u03b1_1193_ = _args[1];
lean_object* v_c_1194_ = _args[2];
lean_object* v_inst_1195_ = _args[3];
lean_object* v_a_1196_ = _args[4];
lean_object* v_b_1197_ = _args[5];
lean_object* v_instToMatch_1198_ = _args[6];
lean_object* v_fallback_1199_ = _args[7];
lean_object* v_a_1200_ = _args[8];
lean_object* v_a_1201_ = _args[9];
lean_object* v_a_1202_ = _args[10];
lean_object* v_a_1203_ = _args[11];
lean_object* v_a_1204_ = _args[12];
lean_object* v_a_1205_ = _args[13];
lean_object* v_a_1206_ = _args[14];
lean_object* v_a_1207_ = _args[15];
lean_object* v_a_1208_ = _args[16];
lean_object* v_a_1209_ = _args[17];
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(v_f_1192_, v_00_u03b1_1193_, v_c_1194_, v_inst_1195_, v_a_1196_, v_b_1197_, v_instToMatch_1198_, v_fallback_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_);
lean_dec(v_a_1208_);
lean_dec_ref(v_a_1207_);
lean_dec(v_a_1206_);
lean_dec_ref(v_a_1205_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
lean_dec(v_a_1202_);
lean_dec_ref(v_a_1201_);
lean_dec(v_a_1200_);
lean_dec_ref(v_f_1192_);
return v_res_1210_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__3(void){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1216_ = lean_box(0);
v___x_1217_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2));
v___x_1218_ = l_Lean_mkConst(v___x_1217_, v___x_1216_);
return v___x_1218_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__8(void){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1228_ = lean_box(0);
v___x_1229_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7));
v___x_1230_ = l_Lean_mkConst(v___x_1229_, v___x_1228_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(lean_object* v_f_1236_, lean_object* v_00_u03b1_1237_, lean_object* v_c_1238_, lean_object* v_inst_1239_, lean_object* v_a_1240_, lean_object* v_b_1241_, lean_object* v_c_x27_1242_, lean_object* v_h_1243_, lean_object* v_inst_x27_1244_, lean_object* v_fallback_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_inst_x27_1244_, v_a_1252_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_a_1257_);
lean_dec_ref_known(v___x_1256_, 1);
v___x_1258_ = l_Lean_Expr_cleanupAnnotations(v_a_1257_);
v___x_1259_ = l_Lean_Expr_isApp(v___x_1258_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; 
lean_dec_ref(v___x_1258_);
lean_dec_ref(v_h_1243_);
lean_dec_ref(v_c_x27_1242_);
lean_dec_ref(v_b_1241_);
lean_dec_ref(v_a_1240_);
lean_dec_ref(v_inst_1239_);
lean_dec_ref(v_c_1238_);
lean_dec_ref(v_00_u03b1_1237_);
lean_inc(v_a_1254_);
lean_inc_ref(v_a_1253_);
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
lean_inc(v_a_1250_);
lean_inc_ref(v_a_1249_);
lean_inc(v_a_1248_);
lean_inc_ref(v_a_1247_);
lean_inc(v_a_1246_);
v___x_1260_ = lean_apply_10(v_fallback_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, lean_box(0));
return v___x_1260_;
}
else
{
lean_object* v_arg_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v_arg_1261_ = lean_ctor_get(v___x_1258_, 1);
lean_inc_ref(v_arg_1261_);
v___x_1262_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1258_);
v___x_1263_ = l_Lean_Expr_isApp(v___x_1262_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; 
lean_dec_ref(v___x_1262_);
lean_dec_ref(v_arg_1261_);
lean_dec_ref(v_h_1243_);
lean_dec_ref(v_c_x27_1242_);
lean_dec_ref(v_b_1241_);
lean_dec_ref(v_a_1240_);
lean_dec_ref(v_inst_1239_);
lean_dec_ref(v_c_1238_);
lean_dec_ref(v_00_u03b1_1237_);
lean_inc(v_a_1254_);
lean_inc_ref(v_a_1253_);
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
lean_inc(v_a_1250_);
lean_inc_ref(v_a_1249_);
lean_inc(v_a_1248_);
lean_inc_ref(v_a_1247_);
lean_inc(v_a_1246_);
v___x_1264_ = lean_apply_10(v_fallback_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, lean_box(0));
return v___x_1264_;
}
else
{
lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1265_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1262_);
v___x_1266_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_1267_ = l_Lean_Expr_isConstOf(v___x_1265_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1268_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3));
v___x_1269_ = l_Lean_Expr_isConstOf(v___x_1265_, v___x_1268_);
lean_dec_ref(v___x_1265_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; 
lean_dec_ref(v_arg_1261_);
lean_dec_ref(v_h_1243_);
lean_dec_ref(v_c_x27_1242_);
lean_dec_ref(v_b_1241_);
lean_dec_ref(v_a_1240_);
lean_dec_ref(v_inst_1239_);
lean_dec_ref(v_c_1238_);
lean_dec_ref(v_00_u03b1_1237_);
lean_inc(v_a_1254_);
lean_inc_ref(v_a_1253_);
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
lean_inc(v_a_1250_);
lean_inc_ref(v_a_1249_);
lean_inc(v_a_1248_);
lean_inc_ref(v_a_1247_);
lean_inc(v_a_1246_);
v___x_1270_ = lean_apply_10(v_fallback_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, lean_box(0));
return v___x_1270_;
}
else
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
lean_dec_ref(v_fallback_1245_);
v___x_1271_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__3, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__3);
lean_inc_ref(v_arg_1261_);
lean_inc_ref(v_h_1243_);
lean_inc_ref(v_c_x27_1242_);
lean_inc_ref(v_c_1238_);
v___x_1272_ = l_Lean_mkApp4(v___x_1271_, v_c_1238_, v_c_x27_1242_, v_h_1243_, v_arg_1261_);
v___x_1273_ = lean_unsigned_to_nat(1u);
v___x_1274_ = lean_mk_empty_array_with_capacity(v___x_1273_);
v___x_1275_ = lean_array_push(v___x_1274_, v___x_1272_);
lean_inc_ref(v_a_1240_);
v___x_1276_ = l_Lean_Expr_betaRev(v_a_1240_, v___x_1275_, v___x_1267_, v___x_1267_);
lean_dec_ref(v___x_1275_);
v___x_1277_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1276_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1290_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1280_ = v___x_1277_;
v_isShared_1281_ = v_isSharedCheck_1290_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1277_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1290_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1288_; 
v___x_1282_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__5));
v___x_1283_ = l_Lean_Expr_constLevels_x21(v_f_1236_);
v___x_1284_ = l_Lean_mkConst(v___x_1282_, v___x_1283_);
v___x_1285_ = l_Lean_mkApp8(v___x_1284_, v_00_u03b1_1237_, v_c_1238_, v_inst_1239_, v_a_1240_, v_b_1241_, v_c_x27_1242_, v_h_1243_, v_arg_1261_);
v___x_1286_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1286_, 0, v_a_1278_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
lean_ctor_set_uint8(v___x_1286_, sizeof(void*)*2, v___x_1267_);
lean_ctor_set_uint8(v___x_1286_, sizeof(void*)*2 + 1, v___x_1267_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 0, v___x_1286_);
v___x_1288_ = v___x_1280_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec_ref(v_arg_1261_);
lean_dec_ref(v_h_1243_);
lean_dec_ref(v_c_x27_1242_);
lean_dec_ref(v_b_1241_);
lean_dec_ref(v_a_1240_);
lean_dec_ref(v_inst_1239_);
lean_dec_ref(v_c_1238_);
lean_dec_ref(v_00_u03b1_1237_);
v_a_1291_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1277_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1277_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
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
}
else
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
lean_dec_ref(v___x_1265_);
lean_dec_ref(v_fallback_1245_);
v___x_1299_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__8);
lean_inc_ref(v_arg_1261_);
lean_inc_ref(v_h_1243_);
lean_inc_ref(v_c_x27_1242_);
lean_inc_ref(v_c_1238_);
v___x_1300_ = l_Lean_mkApp4(v___x_1299_, v_c_1238_, v_c_x27_1242_, v_h_1243_, v_arg_1261_);
v___x_1301_ = lean_unsigned_to_nat(1u);
v___x_1302_ = lean_mk_empty_array_with_capacity(v___x_1301_);
v___x_1303_ = lean_array_push(v___x_1302_, v___x_1300_);
v___x_1304_ = 0;
lean_inc_ref(v_b_1241_);
v___x_1305_ = l_Lean_Expr_betaRev(v_b_1241_, v___x_1303_, v___x_1304_, v___x_1304_);
lean_dec_ref(v___x_1303_);
v___x_1306_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1305_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1319_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1309_ = v___x_1306_;
v_isShared_1310_ = v_isSharedCheck_1319_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1319_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1317_; 
v___x_1311_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__10));
v___x_1312_ = l_Lean_Expr_constLevels_x21(v_f_1236_);
v___x_1313_ = l_Lean_mkConst(v___x_1311_, v___x_1312_);
v___x_1314_ = l_Lean_mkApp8(v___x_1313_, v_00_u03b1_1237_, v_c_1238_, v_inst_1239_, v_a_1240_, v_b_1241_, v_c_x27_1242_, v_h_1243_, v_arg_1261_);
v___x_1315_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1315_, 0, v_a_1307_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
lean_ctor_set_uint8(v___x_1315_, sizeof(void*)*2, v___x_1304_);
lean_ctor_set_uint8(v___x_1315_, sizeof(void*)*2 + 1, v___x_1304_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v___x_1315_);
v___x_1317_ = v___x_1309_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec_ref(v_arg_1261_);
lean_dec_ref(v_h_1243_);
lean_dec_ref(v_c_x27_1242_);
lean_dec_ref(v_b_1241_);
lean_dec_ref(v_a_1240_);
lean_dec_ref(v_inst_1239_);
lean_dec_ref(v_c_1238_);
lean_dec_ref(v_00_u03b1_1237_);
v_a_1320_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1306_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1306_);
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
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec_ref(v_fallback_1245_);
lean_dec_ref(v_h_1243_);
lean_dec_ref(v_c_x27_1242_);
lean_dec_ref(v_b_1241_);
lean_dec_ref(v_a_1240_);
lean_dec_ref(v_inst_1239_);
lean_dec_ref(v_c_1238_);
lean_dec_ref(v_00_u03b1_1237_);
v_a_1328_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1256_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1256_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___boxed(lean_object** _args){
lean_object* v_f_1336_ = _args[0];
lean_object* v_00_u03b1_1337_ = _args[1];
lean_object* v_c_1338_ = _args[2];
lean_object* v_inst_1339_ = _args[3];
lean_object* v_a_1340_ = _args[4];
lean_object* v_b_1341_ = _args[5];
lean_object* v_c_x27_1342_ = _args[6];
lean_object* v_h_1343_ = _args[7];
lean_object* v_inst_x27_1344_ = _args[8];
lean_object* v_fallback_1345_ = _args[9];
lean_object* v_a_1346_ = _args[10];
lean_object* v_a_1347_ = _args[11];
lean_object* v_a_1348_ = _args[12];
lean_object* v_a_1349_ = _args[13];
lean_object* v_a_1350_ = _args[14];
lean_object* v_a_1351_ = _args[15];
lean_object* v_a_1352_ = _args[16];
lean_object* v_a_1353_ = _args[17];
lean_object* v_a_1354_ = _args[18];
lean_object* v_a_1355_ = _args[19];
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(v_f_1336_, v_00_u03b1_1337_, v_c_1338_, v_inst_1339_, v_a_1340_, v_b_1341_, v_c_x27_1342_, v_h_1343_, v_inst_x27_1344_, v_fallback_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
lean_dec(v_a_1354_);
lean_dec_ref(v_a_1353_);
lean_dec(v_a_1352_);
lean_dec_ref(v_a_1351_);
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1349_);
lean_dec(v_a_1348_);
lean_dec_ref(v_a_1347_);
lean_dec(v_a_1346_);
lean_dec_ref(v_f_1336_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(lean_object* v_f_1357_, lean_object* v_00_u03b1_1358_, lean_object* v_c_1359_, lean_object* v_inst_1360_, lean_object* v_a_1361_, lean_object* v_b_1362_, lean_object* v_fallback_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_){
_start:
{
lean_object* v___x_1374_; 
lean_inc(v_a_1372_);
lean_inc_ref(v_a_1371_);
lean_inc(v_a_1370_);
lean_inc_ref(v_a_1369_);
lean_inc(v_a_1368_);
lean_inc_ref(v_a_1367_);
lean_inc(v_a_1366_);
lean_inc_ref(v_a_1365_);
lean_inc(v_a_1364_);
lean_inc_ref(v_inst_1360_);
v___x_1374_ = lean_sym_simp(v_inst_1360_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1374_, 1);
if (lean_obj_tag(v_a_1375_) == 0)
{
uint8_t v_contextDependent_1376_; lean_object* v___x_1377_; 
v_contextDependent_1376_ = lean_ctor_get_uint8(v_a_1375_, 1);
lean_dec_ref_known(v_a_1375_, 0);
lean_inc_ref(v_inst_1360_);
v___x_1377_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(v_f_1357_, v_00_u03b1_1358_, v_c_1359_, v_inst_1360_, v_a_1361_, v_b_1362_, v_inst_1360_, v_fallback_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; uint8_t v___y_1380_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
if (v_contextDependent_1376_ == 0)
{
lean_dec(v_a_1378_);
return v___x_1377_;
}
else
{
if (lean_obj_tag(v_a_1378_) == 0)
{
uint8_t v_contextDependent_1390_; uint8_t v___x_1391_; 
v_contextDependent_1390_ = lean_ctor_get_uint8(v_a_1378_, 1);
v___x_1391_ = lean_bool_not(v_contextDependent_1390_);
v___y_1380_ = v___x_1391_;
goto v___jp_1379_;
}
else
{
uint8_t v_contextDependent_1392_; uint8_t v___x_1393_; 
v_contextDependent_1392_ = lean_ctor_get_uint8(v_a_1378_, sizeof(void*)*2 + 1);
v___x_1393_ = lean_bool_not(v_contextDependent_1392_);
v___y_1380_ = v___x_1393_;
goto v___jp_1379_;
}
}
v___jp_1379_:
{
if (v___y_1380_ == 0)
{
lean_dec(v_a_1378_);
return v___x_1377_;
}
else
{
lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1388_; 
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1388_ == 0)
{
lean_object* v_unused_1389_; 
v_unused_1389_ = lean_ctor_get(v___x_1377_, 0);
lean_dec(v_unused_1389_);
v___x_1382_ = v___x_1377_;
v_isShared_1383_ = v_isSharedCheck_1388_;
goto v_resetjp_1381_;
}
else
{
lean_dec(v___x_1377_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1388_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1384_; lean_object* v___x_1386_; 
v___x_1384_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1378_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1384_);
v___x_1386_ = v___x_1382_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1384_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
}
else
{
return v___x_1377_;
}
}
else
{
lean_object* v_e_x27_1394_; uint8_t v_contextDependent_1395_; lean_object* v___x_1396_; 
v_e_x27_1394_ = lean_ctor_get(v_a_1375_, 0);
lean_inc_ref(v_e_x27_1394_);
v_contextDependent_1395_ = lean_ctor_get_uint8(v_a_1375_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1375_, 2);
v___x_1396_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(v_f_1357_, v_00_u03b1_1358_, v_c_1359_, v_inst_1360_, v_a_1361_, v_b_1362_, v_e_x27_1394_, v_fallback_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; uint8_t v___y_1399_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_a_1397_);
if (v_contextDependent_1395_ == 0)
{
lean_dec(v_a_1397_);
return v___x_1396_;
}
else
{
if (lean_obj_tag(v_a_1397_) == 0)
{
uint8_t v_contextDependent_1409_; uint8_t v___x_1410_; 
v_contextDependent_1409_ = lean_ctor_get_uint8(v_a_1397_, 1);
v___x_1410_ = lean_bool_not(v_contextDependent_1409_);
v___y_1399_ = v___x_1410_;
goto v___jp_1398_;
}
else
{
uint8_t v_contextDependent_1411_; uint8_t v___x_1412_; 
v_contextDependent_1411_ = lean_ctor_get_uint8(v_a_1397_, sizeof(void*)*2 + 1);
v___x_1412_ = lean_bool_not(v_contextDependent_1411_);
v___y_1399_ = v___x_1412_;
goto v___jp_1398_;
}
}
v___jp_1398_:
{
if (v___y_1399_ == 0)
{
lean_dec(v_a_1397_);
return v___x_1396_;
}
else
{
lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1407_; 
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1407_ == 0)
{
lean_object* v_unused_1408_; 
v_unused_1408_ = lean_ctor_get(v___x_1396_, 0);
lean_dec(v_unused_1408_);
v___x_1401_ = v___x_1396_;
v_isShared_1402_ = v_isSharedCheck_1407_;
goto v_resetjp_1400_;
}
else
{
lean_dec(v___x_1396_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1407_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1403_; lean_object* v___x_1405_; 
v___x_1403_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1397_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 0, v___x_1403_);
v___x_1405_ = v___x_1401_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
else
{
return v___x_1396_;
}
}
}
else
{
lean_dec_ref(v_fallback_1363_);
lean_dec_ref(v_b_1362_);
lean_dec_ref(v_a_1361_);
lean_dec_ref(v_inst_1360_);
lean_dec_ref(v_c_1359_);
lean_dec_ref(v_00_u03b1_1358_);
return v___x_1374_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___boxed(lean_object** _args){
lean_object* v_f_1413_ = _args[0];
lean_object* v_00_u03b1_1414_ = _args[1];
lean_object* v_c_1415_ = _args[2];
lean_object* v_inst_1416_ = _args[3];
lean_object* v_a_1417_ = _args[4];
lean_object* v_b_1418_ = _args[5];
lean_object* v_fallback_1419_ = _args[6];
lean_object* v_a_1420_ = _args[7];
lean_object* v_a_1421_ = _args[8];
lean_object* v_a_1422_ = _args[9];
lean_object* v_a_1423_ = _args[10];
lean_object* v_a_1424_ = _args[11];
lean_object* v_a_1425_ = _args[12];
lean_object* v_a_1426_ = _args[13];
lean_object* v_a_1427_ = _args[14];
lean_object* v_a_1428_ = _args[15];
lean_object* v_a_1429_ = _args[16];
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(v_f_1413_, v_00_u03b1_1414_, v_c_1415_, v_inst_1416_, v_a_1417_, v_b_1418_, v_fallback_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_);
lean_dec(v_a_1428_);
lean_dec_ref(v_a_1427_);
lean_dec(v_a_1426_);
lean_dec_ref(v_a_1425_);
lean_dec(v_a_1424_);
lean_dec_ref(v_a_1423_);
lean_dec(v_a_1422_);
lean_dec_ref(v_a_1421_);
lean_dec(v_a_1420_);
lean_dec_ref(v_f_1413_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr(lean_object* v_f_1431_, lean_object* v_00_u03b1_1432_, lean_object* v_c_1433_, lean_object* v_inst_1434_, lean_object* v_a_1435_, lean_object* v_b_1436_, lean_object* v_c_x27_1437_, lean_object* v_h_1438_, lean_object* v_inst_x27_1439_, lean_object* v_fallback_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v___x_1451_; 
lean_inc(v_a_1449_);
lean_inc_ref(v_a_1448_);
lean_inc(v_a_1447_);
lean_inc_ref(v_a_1446_);
lean_inc(v_a_1445_);
lean_inc_ref(v_a_1444_);
lean_inc(v_a_1443_);
lean_inc_ref(v_a_1442_);
lean_inc(v_a_1441_);
lean_inc_ref(v_inst_x27_1439_);
v___x_1451_ = lean_sym_simp(v_inst_x27_1439_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1452_);
lean_dec_ref_known(v___x_1451_, 1);
if (lean_obj_tag(v_a_1452_) == 0)
{
uint8_t v_contextDependent_1453_; lean_object* v___x_1454_; 
v_contextDependent_1453_ = lean_ctor_get_uint8(v_a_1452_, 1);
lean_dec_ref_known(v_a_1452_, 0);
v___x_1454_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(v_f_1431_, v_00_u03b1_1432_, v_c_1433_, v_inst_1434_, v_a_1435_, v_b_1436_, v_c_x27_1437_, v_h_1438_, v_inst_x27_1439_, v_fallback_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; uint8_t v___y_1457_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1455_);
if (v_contextDependent_1453_ == 0)
{
lean_dec(v_a_1455_);
return v___x_1454_;
}
else
{
if (lean_obj_tag(v_a_1455_) == 0)
{
uint8_t v_contextDependent_1467_; uint8_t v___x_1468_; 
v_contextDependent_1467_ = lean_ctor_get_uint8(v_a_1455_, 1);
v___x_1468_ = lean_bool_not(v_contextDependent_1467_);
v___y_1457_ = v___x_1468_;
goto v___jp_1456_;
}
else
{
uint8_t v_contextDependent_1469_; uint8_t v___x_1470_; 
v_contextDependent_1469_ = lean_ctor_get_uint8(v_a_1455_, sizeof(void*)*2 + 1);
v___x_1470_ = lean_bool_not(v_contextDependent_1469_);
v___y_1457_ = v___x_1470_;
goto v___jp_1456_;
}
}
v___jp_1456_:
{
if (v___y_1457_ == 0)
{
lean_dec(v_a_1455_);
return v___x_1454_;
}
else
{
lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1465_; 
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; 
v_unused_1466_ = lean_ctor_get(v___x_1454_, 0);
lean_dec(v_unused_1466_);
v___x_1459_ = v___x_1454_;
v_isShared_1460_ = v_isSharedCheck_1465_;
goto v_resetjp_1458_;
}
else
{
lean_dec(v___x_1454_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1465_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1461_; lean_object* v___x_1463_; 
v___x_1461_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1455_);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 0, v___x_1461_);
v___x_1463_ = v___x_1459_;
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
}
else
{
return v___x_1454_;
}
}
else
{
lean_object* v_e_x27_1471_; uint8_t v_contextDependent_1472_; lean_object* v___x_1473_; 
lean_dec_ref(v_inst_x27_1439_);
v_e_x27_1471_ = lean_ctor_get(v_a_1452_, 0);
lean_inc_ref(v_e_x27_1471_);
v_contextDependent_1472_ = lean_ctor_get_uint8(v_a_1452_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1452_, 2);
v___x_1473_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(v_f_1431_, v_00_u03b1_1432_, v_c_1433_, v_inst_1434_, v_a_1435_, v_b_1436_, v_c_x27_1437_, v_h_1438_, v_e_x27_1471_, v_fallback_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; uint8_t v___y_1476_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1474_);
if (v_contextDependent_1472_ == 0)
{
lean_dec(v_a_1474_);
return v___x_1473_;
}
else
{
if (lean_obj_tag(v_a_1474_) == 0)
{
uint8_t v_contextDependent_1486_; uint8_t v___x_1487_; 
v_contextDependent_1486_ = lean_ctor_get_uint8(v_a_1474_, 1);
v___x_1487_ = lean_bool_not(v_contextDependent_1486_);
v___y_1476_ = v___x_1487_;
goto v___jp_1475_;
}
else
{
uint8_t v_contextDependent_1488_; uint8_t v___x_1489_; 
v_contextDependent_1488_ = lean_ctor_get_uint8(v_a_1474_, sizeof(void*)*2 + 1);
v___x_1489_ = lean_bool_not(v_contextDependent_1488_);
v___y_1476_ = v___x_1489_;
goto v___jp_1475_;
}
}
v___jp_1475_:
{
if (v___y_1476_ == 0)
{
lean_dec(v_a_1474_);
return v___x_1473_;
}
else
{
lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1484_; 
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1484_ == 0)
{
lean_object* v_unused_1485_; 
v_unused_1485_ = lean_ctor_get(v___x_1473_, 0);
lean_dec(v_unused_1485_);
v___x_1478_ = v___x_1473_;
v_isShared_1479_ = v_isSharedCheck_1484_;
goto v_resetjp_1477_;
}
else
{
lean_dec(v___x_1473_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1484_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1480_; lean_object* v___x_1482_; 
v___x_1480_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1474_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v___x_1480_);
v___x_1482_ = v___x_1478_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1480_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
else
{
return v___x_1473_;
}
}
}
else
{
lean_dec_ref(v_fallback_1440_);
lean_dec_ref(v_inst_x27_1439_);
lean_dec_ref(v_h_1438_);
lean_dec_ref(v_c_x27_1437_);
lean_dec_ref(v_b_1436_);
lean_dec_ref(v_a_1435_);
lean_dec_ref(v_inst_1434_);
lean_dec_ref(v_c_1433_);
lean_dec_ref(v_00_u03b1_1432_);
return v___x_1451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr___boxed(lean_object** _args){
lean_object* v_f_1490_ = _args[0];
lean_object* v_00_u03b1_1491_ = _args[1];
lean_object* v_c_1492_ = _args[2];
lean_object* v_inst_1493_ = _args[3];
lean_object* v_a_1494_ = _args[4];
lean_object* v_b_1495_ = _args[5];
lean_object* v_c_x27_1496_ = _args[6];
lean_object* v_h_1497_ = _args[7];
lean_object* v_inst_x27_1498_ = _args[8];
lean_object* v_fallback_1499_ = _args[9];
lean_object* v_a_1500_ = _args[10];
lean_object* v_a_1501_ = _args[11];
lean_object* v_a_1502_ = _args[12];
lean_object* v_a_1503_ = _args[13];
lean_object* v_a_1504_ = _args[14];
lean_object* v_a_1505_ = _args[15];
lean_object* v_a_1506_ = _args[16];
lean_object* v_a_1507_ = _args[17];
lean_object* v_a_1508_ = _args[18];
lean_object* v_a_1509_ = _args[19];
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr(v_f_1490_, v_00_u03b1_1491_, v_c_1492_, v_inst_1493_, v_a_1494_, v_b_1495_, v_c_x27_1496_, v_h_1497_, v_inst_x27_1498_, v_fallback_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
lean_dec(v_a_1508_);
lean_dec_ref(v_a_1507_);
lean_dec(v_a_1506_);
lean_dec_ref(v_a_1505_);
lean_dec(v_a_1504_);
lean_dec_ref(v_a_1503_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
lean_dec(v_a_1500_);
lean_dec_ref(v_f_1490_);
return v_res_1510_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = lean_unsigned_to_nat(0u);
v___x_1515_ = l_Lean_mkBVar(v___x_1514_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1(lean_object* v_proof_1521_, lean_object* v___x_1522_, lean_object* v_arg_1523_, lean_object* v_e_x27_1524_, lean_object* v_arg_1525_, uint8_t v_a_1526_, lean_object* v_arg_1527_, lean_object* v___x_1528_, lean_object* v___x_1529_, lean_object* v_e_1530_, uint8_t v___x_1531_, uint8_t v_contextDependent_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_Meta_Sym_shareCommon(v_proof_1521_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc_n(v_a_1544_, 2);
lean_dec_ref_known(v___x_1543_, 1);
v___x_1545_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__1));
v___x_1546_ = 0;
v___x_1547_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2));
lean_inc(v___x_1522_);
v___x_1548_ = l_Lean_mkConst(v___x_1547_, v___x_1522_);
v___x_1549_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__2);
lean_inc_ref_n(v_e_x27_1524_, 2);
lean_inc_ref(v_arg_1523_);
v___x_1550_ = l_Lean_mkApp4(v___x_1548_, v_arg_1523_, v_e_x27_1524_, v_a_1544_, v___x_1549_);
v___x_1551_ = lean_unsigned_to_nat(1u);
v___x_1552_ = lean_mk_empty_array_with_capacity(v___x_1551_);
lean_inc_ref(v___x_1552_);
v___x_1553_ = lean_array_push(v___x_1552_, v___x_1550_);
v___x_1554_ = l_Lean_Expr_betaRev(v_arg_1525_, v___x_1553_, v_a_1526_, v_a_1526_);
lean_dec_ref(v___x_1553_);
v___x_1555_ = l_Lean_mkLambda(v___x_1545_, v___x_1546_, v_e_x27_1524_, v___x_1554_);
v___x_1556_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1555_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1556_, 1);
lean_inc_ref_n(v_e_x27_1524_, 2);
v___x_1558_ = l_Lean_mkNot(v_e_x27_1524_);
v___x_1559_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7));
v___x_1560_ = l_Lean_mkConst(v___x_1559_, v___x_1522_);
lean_inc(v_a_1544_);
v___x_1561_ = l_Lean_mkApp4(v___x_1560_, v_arg_1523_, v_e_x27_1524_, v_a_1544_, v___x_1549_);
v___x_1562_ = lean_array_push(v___x_1552_, v___x_1561_);
v___x_1563_ = l_Lean_Expr_betaRev(v_arg_1527_, v___x_1562_, v_a_1526_, v_a_1526_);
lean_dec_ref(v___x_1562_);
v___x_1564_ = l_Lean_mkLambda(v___x_1545_, v___x_1546_, v___x_1558_, v___x_1563_);
v___x_1565_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1564_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1567_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1565_, 1);
lean_inc_ref(v___x_1529_);
lean_inc_ref(v_e_x27_1524_);
v___x_1567_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(v___x_1528_, v_e_x27_1524_, v___x_1529_, v_a_1557_, v_a_1566_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1579_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1570_ = v___x_1567_;
v_isShared_1571_ = v_isSharedCheck_1579_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1567_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1579_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1577_; 
v___x_1572_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__4));
v___x_1573_ = l_Lean_Expr_replaceFn(v_e_1530_, v___x_1572_);
v___x_1574_ = l_Lean_mkApp3(v___x_1573_, v_e_x27_1524_, v___x_1529_, v_a_1544_);
v___x_1575_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1575_, 0, v_a_1568_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
lean_ctor_set_uint8(v___x_1575_, sizeof(void*)*2, v___x_1531_);
lean_ctor_set_uint8(v___x_1575_, sizeof(void*)*2 + 1, v_contextDependent_1532_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v___x_1575_);
v___x_1577_ = v___x_1570_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec(v_a_1544_);
lean_dec_ref(v_e_1530_);
lean_dec_ref(v___x_1529_);
lean_dec_ref(v_e_x27_1524_);
v_a_1580_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1567_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1567_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
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
lean_dec(v_a_1557_);
lean_dec(v_a_1544_);
lean_dec_ref(v_e_1530_);
lean_dec_ref(v___x_1529_);
lean_dec_ref(v___x_1528_);
lean_dec_ref(v_e_x27_1524_);
v_a_1588_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1565_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1565_);
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
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec_ref(v___x_1552_);
lean_dec(v_a_1544_);
lean_dec_ref(v_e_1530_);
lean_dec_ref(v___x_1529_);
lean_dec_ref(v___x_1528_);
lean_dec_ref(v_arg_1527_);
lean_dec_ref(v_e_x27_1524_);
lean_dec_ref(v_arg_1523_);
lean_dec(v___x_1522_);
v_a_1596_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1556_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1556_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_dec_ref(v_e_1530_);
lean_dec_ref(v___x_1529_);
lean_dec_ref(v___x_1528_);
lean_dec_ref(v_arg_1527_);
lean_dec_ref(v_arg_1525_);
lean_dec_ref(v_e_x27_1524_);
lean_dec_ref(v_arg_1523_);
lean_dec(v___x_1522_);
v_a_1604_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1543_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1543_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___boxed(lean_object** _args){
lean_object* v_proof_1612_ = _args[0];
lean_object* v___x_1613_ = _args[1];
lean_object* v_arg_1614_ = _args[2];
lean_object* v_e_x27_1615_ = _args[3];
lean_object* v_arg_1616_ = _args[4];
lean_object* v_a_1617_ = _args[5];
lean_object* v_arg_1618_ = _args[6];
lean_object* v___x_1619_ = _args[7];
lean_object* v___x_1620_ = _args[8];
lean_object* v_e_1621_ = _args[9];
lean_object* v___x_1622_ = _args[10];
lean_object* v_contextDependent_1623_ = _args[11];
lean_object* v___y_1624_ = _args[12];
lean_object* v___y_1625_ = _args[13];
lean_object* v___y_1626_ = _args[14];
lean_object* v___y_1627_ = _args[15];
lean_object* v___y_1628_ = _args[16];
lean_object* v___y_1629_ = _args[17];
lean_object* v___y_1630_ = _args[18];
lean_object* v___y_1631_ = _args[19];
lean_object* v___y_1632_ = _args[20];
lean_object* v___y_1633_ = _args[21];
_start:
{
uint8_t v_a_32592__boxed_1634_; uint8_t v___x_32596__boxed_1635_; uint8_t v_contextDependent_32597__boxed_1636_; lean_object* v_res_1637_; 
v_a_32592__boxed_1634_ = lean_unbox(v_a_1617_);
v___x_32596__boxed_1635_ = lean_unbox(v___x_1622_);
v_contextDependent_32597__boxed_1636_ = lean_unbox(v_contextDependent_1623_);
v_res_1637_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1(v_proof_1612_, v___x_1613_, v_arg_1614_, v_e_x27_1615_, v_arg_1616_, v_a_32592__boxed_1634_, v_arg_1618_, v___x_1619_, v___x_1620_, v_e_1621_, v___x_32596__boxed_1635_, v_contextDependent_32597__boxed_1636_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
return v_res_1637_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1644_ = lean_box(0);
v___x_1645_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
v___x_1646_ = l_Lean_mkConst(v___x_1645_, v___x_1644_);
return v___x_1646_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1647_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4);
v___x_1648_ = lean_unsigned_to_nat(1u);
v___x_1649_ = lean_mk_empty_array_with_capacity(v___x_1648_);
v___x_1650_ = lean_array_push(v___x_1649_, v___x_1647_);
return v___x_1650_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10(void){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1658_ = lean_box(0);
v___x_1659_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9));
v___x_1660_ = l_Lean_mkConst(v___x_1659_, v___x_1658_);
return v___x_1660_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11(void){
_start:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1661_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10);
v___x_1662_ = lean_unsigned_to_nat(1u);
v___x_1663_ = lean_mk_empty_array_with_capacity(v___x_1662_);
v___x_1664_ = lean_array_push(v___x_1663_, v___x_1661_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0(uint8_t v___x_1673_, lean_object* v_e_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v___x_1688_; uint8_t v___x_1689_; 
lean_inc_ref(v_e_1674_);
v___x_1688_ = l_Lean_Expr_cleanupAnnotations(v_e_1674_);
v___x_1689_ = l_Lean_Expr_isApp(v___x_1688_);
if (v___x_1689_ == 0)
{
lean_dec_ref(v___x_1688_);
lean_dec_ref(v_e_1674_);
goto v___jp_1685_;
}
else
{
lean_object* v_arg_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; 
v_arg_1690_ = lean_ctor_get(v___x_1688_, 1);
lean_inc_ref(v_arg_1690_);
v___x_1691_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1688_);
v___x_1692_ = l_Lean_Expr_isApp(v___x_1691_);
if (v___x_1692_ == 0)
{
lean_dec_ref(v___x_1691_);
lean_dec_ref(v_arg_1690_);
lean_dec_ref(v_e_1674_);
goto v___jp_1685_;
}
else
{
lean_object* v_arg_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; 
v_arg_1693_ = lean_ctor_get(v___x_1691_, 1);
lean_inc_ref(v_arg_1693_);
v___x_1694_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1691_);
v___x_1695_ = l_Lean_Expr_isApp(v___x_1694_);
if (v___x_1695_ == 0)
{
lean_dec_ref(v___x_1694_);
lean_dec_ref(v_arg_1693_);
lean_dec_ref(v_arg_1690_);
lean_dec_ref(v_e_1674_);
goto v___jp_1685_;
}
else
{
lean_object* v_arg_1696_; lean_object* v___x_1697_; uint8_t v___x_1698_; 
v_arg_1696_ = lean_ctor_get(v___x_1694_, 1);
lean_inc_ref(v_arg_1696_);
v___x_1697_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1694_);
v___x_1698_ = l_Lean_Expr_isApp(v___x_1697_);
if (v___x_1698_ == 0)
{
lean_dec_ref(v___x_1697_);
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1693_);
lean_dec_ref(v_arg_1690_);
lean_dec_ref(v_e_1674_);
goto v___jp_1685_;
}
else
{
lean_object* v_arg_1699_; lean_object* v___x_1700_; uint8_t v___x_1701_; 
v_arg_1699_ = lean_ctor_get(v___x_1697_, 1);
lean_inc_ref(v_arg_1699_);
v___x_1700_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1697_);
v___x_1701_ = l_Lean_Expr_isApp(v___x_1700_);
if (v___x_1701_ == 0)
{
lean_dec_ref(v___x_1700_);
lean_dec_ref(v_arg_1699_);
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1693_);
lean_dec_ref(v_arg_1690_);
lean_dec_ref(v_e_1674_);
goto v___jp_1685_;
}
else
{
lean_object* v_arg_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; 
v_arg_1702_ = lean_ctor_get(v___x_1700_, 1);
lean_inc_ref(v_arg_1702_);
v___x_1703_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1700_);
v___x_1704_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1));
v___x_1705_ = l_Lean_Expr_isConstOf(v___x_1703_, v___x_1704_);
if (v___x_1705_ == 0)
{
lean_dec_ref(v___x_1703_);
lean_dec_ref(v_arg_1702_);
lean_dec_ref(v_arg_1699_);
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1693_);
lean_dec_ref(v_arg_1690_);
lean_dec_ref(v_e_1674_);
goto v___jp_1685_;
}
else
{
lean_object* v___x_1706_; 
lean_inc(v___y_1683_);
lean_inc_ref(v___y_1682_);
lean_inc(v___y_1681_);
lean_inc_ref(v___y_1680_);
lean_inc(v___y_1679_);
lean_inc_ref(v___y_1678_);
lean_inc(v___y_1677_);
lean_inc_ref(v___y_1676_);
lean_inc(v___y_1675_);
lean_inc_ref(v_arg_1699_);
v___x_1706_ = lean_sym_simp(v_arg_1699_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_a_1707_);
lean_dec_ref_known(v___x_1706_, 1);
if (lean_obj_tag(v_a_1707_) == 0)
{
uint8_t v_contextDependent_1708_; lean_object* v___x_1709_; 
lean_dec_ref(v_e_1674_);
v_contextDependent_1708_ = lean_ctor_get_uint8(v_a_1707_, 1);
lean_dec_ref_known(v_a_1707_, 0);
v___x_1709_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_1699_, v___y_1678_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; uint8_t v___x_1711_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_a_1710_);
lean_dec_ref_known(v___x_1709_, 1);
v___x_1711_ = lean_unbox(v_a_1710_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; 
v___x_1712_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_1699_, v___y_1678_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; uint8_t v___x_1714_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1713_);
lean_dec_ref_known(v___x_1712_, 1);
v___x_1714_ = lean_unbox(v_a_1713_);
lean_dec(v_a_1713_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; lean_object* v___f_1716_; lean_object* v___x_1717_; 
lean_dec(v_a_1710_);
v___x_1715_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_1705_, v_contextDependent_1708_);
v___f_1716_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1716_, 0, v___x_1715_);
v___x_1717_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(v___x_1703_, v_arg_1702_, v_arg_1699_, v_arg_1696_, v_arg_1693_, v_arg_1690_, v___f_1716_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec_ref(v___x_1703_);
return v___x_1717_;
}
else
{
lean_object* v___x_1718_; uint8_t v___x_1719_; uint8_t v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
lean_dec_ref(v_arg_1699_);
lean_dec_ref(v_arg_1696_);
v___x_1718_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5);
v___x_1719_ = lean_unbox(v_a_1710_);
v___x_1720_ = lean_unbox(v_a_1710_);
lean_inc_ref(v_arg_1690_);
v___x_1721_ = l_Lean_Expr_betaRev(v_arg_1690_, v___x_1718_, v___x_1719_, v___x_1720_);
v___x_1722_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1721_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1736_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1725_ = v___x_1722_;
v_isShared_1726_ = v_isSharedCheck_1736_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1722_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1736_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; uint8_t v___x_1732_; lean_object* v___x_1734_; 
v___x_1727_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6));
v___x_1728_ = l_Lean_Expr_constLevels_x21(v___x_1703_);
lean_dec_ref(v___x_1703_);
v___x_1729_ = l_Lean_mkConst(v___x_1727_, v___x_1728_);
v___x_1730_ = l_Lean_mkApp3(v___x_1729_, v_arg_1702_, v_arg_1693_, v_arg_1690_);
v___x_1731_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1731_, 0, v_a_1723_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
v___x_1732_ = lean_unbox(v_a_1710_);
lean_dec(v_a_1710_);
lean_ctor_set_uint8(v___x_1731_, sizeof(void*)*2, v___x_1732_);
lean_ctor_set_uint8(v___x_1731_, sizeof(void*)*2 + 1, v_contextDependent_1708_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1731_);
v___x_1734_ = v___x_1725_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1731_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
lean_dec(v_a_1710_);
lean_dec_ref(v___x_1703_);
lean_dec_ref(v_arg_1702_);
lean_dec_ref(v_arg_1693_);
lean_dec_ref(v_arg_1690_);
v_a_1737_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1722_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1722_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
lean_dec(v_a_1710_);
lean_dec_ref(v___x_1703_);
lean_dec_ref(v_arg_1702_);
lean_dec_ref(v_arg_1699_);
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1693_);
lean_dec_ref(v_arg_1690_);
v_a_1745_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1712_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1712_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
lean_dec(v_a_1710_);
lean_dec_ref(v_arg_1699_);
lean_dec_ref(v_arg_1696_);
v___x_1753_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11);
lean_inc_ref(v_arg_1693_);
v___x_1754_ = l_Lean_Expr_betaRev(v_arg_1693_, v___x_1753_, v___x_1673_, v___x_1673_);
v___x_1755_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1754_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1768_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1768_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1768_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1766_; 
v___x_1760_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12));
v___x_1761_ = l_Lean_Expr_constLevels_x21(v___x_1703_);
lean_dec_ref(v___x_1703_);
v___x_1762_ = l_Lean_mkConst(v___x_1760_, v___x_1761_);
v___x_1763_ = l_Lean_mkApp3(v___x_1762_, v_arg_1702_, v_arg_1693_, v_arg_1690_);
v___x_1764_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1764_, 0, v_a_1756_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
lean_ctor_set_uint8(v___x_1764_, sizeof(void*)*2, v___x_1673_);
lean_ctor_set_uint8(v___x_1764_, sizeof(void*)*2 + 1, v_contextDependent_1708_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1764_);
v___x_1766_ = v___x_1758_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_dec_ref(v___x_1703_);
lean_dec_ref(v_arg_1702_);
lean_dec_ref(v_arg_1693_);
lean_dec_ref(v_arg_1690_);
v_a_1769_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1755_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1755_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
}
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
lean_dec_ref(v___x_1703_);
lean_dec_ref(v_arg_1702_);
lean_dec_ref(v_arg_1699_);
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1693_);
lean_dec_ref(v_arg_1690_);
v_a_1777_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1709_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1709_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
else
{
lean_object* v_e_x27_1785_; lean_object* v_proof_1786_; uint8_t v_contextDependent_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1902_; 
v_e_x27_1785_ = lean_ctor_get(v_a_1707_, 0);
v_proof_1786_ = lean_ctor_get(v_a_1707_, 1);
v_contextDependent_1787_ = lean_ctor_get_uint8(v_a_1707_, sizeof(void*)*2 + 1);
v_isSharedCheck_1902_ = !lean_is_exclusive(v_a_1707_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1789_ = v_a_1707_;
v_isShared_1790_ = v_isSharedCheck_1902_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_proof_1786_);
lean_inc(v_e_x27_1785_);
lean_dec(v_a_1707_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1902_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_1785_, v___y_1678_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; uint8_t v___x_1793_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_a_1792_);
lean_dec_ref_known(v___x_1791_, 1);
v___x_1793_ = lean_unbox(v_a_1792_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_1785_, v___y_1678_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; uint8_t v___x_1796_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
lean_inc(v_a_1795_);
lean_dec_ref_known(v___x_1794_, 1);
v___x_1796_ = lean_unbox(v_a_1795_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___f_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
lean_dec(v_a_1792_);
lean_del_object(v___x_1789_);
v___x_1797_ = lean_box(0);
v___x_1798_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6);
lean_inc_ref_n(v_proof_1786_, 2);
lean_inc_ref_n(v_arg_1696_, 2);
lean_inc_ref_n(v_e_x27_1785_, 2);
lean_inc_ref_n(v_arg_1699_, 3);
v___x_1799_ = l_Lean_mkApp4(v___x_1798_, v_arg_1699_, v_e_x27_1785_, v_arg_1696_, v_proof_1786_);
v___x_1800_ = lean_unsigned_to_nat(4u);
v___x_1801_ = l_Lean_Expr_getBoundedAppFn(v___x_1800_, v_e_1674_);
v___x_1802_ = lean_box(v___x_1705_);
v___x_1803_ = lean_box(v_contextDependent_1787_);
lean_inc_ref(v___x_1799_);
lean_inc_ref_n(v_arg_1690_, 2);
lean_inc_ref_n(v_arg_1693_, 2);
v___f_1804_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___boxed), 22, 12);
lean_closure_set(v___f_1804_, 0, v_proof_1786_);
lean_closure_set(v___f_1804_, 1, v___x_1797_);
lean_closure_set(v___f_1804_, 2, v_arg_1699_);
lean_closure_set(v___f_1804_, 3, v_e_x27_1785_);
lean_closure_set(v___f_1804_, 4, v_arg_1693_);
lean_closure_set(v___f_1804_, 5, v_a_1795_);
lean_closure_set(v___f_1804_, 6, v_arg_1690_);
lean_closure_set(v___f_1804_, 7, v___x_1801_);
lean_closure_set(v___f_1804_, 8, v___x_1799_);
lean_closure_set(v___f_1804_, 9, v_e_1674_);
lean_closure_set(v___f_1804_, 10, v___x_1802_);
lean_closure_set(v___f_1804_, 11, v___x_1803_);
lean_inc_ref(v_arg_1702_);
lean_inc_ref(v___x_1703_);
v___x_1805_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr___boxed), 20, 10);
lean_closure_set(v___x_1805_, 0, v___x_1703_);
lean_closure_set(v___x_1805_, 1, v_arg_1702_);
lean_closure_set(v___x_1805_, 2, v_arg_1699_);
lean_closure_set(v___x_1805_, 3, v_arg_1696_);
lean_closure_set(v___x_1805_, 4, v_arg_1693_);
lean_closure_set(v___x_1805_, 5, v_arg_1690_);
lean_closure_set(v___x_1805_, 6, v_e_x27_1785_);
lean_closure_set(v___x_1805_, 7, v_proof_1786_);
lean_closure_set(v___x_1805_, 8, v___x_1799_);
lean_closure_set(v___x_1805_, 9, v___f_1804_);
v___x_1806_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(v___x_1703_, v_arg_1702_, v_arg_1699_, v_arg_1696_, v_arg_1693_, v_arg_1690_, v___x_1805_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec_ref(v___x_1703_);
return v___x_1806_;
}
else
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
lean_dec(v_a_1795_);
lean_dec_ref(v_e_x27_1785_);
lean_dec_ref(v___x_1703_);
lean_dec_ref(v_arg_1702_);
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1693_);
lean_inc_ref(v_proof_1786_);
v___x_1807_ = l_Lean_Meta_mkOfEqFalseCore(v_arg_1699_, v_proof_1786_);
v___x_1808_ = l_Lean_Meta_Sym_shareCommon(v___x_1807_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; uint8_t v___x_1813_; uint8_t v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
lean_dec_ref_known(v___x_1808_, 1);
v___x_1810_ = lean_unsigned_to_nat(1u);
v___x_1811_ = lean_mk_empty_array_with_capacity(v___x_1810_);
v___x_1812_ = lean_array_push(v___x_1811_, v_a_1809_);
v___x_1813_ = lean_unbox(v_a_1792_);
v___x_1814_ = lean_unbox(v_a_1792_);
v___x_1815_ = l_Lean_Expr_betaRev(v_arg_1690_, v___x_1812_, v___x_1813_, v___x_1814_);
lean_dec_ref(v___x_1812_);
v___x_1816_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1815_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1831_; 
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1819_ = v___x_1816_;
v_isShared_1820_ = v_isSharedCheck_1831_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1816_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1831_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1825_; 
v___x_1821_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14));
v___x_1822_ = l_Lean_Expr_replaceFn(v_e_1674_, v___x_1821_);
v___x_1823_ = l_Lean_Expr_app___override(v___x_1822_, v_proof_1786_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 1, v___x_1823_);
lean_ctor_set(v___x_1789_, 0, v_a_1817_);
v___x_1825_ = v___x_1789_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1817_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
uint8_t v___x_1826_; lean_object* v___x_1828_; 
v___x_1826_ = lean_unbox(v_a_1792_);
lean_dec(v_a_1792_);
lean_ctor_set_uint8(v___x_1825_, sizeof(void*)*2, v___x_1826_);
lean_ctor_set_uint8(v___x_1825_, sizeof(void*)*2 + 1, v_contextDependent_1787_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___x_1825_);
v___x_1828_ = v___x_1819_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1825_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_dec(v_a_1792_);
lean_del_object(v___x_1789_);
lean_dec_ref(v_proof_1786_);
lean_dec_ref(v_e_1674_);
v_a_1832_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1816_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1816_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
lean_dec(v_a_1792_);
lean_del_object(v___x_1789_);
lean_dec_ref(v_proof_1786_);
lean_dec_ref(v_arg_1690_);
lean_dec_ref(v_e_1674_);
v_a_1840_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1808_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1808_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
}
else
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
lean_dec(v_a_1792_);
lean_del_object(v___x_1789_);
lean_dec_ref(v_proof_1786_);
lean_dec_ref(v_e_x27_1785_);
lean_dec_ref(v___x_1703_);
lean_dec_ref(v_arg_1702_);
lean_dec_ref(v_arg_1699_);
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1693_);
lean_dec_ref(v_arg_1690_);
lean_dec_ref(v_e_1674_);
v_a_1848_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1850_ = v___x_1794_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1794_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1848_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
else
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
lean_dec(v_a_1792_);
lean_dec_ref(v_e_x27_1785_);
lean_dec_ref(v___x_1703_);
lean_dec_ref(v_arg_1702_);
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1690_);
lean_inc_ref(v_proof_1786_);
v___x_1856_ = l_Lean_Meta_mkOfEqTrueCore(v_arg_1699_, v_proof_1786_);
v___x_1857_ = l_Lean_Meta_Sym_shareCommon(v___x_1856_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
lean_inc(v_a_1858_);
lean_dec_ref_known(v___x_1857_, 1);
v___x_1859_ = lean_unsigned_to_nat(1u);
v___x_1860_ = lean_mk_empty_array_with_capacity(v___x_1859_);
v___x_1861_ = lean_array_push(v___x_1860_, v_a_1858_);
v___x_1862_ = l_Lean_Expr_betaRev(v_arg_1693_, v___x_1861_, v___x_1673_, v___x_1673_);
lean_dec_ref(v___x_1861_);
v___x_1863_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1862_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1877_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1866_ = v___x_1863_;
v_isShared_1867_ = v_isSharedCheck_1877_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1863_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1877_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1872_; 
v___x_1868_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16));
v___x_1869_ = l_Lean_Expr_replaceFn(v_e_1674_, v___x_1868_);
v___x_1870_ = l_Lean_Expr_app___override(v___x_1869_, v_proof_1786_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 1, v___x_1870_);
lean_ctor_set(v___x_1789_, 0, v_a_1864_);
v___x_1872_ = v___x_1789_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1864_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v___x_1870_);
lean_ctor_set_uint8(v_reuseFailAlloc_1876_, sizeof(void*)*2 + 1, v_contextDependent_1787_);
v___x_1872_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
lean_object* v___x_1874_; 
lean_ctor_set_uint8(v___x_1872_, sizeof(void*)*2, v___x_1673_);
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 0, v___x_1872_);
v___x_1874_ = v___x_1866_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
lean_del_object(v___x_1789_);
lean_dec_ref(v_proof_1786_);
lean_dec_ref(v_e_1674_);
v_a_1878_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1880_ = v___x_1863_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1863_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
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
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
lean_del_object(v___x_1789_);
lean_dec_ref(v_proof_1786_);
lean_dec_ref(v_arg_1693_);
lean_dec_ref(v_e_1674_);
v_a_1886_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1857_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1857_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
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
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_del_object(v___x_1789_);
lean_dec_ref(v_proof_1786_);
lean_dec_ref(v_e_x27_1785_);
lean_dec_ref(v___x_1703_);
lean_dec_ref(v_arg_1702_);
lean_dec_ref(v_arg_1699_);
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1693_);
lean_dec_ref(v_arg_1690_);
lean_dec_ref(v_e_1674_);
v_a_1894_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1791_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1791_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1703_);
lean_dec_ref(v_arg_1702_);
lean_dec_ref(v_arg_1699_);
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1693_);
lean_dec_ref(v_arg_1690_);
lean_dec_ref(v_e_1674_);
return v___x_1706_;
}
}
}
}
}
}
}
v___jp_1685_:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1686_, 0, v___x_1673_);
lean_ctor_set_uint8(v___x_1686_, 1, v___x_1673_);
v___x_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
return v___x_1687_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___boxed(lean_object* v___x_1903_, lean_object* v_e_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
uint8_t v___x_32876__boxed_1915_; lean_object* v_res_1916_; 
v___x_32876__boxed_1915_ = lean_unbox(v___x_1903_);
v_res_1916_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0(v___x_32876__boxed_1915_, v_e_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
lean_dec_ref(v___y_1910_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv(lean_object* v_e_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_){
_start:
{
lean_object* v_numArgs_1928_; lean_object* v___x_1929_; uint8_t v___x_1930_; 
v_numArgs_1928_ = l_Lean_Expr_getAppNumArgs(v_e_1917_);
v___x_1929_ = lean_unsigned_to_nat(5u);
v___x_1930_ = lean_nat_dec_lt(v_numArgs_1928_, v___x_1929_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; lean_object* v___f_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1931_ = lean_box(v___x_1930_);
v___f_1932_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___boxed), 12, 1);
lean_closure_set(v___f_1932_, 0, v___x_1931_);
v___x_1933_ = lean_nat_sub(v_numArgs_1928_, v___x_1929_);
lean_dec(v_numArgs_1928_);
v___x_1934_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_1917_, v___x_1933_, v___f_1932_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
lean_dec(v___x_1933_);
return v___x_1934_;
}
else
{
uint8_t v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
lean_dec(v_numArgs_1928_);
lean_dec_ref(v_e_1917_);
v___x_1935_ = 0;
v___x_1936_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1936_, 0, v___x_1930_);
lean_ctor_set_uint8(v___x_1936_, 1, v___x_1935_);
v___x_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
return v___x_1937_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___boxed(lean_object* v_e_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv(v_e_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_);
lean_dec(v_a_1947_);
lean_dec_ref(v_a_1946_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
lean_dec(v_a_1939_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1968_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16_));
v___x_1969_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16_));
v___x_1970_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___boxed), 11, 0);
v___x_1971_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_1968_, v___x_1969_, v___x_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16____boxed(lean_object* v_a_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16_();
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_1975_; uint8_t v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1975_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16_));
v___x_1976_ = 0;
v___x_1977_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___boxed), 11, 0);
v___x_1978_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_1975_, v___x_1976_, v___x_1977_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_18____boxed(lean_object* v_a_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_18_();
return v_res_1980_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2(void){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1986_ = lean_box(0);
v___x_1987_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1));
v___x_1988_ = l_Lean_mkConst(v___x_1987_, v___x_1986_);
return v___x_1988_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5(void){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1994_ = lean_box(0);
v___x_1995_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4));
v___x_1996_ = l_Lean_mkConst(v___x_1995_, v___x_1994_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(lean_object* v_p_1997_, lean_object* v_inst_1998_, lean_object* v_instToMatch_1999_, lean_object* v_fallback_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_instToMatch_1999_, v_a_2007_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref_known(v___x_2011_, 1);
v___x_2013_ = l_Lean_Expr_cleanupAnnotations(v_a_2012_);
v___x_2014_ = l_Lean_Expr_isApp(v___x_2013_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; 
lean_dec_ref(v___x_2013_);
lean_dec_ref(v_inst_1998_);
lean_dec_ref(v_p_1997_);
lean_inc(v_a_2009_);
lean_inc_ref(v_a_2008_);
lean_inc(v_a_2007_);
lean_inc_ref(v_a_2006_);
lean_inc(v_a_2005_);
lean_inc_ref(v_a_2004_);
lean_inc(v_a_2003_);
lean_inc_ref(v_a_2002_);
lean_inc(v_a_2001_);
v___x_2015_ = lean_apply_10(v_fallback_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, lean_box(0));
return v___x_2015_;
}
else
{
lean_object* v_arg_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; 
v_arg_2016_ = lean_ctor_get(v___x_2013_, 1);
lean_inc_ref(v_arg_2016_);
v___x_2017_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2013_);
v___x_2018_ = l_Lean_Expr_isApp(v___x_2017_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; 
lean_dec_ref(v___x_2017_);
lean_dec_ref(v_arg_2016_);
lean_dec_ref(v_inst_1998_);
lean_dec_ref(v_p_1997_);
lean_inc(v_a_2009_);
lean_inc_ref(v_a_2008_);
lean_inc(v_a_2007_);
lean_inc_ref(v_a_2006_);
lean_inc(v_a_2005_);
lean_inc_ref(v_a_2004_);
lean_inc(v_a_2003_);
lean_inc_ref(v_a_2002_);
lean_inc(v_a_2001_);
v___x_2019_ = lean_apply_10(v_fallback_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, lean_box(0));
return v___x_2019_;
}
else
{
lean_object* v___x_2020_; lean_object* v___x_2021_; uint8_t v___x_2022_; 
v___x_2020_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2017_);
v___x_2021_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_2022_ = l_Lean_Expr_isConstOf(v___x_2020_, v___x_2021_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; uint8_t v___x_2024_; 
v___x_2023_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3));
v___x_2024_ = l_Lean_Expr_isConstOf(v___x_2020_, v___x_2023_);
lean_dec_ref(v___x_2020_);
if (v___x_2024_ == 0)
{
lean_object* v___x_2025_; 
lean_dec_ref(v_arg_2016_);
lean_dec_ref(v_inst_1998_);
lean_dec_ref(v_p_1997_);
lean_inc(v_a_2009_);
lean_inc_ref(v_a_2008_);
lean_inc(v_a_2007_);
lean_inc_ref(v_a_2006_);
lean_inc(v_a_2005_);
lean_inc_ref(v_a_2004_);
lean_inc(v_a_2003_);
lean_inc_ref(v_a_2002_);
lean_inc(v_a_2001_);
v___x_2025_ = lean_apply_10(v_fallback_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, lean_box(0));
return v___x_2025_;
}
else
{
lean_object* v___x_2026_; 
lean_dec_ref(v_fallback_2000_);
v___x_2026_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2004_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2037_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2029_ = v___x_2026_;
v_isShared_2030_ = v_isSharedCheck_2037_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2026_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2037_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2035_; 
v___x_2031_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2);
v___x_2032_ = l_Lean_mkApp3(v___x_2031_, v_p_1997_, v_inst_1998_, v_arg_2016_);
v___x_2033_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2033_, 0, v_a_2027_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
lean_ctor_set_uint8(v___x_2033_, sizeof(void*)*2, v___x_2022_);
lean_ctor_set_uint8(v___x_2033_, sizeof(void*)*2 + 1, v___x_2022_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 0, v___x_2033_);
v___x_2035_ = v___x_2029_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2033_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec_ref(v_arg_2016_);
lean_dec_ref(v_inst_1998_);
lean_dec_ref(v_p_1997_);
v_a_2038_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2026_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2026_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
else
{
lean_object* v___x_2046_; 
lean_dec_ref(v___x_2020_);
lean_dec_ref(v_fallback_2000_);
v___x_2046_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2004_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2058_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2049_ = v___x_2046_;
v_isShared_2050_ = v_isSharedCheck_2058_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2046_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2058_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2056_; 
v___x_2051_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5);
v___x_2052_ = l_Lean_mkApp3(v___x_2051_, v_p_1997_, v_inst_1998_, v_arg_2016_);
v___x_2053_ = 0;
v___x_2054_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2054_, 0, v_a_2047_);
lean_ctor_set(v___x_2054_, 1, v___x_2052_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*2, v___x_2053_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*2 + 1, v___x_2053_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2054_);
v___x_2056_ = v___x_2049_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec_ref(v_arg_2016_);
lean_dec_ref(v_inst_1998_);
lean_dec_ref(v_p_1997_);
v_a_2059_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2046_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2046_);
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
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_dec_ref(v_fallback_2000_);
lean_dec_ref(v_inst_1998_);
lean_dec_ref(v_p_1997_);
v_a_2067_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2011_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2011_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___boxed(lean_object* v_p_2075_, lean_object* v_inst_2076_, lean_object* v_instToMatch_2077_, lean_object* v_fallback_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(v_p_2075_, v_inst_2076_, v_instToMatch_2077_, v_fallback_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
lean_dec(v_a_2087_);
lean_dec_ref(v_a_2086_);
lean_dec(v_a_2085_);
lean_dec_ref(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
lean_dec(v_a_2079_);
return v_res_2089_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2(void){
_start:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2095_ = lean_box(0);
v___x_2096_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1));
v___x_2097_ = l_Lean_mkConst(v___x_2096_, v___x_2095_);
return v___x_2097_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5(void){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2103_ = lean_box(0);
v___x_2104_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4));
v___x_2105_ = l_Lean_mkConst(v___x_2104_, v___x_2103_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(lean_object* v_p_2106_, lean_object* v_p_x27_2107_, lean_object* v_h_2108_, lean_object* v_inst_2109_, lean_object* v_inst_x27_2110_, lean_object* v_fallback_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_inst_x27_2110_, v_a_2118_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2122_, 1);
v___x_2124_ = l_Lean_Expr_cleanupAnnotations(v_a_2123_);
v___x_2125_ = l_Lean_Expr_isApp(v___x_2124_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; 
lean_dec_ref(v___x_2124_);
lean_dec_ref(v_inst_2109_);
lean_dec_ref(v_h_2108_);
lean_dec_ref(v_p_x27_2107_);
lean_dec_ref(v_p_2106_);
lean_inc(v_a_2120_);
lean_inc_ref(v_a_2119_);
lean_inc(v_a_2118_);
lean_inc_ref(v_a_2117_);
lean_inc(v_a_2116_);
lean_inc_ref(v_a_2115_);
lean_inc(v_a_2114_);
lean_inc_ref(v_a_2113_);
lean_inc(v_a_2112_);
v___x_2126_ = lean_apply_10(v_fallback_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, lean_box(0));
return v___x_2126_;
}
else
{
lean_object* v_arg_2127_; lean_object* v___x_2128_; uint8_t v___x_2129_; 
v_arg_2127_ = lean_ctor_get(v___x_2124_, 1);
lean_inc_ref(v_arg_2127_);
v___x_2128_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2124_);
v___x_2129_ = l_Lean_Expr_isApp(v___x_2128_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2130_; 
lean_dec_ref(v___x_2128_);
lean_dec_ref(v_arg_2127_);
lean_dec_ref(v_inst_2109_);
lean_dec_ref(v_h_2108_);
lean_dec_ref(v_p_x27_2107_);
lean_dec_ref(v_p_2106_);
lean_inc(v_a_2120_);
lean_inc_ref(v_a_2119_);
lean_inc(v_a_2118_);
lean_inc_ref(v_a_2117_);
lean_inc(v_a_2116_);
lean_inc_ref(v_a_2115_);
lean_inc(v_a_2114_);
lean_inc_ref(v_a_2113_);
lean_inc(v_a_2112_);
v___x_2130_ = lean_apply_10(v_fallback_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, lean_box(0));
return v___x_2130_;
}
else
{
lean_object* v___x_2131_; lean_object* v___x_2132_; uint8_t v___x_2133_; 
v___x_2131_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2128_);
v___x_2132_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_2133_ = l_Lean_Expr_isConstOf(v___x_2131_, v___x_2132_);
if (v___x_2133_ == 0)
{
lean_object* v___x_2134_; uint8_t v___x_2135_; 
v___x_2134_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3));
v___x_2135_ = l_Lean_Expr_isConstOf(v___x_2131_, v___x_2134_);
lean_dec_ref(v___x_2131_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; 
lean_dec_ref(v_arg_2127_);
lean_dec_ref(v_inst_2109_);
lean_dec_ref(v_h_2108_);
lean_dec_ref(v_p_x27_2107_);
lean_dec_ref(v_p_2106_);
lean_inc(v_a_2120_);
lean_inc_ref(v_a_2119_);
lean_inc(v_a_2118_);
lean_inc_ref(v_a_2117_);
lean_inc(v_a_2116_);
lean_inc_ref(v_a_2115_);
lean_inc(v_a_2114_);
lean_inc_ref(v_a_2113_);
lean_inc(v_a_2112_);
v___x_2136_ = lean_apply_10(v_fallback_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, lean_box(0));
return v___x_2136_;
}
else
{
lean_object* v___x_2137_; 
lean_dec_ref(v_fallback_2111_);
v___x_2137_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2115_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2148_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2140_ = v___x_2137_;
v_isShared_2141_ = v_isSharedCheck_2148_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2137_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2148_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2146_; 
v___x_2142_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2);
v___x_2143_ = l_Lean_mkApp5(v___x_2142_, v_p_2106_, v_p_x27_2107_, v_h_2108_, v_inst_2109_, v_arg_2127_);
v___x_2144_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2144_, 0, v_a_2138_);
lean_ctor_set(v___x_2144_, 1, v___x_2143_);
lean_ctor_set_uint8(v___x_2144_, sizeof(void*)*2, v___x_2133_);
lean_ctor_set_uint8(v___x_2144_, sizeof(void*)*2 + 1, v___x_2133_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v___x_2144_);
v___x_2146_ = v___x_2140_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2144_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
lean_dec_ref(v_arg_2127_);
lean_dec_ref(v_inst_2109_);
lean_dec_ref(v_h_2108_);
lean_dec_ref(v_p_x27_2107_);
lean_dec_ref(v_p_2106_);
v_a_2149_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2137_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2137_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
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
}
else
{
lean_object* v___x_2157_; 
lean_dec_ref(v___x_2131_);
lean_dec_ref(v_fallback_2111_);
v___x_2157_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2115_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2169_; 
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2160_ = v___x_2157_;
v_isShared_2161_ = v_isSharedCheck_2169_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2157_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2169_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; uint8_t v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2167_; 
v___x_2162_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5);
v___x_2163_ = l_Lean_mkApp5(v___x_2162_, v_p_2106_, v_p_x27_2107_, v_h_2108_, v_inst_2109_, v_arg_2127_);
v___x_2164_ = 0;
v___x_2165_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2165_, 0, v_a_2158_);
lean_ctor_set(v___x_2165_, 1, v___x_2163_);
lean_ctor_set_uint8(v___x_2165_, sizeof(void*)*2, v___x_2164_);
lean_ctor_set_uint8(v___x_2165_, sizeof(void*)*2 + 1, v___x_2164_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v___x_2165_);
v___x_2167_ = v___x_2160_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
lean_dec_ref(v_arg_2127_);
lean_dec_ref(v_inst_2109_);
lean_dec_ref(v_h_2108_);
lean_dec_ref(v_p_x27_2107_);
lean_dec_ref(v_p_2106_);
v_a_2170_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2157_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2157_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
lean_dec_ref(v_fallback_2111_);
lean_dec_ref(v_inst_2109_);
lean_dec_ref(v_h_2108_);
lean_dec_ref(v_p_x27_2107_);
lean_dec_ref(v_p_2106_);
v_a_2178_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2122_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2122_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___boxed(lean_object* v_p_2186_, lean_object* v_p_x27_2187_, lean_object* v_h_2188_, lean_object* v_inst_2189_, lean_object* v_inst_x27_2190_, lean_object* v_fallback_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(v_p_2186_, v_p_x27_2187_, v_h_2188_, v_inst_2189_, v_inst_x27_2190_, v_fallback_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_);
lean_dec(v_a_2200_);
lean_dec_ref(v_a_2199_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
lean_dec(v_a_2194_);
lean_dec_ref(v_a_2193_);
lean_dec(v_a_2192_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(lean_object* v_p_2203_, lean_object* v_inst_2204_, lean_object* v_fallback_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_){
_start:
{
lean_object* v___x_2216_; 
lean_inc(v_a_2214_);
lean_inc_ref(v_a_2213_);
lean_inc(v_a_2212_);
lean_inc_ref(v_a_2211_);
lean_inc(v_a_2210_);
lean_inc_ref(v_a_2209_);
lean_inc(v_a_2208_);
lean_inc_ref(v_a_2207_);
lean_inc(v_a_2206_);
lean_inc_ref(v_inst_2204_);
v___x_2216_ = lean_sym_simp(v_inst_2204_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_a_2217_);
lean_dec_ref_known(v___x_2216_, 1);
if (lean_obj_tag(v_a_2217_) == 0)
{
uint8_t v_contextDependent_2218_; lean_object* v___x_2219_; 
v_contextDependent_2218_ = lean_ctor_get_uint8(v_a_2217_, 1);
lean_dec_ref_known(v_a_2217_, 0);
lean_inc_ref(v_inst_2204_);
v___x_2219_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(v_p_2203_, v_inst_2204_, v_inst_2204_, v_fallback_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; uint8_t v___y_2222_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2220_);
if (v_contextDependent_2218_ == 0)
{
lean_dec(v_a_2220_);
return v___x_2219_;
}
else
{
if (lean_obj_tag(v_a_2220_) == 0)
{
uint8_t v_contextDependent_2232_; uint8_t v___x_2233_; 
v_contextDependent_2232_ = lean_ctor_get_uint8(v_a_2220_, 1);
v___x_2233_ = lean_bool_not(v_contextDependent_2232_);
v___y_2222_ = v___x_2233_;
goto v___jp_2221_;
}
else
{
uint8_t v_contextDependent_2234_; uint8_t v___x_2235_; 
v_contextDependent_2234_ = lean_ctor_get_uint8(v_a_2220_, sizeof(void*)*2 + 1);
v___x_2235_ = lean_bool_not(v_contextDependent_2234_);
v___y_2222_ = v___x_2235_;
goto v___jp_2221_;
}
}
v___jp_2221_:
{
if (v___y_2222_ == 0)
{
lean_dec(v_a_2220_);
return v___x_2219_;
}
else
{
lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2230_; 
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; 
v_unused_2231_ = lean_ctor_get(v___x_2219_, 0);
lean_dec(v_unused_2231_);
v___x_2224_ = v___x_2219_;
v_isShared_2225_ = v_isSharedCheck_2230_;
goto v_resetjp_2223_;
}
else
{
lean_dec(v___x_2219_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2230_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2226_; lean_object* v___x_2228_; 
v___x_2226_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2220_);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 0, v___x_2226_);
v___x_2228_ = v___x_2224_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2226_);
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
else
{
return v___x_2219_;
}
}
else
{
lean_object* v_e_x27_2236_; uint8_t v_contextDependent_2237_; lean_object* v___x_2238_; 
v_e_x27_2236_ = lean_ctor_get(v_a_2217_, 0);
lean_inc_ref(v_e_x27_2236_);
v_contextDependent_2237_ = lean_ctor_get_uint8(v_a_2217_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2217_, 2);
v___x_2238_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(v_p_2203_, v_inst_2204_, v_e_x27_2236_, v_fallback_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; uint8_t v___y_2241_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
if (v_contextDependent_2237_ == 0)
{
lean_dec(v_a_2239_);
return v___x_2238_;
}
else
{
if (lean_obj_tag(v_a_2239_) == 0)
{
uint8_t v_contextDependent_2251_; uint8_t v___x_2252_; 
v_contextDependent_2251_ = lean_ctor_get_uint8(v_a_2239_, 1);
v___x_2252_ = lean_bool_not(v_contextDependent_2251_);
v___y_2241_ = v___x_2252_;
goto v___jp_2240_;
}
else
{
uint8_t v_contextDependent_2253_; uint8_t v___x_2254_; 
v_contextDependent_2253_ = lean_ctor_get_uint8(v_a_2239_, sizeof(void*)*2 + 1);
v___x_2254_ = lean_bool_not(v_contextDependent_2253_);
v___y_2241_ = v___x_2254_;
goto v___jp_2240_;
}
}
v___jp_2240_:
{
if (v___y_2241_ == 0)
{
lean_dec(v_a_2239_);
return v___x_2238_;
}
else
{
lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2249_; 
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2249_ == 0)
{
lean_object* v_unused_2250_; 
v_unused_2250_ = lean_ctor_get(v___x_2238_, 0);
lean_dec(v_unused_2250_);
v___x_2243_ = v___x_2238_;
v_isShared_2244_ = v_isSharedCheck_2249_;
goto v_resetjp_2242_;
}
else
{
lean_dec(v___x_2238_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2249_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2247_; 
v___x_2245_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2239_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 0, v___x_2245_);
v___x_2247_ = v___x_2243_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2245_);
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
else
{
return v___x_2238_;
}
}
}
else
{
lean_dec_ref(v_fallback_2205_);
lean_dec_ref(v_inst_2204_);
lean_dec_ref(v_p_2203_);
return v___x_2216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable___boxed(lean_object* v_p_2255_, lean_object* v_inst_2256_, lean_object* v_fallback_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(v_p_2255_, v_inst_2256_, v_fallback_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
lean_dec(v_a_2266_);
lean_dec_ref(v_a_2265_);
lean_dec(v_a_2264_);
lean_dec_ref(v_a_2263_);
lean_dec(v_a_2262_);
lean_dec_ref(v_a_2261_);
lean_dec(v_a_2260_);
lean_dec_ref(v_a_2259_);
lean_dec(v_a_2258_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr(lean_object* v_p_2269_, lean_object* v_p_x27_2270_, lean_object* v_h_2271_, lean_object* v_inst_2272_, lean_object* v_inst_x27_2273_, lean_object* v_fallback_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v___x_2285_; 
lean_inc(v_a_2283_);
lean_inc_ref(v_a_2282_);
lean_inc(v_a_2281_);
lean_inc_ref(v_a_2280_);
lean_inc(v_a_2279_);
lean_inc_ref(v_a_2278_);
lean_inc(v_a_2277_);
lean_inc_ref(v_a_2276_);
lean_inc(v_a_2275_);
lean_inc_ref(v_inst_x27_2273_);
v___x_2285_ = lean_sym_simp(v_inst_x27_2273_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
lean_dec_ref_known(v___x_2285_, 1);
if (lean_obj_tag(v_a_2286_) == 0)
{
uint8_t v_contextDependent_2287_; lean_object* v___x_2288_; 
v_contextDependent_2287_ = lean_ctor_get_uint8(v_a_2286_, 1);
lean_dec_ref_known(v_a_2286_, 0);
v___x_2288_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(v_p_2269_, v_p_x27_2270_, v_h_2271_, v_inst_2272_, v_inst_x27_2273_, v_fallback_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; uint8_t v___y_2291_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_a_2289_);
if (v_contextDependent_2287_ == 0)
{
lean_dec(v_a_2289_);
return v___x_2288_;
}
else
{
if (lean_obj_tag(v_a_2289_) == 0)
{
uint8_t v_contextDependent_2301_; uint8_t v___x_2302_; 
v_contextDependent_2301_ = lean_ctor_get_uint8(v_a_2289_, 1);
v___x_2302_ = lean_bool_not(v_contextDependent_2301_);
v___y_2291_ = v___x_2302_;
goto v___jp_2290_;
}
else
{
uint8_t v_contextDependent_2303_; uint8_t v___x_2304_; 
v_contextDependent_2303_ = lean_ctor_get_uint8(v_a_2289_, sizeof(void*)*2 + 1);
v___x_2304_ = lean_bool_not(v_contextDependent_2303_);
v___y_2291_ = v___x_2304_;
goto v___jp_2290_;
}
}
v___jp_2290_:
{
if (v___y_2291_ == 0)
{
lean_dec(v_a_2289_);
return v___x_2288_;
}
else
{
lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2299_; 
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2299_ == 0)
{
lean_object* v_unused_2300_; 
v_unused_2300_ = lean_ctor_get(v___x_2288_, 0);
lean_dec(v_unused_2300_);
v___x_2293_ = v___x_2288_;
v_isShared_2294_ = v_isSharedCheck_2299_;
goto v_resetjp_2292_;
}
else
{
lean_dec(v___x_2288_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2299_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2295_; lean_object* v___x_2297_; 
v___x_2295_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2289_);
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 0, v___x_2295_);
v___x_2297_ = v___x_2293_;
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
}
else
{
return v___x_2288_;
}
}
else
{
lean_object* v_e_x27_2305_; uint8_t v_contextDependent_2306_; lean_object* v___x_2307_; 
lean_dec_ref(v_inst_x27_2273_);
v_e_x27_2305_ = lean_ctor_get(v_a_2286_, 0);
lean_inc_ref(v_e_x27_2305_);
v_contextDependent_2306_ = lean_ctor_get_uint8(v_a_2286_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2286_, 2);
v___x_2307_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(v_p_2269_, v_p_x27_2270_, v_h_2271_, v_inst_2272_, v_e_x27_2305_, v_fallback_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; uint8_t v___y_2310_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2308_);
if (v_contextDependent_2306_ == 0)
{
lean_dec(v_a_2308_);
return v___x_2307_;
}
else
{
if (lean_obj_tag(v_a_2308_) == 0)
{
uint8_t v_contextDependent_2320_; uint8_t v___x_2321_; 
v_contextDependent_2320_ = lean_ctor_get_uint8(v_a_2308_, 1);
v___x_2321_ = lean_bool_not(v_contextDependent_2320_);
v___y_2310_ = v___x_2321_;
goto v___jp_2309_;
}
else
{
uint8_t v_contextDependent_2322_; uint8_t v___x_2323_; 
v_contextDependent_2322_ = lean_ctor_get_uint8(v_a_2308_, sizeof(void*)*2 + 1);
v___x_2323_ = lean_bool_not(v_contextDependent_2322_);
v___y_2310_ = v___x_2323_;
goto v___jp_2309_;
}
}
v___jp_2309_:
{
if (v___y_2310_ == 0)
{
lean_dec(v_a_2308_);
return v___x_2307_;
}
else
{
lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2318_; 
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2318_ == 0)
{
lean_object* v_unused_2319_; 
v_unused_2319_ = lean_ctor_get(v___x_2307_, 0);
lean_dec(v_unused_2319_);
v___x_2312_ = v___x_2307_;
v_isShared_2313_ = v_isSharedCheck_2318_;
goto v_resetjp_2311_;
}
else
{
lean_dec(v___x_2307_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2318_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2314_; lean_object* v___x_2316_; 
v___x_2314_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2308_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 0, v___x_2314_);
v___x_2316_ = v___x_2312_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v___x_2314_);
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
else
{
return v___x_2307_;
}
}
}
else
{
lean_dec_ref(v_fallback_2274_);
lean_dec_ref(v_inst_x27_2273_);
lean_dec_ref(v_inst_2272_);
lean_dec_ref(v_h_2271_);
lean_dec_ref(v_p_x27_2270_);
lean_dec_ref(v_p_2269_);
return v___x_2285_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___boxed(lean_object* v_p_2324_, lean_object* v_p_x27_2325_, lean_object* v_h_2326_, lean_object* v_inst_2327_, lean_object* v_inst_x27_2328_, lean_object* v_fallback_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr(v_p_2324_, v_p_x27_2325_, v_h_2326_, v_inst_2327_, v_inst_x27_2328_, v_fallback_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v_a_2338_);
lean_dec_ref(v_a_2337_);
lean_dec(v_a_2336_);
lean_dec_ref(v_a_2335_);
lean_dec(v_a_2334_);
lean_dec_ref(v_a_2333_);
lean_dec(v_a_2332_);
lean_dec_ref(v_a_2331_);
lean_dec(v_a_2330_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1(lean_object* v___x_2342_, lean_object* v_e_x27_2343_, lean_object* v___y_2344_, lean_object* v___x_2345_, lean_object* v___x_2346_, lean_object* v___x_2347_, lean_object* v_arg_2348_, lean_object* v_proof_2349_, lean_object* v_arg_2350_, uint8_t v___x_2351_, uint8_t v_contextDependent_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Lean_Meta_Sym_shareCommon(v___x_2342_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; lean_object* v___x_2365_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2364_);
lean_dec_ref_known(v___x_2363_, 1);
lean_inc_ref(v___y_2344_);
lean_inc_ref(v_e_x27_2343_);
v___x_2365_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1(v_a_2364_, v_e_x27_2343_, v___y_2344_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2378_; 
v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2368_ = v___x_2365_;
v_isShared_2369_ = v_isSharedCheck_2378_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2365_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2378_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2376_; 
v___x_2370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1___closed__0));
v___x_2371_ = l_Lean_Name_mkStr3(v___x_2345_, v___x_2346_, v___x_2370_);
v___x_2372_ = l_Lean_mkConst(v___x_2371_, v___x_2347_);
v___x_2373_ = l_Lean_mkApp5(v___x_2372_, v_arg_2348_, v_e_x27_2343_, v_proof_2349_, v_arg_2350_, v___y_2344_);
v___x_2374_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2374_, 0, v_a_2366_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
lean_ctor_set_uint8(v___x_2374_, sizeof(void*)*2, v___x_2351_);
lean_ctor_set_uint8(v___x_2374_, sizeof(void*)*2 + 1, v_contextDependent_2352_);
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 0, v___x_2374_);
v___x_2376_ = v___x_2368_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2374_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
lean_dec_ref(v_arg_2350_);
lean_dec_ref(v_proof_2349_);
lean_dec_ref(v_arg_2348_);
lean_dec(v___x_2347_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___x_2345_);
lean_dec_ref(v___y_2344_);
lean_dec_ref(v_e_x27_2343_);
v_a_2379_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2365_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2365_);
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
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
lean_dec_ref(v_arg_2350_);
lean_dec_ref(v_proof_2349_);
lean_dec_ref(v_arg_2348_);
lean_dec(v___x_2347_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___x_2345_);
lean_dec_ref(v___y_2344_);
lean_dec_ref(v_e_x27_2343_);
v_a_2387_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2363_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2363_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1___boxed(lean_object** _args){
lean_object* v___x_2395_ = _args[0];
lean_object* v_e_x27_2396_ = _args[1];
lean_object* v___y_2397_ = _args[2];
lean_object* v___x_2398_ = _args[3];
lean_object* v___x_2399_ = _args[4];
lean_object* v___x_2400_ = _args[5];
lean_object* v_arg_2401_ = _args[6];
lean_object* v_proof_2402_ = _args[7];
lean_object* v_arg_2403_ = _args[8];
lean_object* v___x_2404_ = _args[9];
lean_object* v_contextDependent_2405_ = _args[10];
lean_object* v___y_2406_ = _args[11];
lean_object* v___y_2407_ = _args[12];
lean_object* v___y_2408_ = _args[13];
lean_object* v___y_2409_ = _args[14];
lean_object* v___y_2410_ = _args[15];
lean_object* v___y_2411_ = _args[16];
lean_object* v___y_2412_ = _args[17];
lean_object* v___y_2413_ = _args[18];
lean_object* v___y_2414_ = _args[19];
lean_object* v___y_2415_ = _args[20];
_start:
{
uint8_t v___x_23749__boxed_2416_; uint8_t v_contextDependent_23750__boxed_2417_; lean_object* v_res_2418_; 
v___x_23749__boxed_2416_ = lean_unbox(v___x_2404_);
v_contextDependent_23750__boxed_2417_ = lean_unbox(v_contextDependent_2405_);
v_res_2418_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1(v___x_2395_, v_e_x27_2396_, v___y_2397_, v___x_2398_, v___x_2399_, v___x_2400_, v_arg_2401_, v_proof_2402_, v_arg_2403_, v___x_23749__boxed_2416_, v_contextDependent_23750__boxed_2417_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
return v_res_2418_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2426_ = lean_box(0);
v___x_2427_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__3));
v___x_2428_ = l_Lean_mkConst(v___x_2427_, v___x_2426_);
return v___x_2428_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2432_ = lean_box(0);
v___x_2433_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__6));
v___x_2434_ = l_Lean_mkConst(v___x_2433_, v___x_2432_);
return v___x_2434_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8(void){
_start:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2435_ = lean_box(0);
v___x_2436_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1));
v___x_2437_ = l_Lean_mkConst(v___x_2436_, v___x_2435_);
return v___x_2437_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11(void){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2443_ = lean_box(0);
v___x_2444_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10));
v___x_2445_ = l_Lean_mkConst(v___x_2444_, v___x_2443_);
return v___x_2445_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__14(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2451_ = lean_box(0);
v___x_2452_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__13));
v___x_2453_ = l_Lean_mkConst(v___x_2452_, v___x_2451_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0(uint8_t v___x_2454_, lean_object* v_e_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v___x_2469_; uint8_t v___x_2470_; 
v___x_2469_ = l_Lean_Expr_cleanupAnnotations(v_e_2455_);
v___x_2470_ = l_Lean_Expr_isApp(v___x_2469_);
if (v___x_2470_ == 0)
{
lean_dec_ref(v___x_2469_);
goto v___jp_2466_;
}
else
{
lean_object* v_arg_2471_; lean_object* v___x_2472_; uint8_t v___x_2473_; 
v_arg_2471_ = lean_ctor_get(v___x_2469_, 1);
lean_inc_ref(v_arg_2471_);
v___x_2472_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2469_);
v___x_2473_ = l_Lean_Expr_isApp(v___x_2472_);
if (v___x_2473_ == 0)
{
lean_dec_ref(v___x_2472_);
lean_dec_ref(v_arg_2471_);
goto v___jp_2466_;
}
else
{
lean_object* v_arg_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; uint8_t v___x_2479_; 
v_arg_2474_ = lean_ctor_get(v___x_2472_, 1);
lean_inc_ref(v_arg_2474_);
v___x_2475_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2472_);
v___x_2476_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__0));
v___x_2477_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__0));
v___x_2478_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1));
v___x_2479_ = l_Lean_Expr_isConstOf(v___x_2475_, v___x_2478_);
lean_dec_ref(v___x_2475_);
if (v___x_2479_ == 0)
{
lean_dec_ref(v_arg_2474_);
lean_dec_ref(v_arg_2471_);
goto v___jp_2466_;
}
else
{
lean_object* v___x_2480_; 
lean_inc(v___y_2464_);
lean_inc_ref(v___y_2463_);
lean_inc(v___y_2462_);
lean_inc_ref(v___y_2461_);
lean_inc(v___y_2460_);
lean_inc_ref(v___y_2459_);
lean_inc(v___y_2458_);
lean_inc_ref(v___y_2457_);
lean_inc(v___y_2456_);
lean_inc_ref(v_arg_2474_);
v___x_2480_ = lean_sym_simp(v_arg_2474_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v_a_2481_; 
v_a_2481_ = lean_ctor_get(v___x_2480_, 0);
lean_inc(v_a_2481_);
lean_dec_ref_known(v___x_2480_, 1);
if (lean_obj_tag(v_a_2481_) == 0)
{
uint8_t v_contextDependent_2482_; lean_object* v___x_2483_; 
v_contextDependent_2482_ = lean_ctor_get_uint8(v_a_2481_, 1);
lean_dec_ref_known(v_a_2481_, 0);
v___x_2483_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_2474_, v___y_2459_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; uint8_t v___x_2485_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_a_2484_);
lean_dec_ref_known(v___x_2483_, 1);
v___x_2485_ = lean_unbox(v_a_2484_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; 
v___x_2486_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_2474_, v___y_2459_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_a_2487_; uint8_t v___x_2488_; 
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_a_2487_);
lean_dec_ref_known(v___x_2486_, 1);
v___x_2488_ = lean_unbox(v_a_2487_);
lean_dec(v_a_2487_);
if (v___x_2488_ == 0)
{
lean_object* v___x_2489_; lean_object* v___f_2490_; lean_object* v___x_2491_; 
lean_dec(v_a_2484_);
v___x_2489_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_2479_, v_contextDependent_2482_);
v___f_2490_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2490_, 0, v___x_2489_);
v___x_2491_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(v_arg_2474_, v_arg_2471_, v___f_2490_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
return v___x_2491_;
}
else
{
lean_object* v___x_2492_; 
lean_dec_ref(v_arg_2474_);
v___x_2492_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v___y_2459_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2504_; 
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2495_ = v___x_2492_;
v_isShared_2496_ = v_isSharedCheck_2504_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2492_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2504_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; uint8_t v___x_2500_; lean_object* v___x_2502_; 
v___x_2497_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__4, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__4);
v___x_2498_ = l_Lean_Expr_app___override(v___x_2497_, v_arg_2471_);
v___x_2499_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2499_, 0, v_a_2493_);
lean_ctor_set(v___x_2499_, 1, v___x_2498_);
v___x_2500_ = lean_unbox(v_a_2484_);
lean_dec(v_a_2484_);
lean_ctor_set_uint8(v___x_2499_, sizeof(void*)*2, v___x_2500_);
lean_ctor_set_uint8(v___x_2499_, sizeof(void*)*2 + 1, v_contextDependent_2482_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 0, v___x_2499_);
v___x_2502_ = v___x_2495_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2499_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_dec(v_a_2484_);
lean_dec_ref(v_arg_2471_);
v_a_2505_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2492_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2492_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
lean_dec(v_a_2484_);
lean_dec_ref(v_arg_2474_);
lean_dec_ref(v_arg_2471_);
v_a_2513_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2486_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2486_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
else
{
lean_object* v___x_2521_; 
lean_dec(v_a_2484_);
lean_dec_ref(v_arg_2474_);
v___x_2521_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v___y_2459_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2532_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2524_ = v___x_2521_;
v_isShared_2525_ = v_isSharedCheck_2532_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2521_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2532_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2530_; 
v___x_2526_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7);
v___x_2527_ = l_Lean_Expr_app___override(v___x_2526_, v_arg_2471_);
v___x_2528_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2528_, 0, v_a_2522_);
lean_ctor_set(v___x_2528_, 1, v___x_2527_);
lean_ctor_set_uint8(v___x_2528_, sizeof(void*)*2, v___x_2454_);
lean_ctor_set_uint8(v___x_2528_, sizeof(void*)*2 + 1, v_contextDependent_2482_);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v___x_2528_);
v___x_2530_ = v___x_2524_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2528_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
lean_dec_ref(v_arg_2471_);
v_a_2533_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2521_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2521_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_dec_ref(v_arg_2474_);
lean_dec_ref(v_arg_2471_);
v_a_2541_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2483_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2483_);
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
else
{
lean_object* v_e_x27_2549_; lean_object* v_proof_2550_; uint8_t v_contextDependent_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2643_; 
v_e_x27_2549_ = lean_ctor_get(v_a_2481_, 0);
v_proof_2550_ = lean_ctor_get(v_a_2481_, 1);
v_contextDependent_2551_ = lean_ctor_get_uint8(v_a_2481_, sizeof(void*)*2 + 1);
v_isSharedCheck_2643_ = !lean_is_exclusive(v_a_2481_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2553_ = v_a_2481_;
v_isShared_2554_ = v_isSharedCheck_2643_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_proof_2550_);
lean_inc(v_e_x27_2549_);
lean_dec(v_a_2481_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2643_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2555_; 
v___x_2555_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_2549_, v___y_2459_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; uint8_t v___x_2557_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_a_2556_);
lean_dec_ref_known(v___x_2555_, 1);
v___x_2557_ = lean_unbox(v_a_2556_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2558_; 
v___x_2558_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_2549_, v___y_2459_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; uint8_t v___x_2560_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_a_2559_);
lean_dec_ref_known(v___x_2558_, 1);
v___x_2560_ = lean_unbox(v_a_2559_);
lean_dec(v_a_2559_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2561_; 
lean_dec(v_a_2556_);
lean_del_object(v___x_2553_);
lean_inc_ref(v_e_x27_2549_);
v___x_2561_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance(v_e_x27_2549_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; lean_object* v___y_2564_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_a_2562_);
lean_dec_ref_known(v___x_2561_, 1);
if (lean_obj_tag(v_a_2562_) == 0)
{
lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2571_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6);
lean_inc_ref(v_proof_2550_);
lean_inc_ref(v_arg_2471_);
lean_inc_ref(v_e_x27_2549_);
lean_inc_ref(v_arg_2474_);
v___x_2572_ = l_Lean_mkApp4(v___x_2571_, v_arg_2474_, v_e_x27_2549_, v_arg_2471_, v_proof_2550_);
v___y_2564_ = v___x_2572_;
goto v___jp_2563_;
}
else
{
lean_object* v_val_2573_; 
v_val_2573_ = lean_ctor_get(v_a_2562_, 0);
lean_inc(v_val_2573_);
lean_dec_ref_known(v_a_2562_, 1);
v___y_2564_ = v_val_2573_;
goto v___jp_2563_;
}
v___jp_2563_:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___f_2569_; lean_object* v___x_2570_; 
v___x_2565_ = lean_box(0);
v___x_2566_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8);
v___x_2567_ = lean_box(v___x_2479_);
v___x_2568_ = lean_box(v_contextDependent_2551_);
lean_inc_ref(v_arg_2471_);
lean_inc_ref(v_proof_2550_);
lean_inc_ref(v_arg_2474_);
lean_inc_ref(v___y_2564_);
lean_inc_ref(v_e_x27_2549_);
v___f_2569_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1___boxed), 21, 11);
lean_closure_set(v___f_2569_, 0, v___x_2566_);
lean_closure_set(v___f_2569_, 1, v_e_x27_2549_);
lean_closure_set(v___f_2569_, 2, v___y_2564_);
lean_closure_set(v___f_2569_, 3, v___x_2476_);
lean_closure_set(v___f_2569_, 4, v___x_2477_);
lean_closure_set(v___f_2569_, 5, v___x_2565_);
lean_closure_set(v___f_2569_, 6, v_arg_2474_);
lean_closure_set(v___f_2569_, 7, v_proof_2550_);
lean_closure_set(v___f_2569_, 8, v_arg_2471_);
lean_closure_set(v___f_2569_, 9, v___x_2567_);
lean_closure_set(v___f_2569_, 10, v___x_2568_);
v___x_2570_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr(v_arg_2474_, v_e_x27_2549_, v_proof_2550_, v_arg_2471_, v___y_2564_, v___f_2569_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
return v___x_2570_;
}
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
lean_dec_ref(v_proof_2550_);
lean_dec_ref(v_e_x27_2549_);
lean_dec_ref(v_arg_2474_);
lean_dec_ref(v_arg_2471_);
v_a_2574_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2561_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2561_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
else
{
lean_object* v___x_2582_; 
lean_dec_ref(v_e_x27_2549_);
v___x_2582_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v___y_2459_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2596_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2585_ = v___x_2582_;
v_isShared_2586_ = v_isSharedCheck_2596_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2582_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2596_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2590_; 
v___x_2587_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11);
v___x_2588_ = l_Lean_mkApp3(v___x_2587_, v_arg_2474_, v_arg_2471_, v_proof_2550_);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 1, v___x_2588_);
lean_ctor_set(v___x_2553_, 0, v_a_2583_);
v___x_2590_ = v___x_2553_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2583_);
lean_ctor_set(v_reuseFailAlloc_2595_, 1, v___x_2588_);
v___x_2590_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
uint8_t v___x_2591_; lean_object* v___x_2593_; 
v___x_2591_ = lean_unbox(v_a_2556_);
lean_dec(v_a_2556_);
lean_ctor_set_uint8(v___x_2590_, sizeof(void*)*2, v___x_2591_);
lean_ctor_set_uint8(v___x_2590_, sizeof(void*)*2 + 1, v_contextDependent_2551_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v___x_2590_);
v___x_2593_ = v___x_2585_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2590_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2604_; 
lean_dec(v_a_2556_);
lean_del_object(v___x_2553_);
lean_dec_ref(v_proof_2550_);
lean_dec_ref(v_arg_2474_);
lean_dec_ref(v_arg_2471_);
v_a_2597_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2599_ = v___x_2582_;
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2582_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2602_; 
if (v_isShared_2600_ == 0)
{
v___x_2602_ = v___x_2599_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2597_);
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
}
else
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
lean_dec(v_a_2556_);
lean_del_object(v___x_2553_);
lean_dec_ref(v_proof_2550_);
lean_dec_ref(v_e_x27_2549_);
lean_dec_ref(v_arg_2474_);
lean_dec_ref(v_arg_2471_);
v_a_2605_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___x_2558_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2558_);
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
else
{
lean_object* v___x_2613_; 
lean_dec(v_a_2556_);
lean_dec_ref(v_e_x27_2549_);
v___x_2613_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v___y_2459_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2626_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2616_ = v___x_2613_;
v_isShared_2617_ = v_isSharedCheck_2626_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2613_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2626_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2621_; 
v___x_2618_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__14, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__14_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__14);
v___x_2619_ = l_Lean_mkApp3(v___x_2618_, v_arg_2474_, v_arg_2471_, v_proof_2550_);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 1, v___x_2619_);
lean_ctor_set(v___x_2553_, 0, v_a_2614_);
v___x_2621_ = v___x_2553_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2614_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v___x_2619_);
lean_ctor_set_uint8(v_reuseFailAlloc_2625_, sizeof(void*)*2 + 1, v_contextDependent_2551_);
v___x_2621_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
lean_object* v___x_2623_; 
lean_ctor_set_uint8(v___x_2621_, sizeof(void*)*2, v___x_2454_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 0, v___x_2621_);
v___x_2623_ = v___x_2616_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2621_);
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
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_del_object(v___x_2553_);
lean_dec_ref(v_proof_2550_);
lean_dec_ref(v_arg_2474_);
lean_dec_ref(v_arg_2471_);
v_a_2627_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2613_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2613_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
}
else
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
lean_del_object(v___x_2553_);
lean_dec_ref(v_proof_2550_);
lean_dec_ref(v_e_x27_2549_);
lean_dec_ref(v_arg_2474_);
lean_dec_ref(v_arg_2471_);
v_a_2635_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2637_ = v___x_2555_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2555_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_arg_2474_);
lean_dec_ref(v_arg_2471_);
return v___x_2480_;
}
}
}
}
v___jp_2466_:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2467_, 0, v___x_2454_);
lean_ctor_set_uint8(v___x_2467_, 1, v___x_2454_);
v___x_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2467_);
return v___x_2468_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___boxed(lean_object* v___x_2644_, lean_object* v_e_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
uint8_t v___x_23949__boxed_2656_; lean_object* v_res_2657_; 
v___x_23949__boxed_2656_ = lean_unbox(v___x_2644_);
v_res_2657_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0(v___x_23949__boxed_2656_, v_e_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv(lean_object* v_e_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_){
_start:
{
lean_object* v_numArgs_2669_; lean_object* v___x_2670_; uint8_t v___x_2671_; 
v_numArgs_2669_ = l_Lean_Expr_getAppNumArgs(v_e_2658_);
v___x_2670_ = lean_unsigned_to_nat(2u);
v___x_2671_ = lean_nat_dec_lt(v_numArgs_2669_, v___x_2670_);
if (v___x_2671_ == 0)
{
lean_object* v___x_2672_; lean_object* v___f_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2672_ = lean_box(v___x_2671_);
v___f_2673_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___boxed), 12, 1);
lean_closure_set(v___f_2673_, 0, v___x_2672_);
v___x_2674_ = lean_nat_sub(v_numArgs_2669_, v___x_2670_);
lean_dec(v_numArgs_2669_);
v___x_2675_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_2658_, v___x_2674_, v___f_2673_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_);
lean_dec(v___x_2674_);
return v___x_2675_;
}
else
{
uint8_t v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
lean_dec(v_numArgs_2669_);
lean_dec_ref(v_e_2658_);
v___x_2676_ = 0;
v___x_2677_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2677_, 0, v___x_2671_);
lean_ctor_set_uint8(v___x_2677_, 1, v___x_2676_);
v___x_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2677_);
return v___x_2678_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___boxed(lean_object* v_e_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv(v_e_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_);
lean_dec(v_a_2688_);
lean_dec_ref(v_a_2687_);
lean_dec(v_a_2686_);
lean_dec_ref(v_a_2685_);
lean_dec(v_a_2684_);
lean_dec_ref(v_a_2683_);
lean_dec(v_a_2682_);
lean_dec_ref(v_a_2681_);
lean_dec(v_a_2680_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2706_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13_));
v___x_2707_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13_));
v___x_2708_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___boxed), 11, 0);
v___x_2709_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_2706_, v___x_2707_, v___x_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13____boxed(lean_object* v_a_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13_();
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_2713_; uint8_t v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2713_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13_));
v___x_2714_ = 0;
v___x_2715_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___boxed), 11, 0);
v___x_2716_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_2713_, v___x_2714_, v___x_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_15____boxed(lean_object* v_a_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_15_();
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(lean_object* v_declName_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v___x_2722_; lean_object* v_env_2723_; uint8_t v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2722_ = lean_st_ref_get(v___y_2720_);
v_env_2723_ = lean_ctor_get(v___x_2722_, 0);
lean_inc_ref(v_env_2723_);
lean_dec(v___x_2722_);
v___x_2724_ = l_Lean_getReducibilityStatusCore(v_env_2723_, v_declName_2719_);
v___x_2725_ = lean_box(v___x_2724_);
v___x_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg___boxed(lean_object* v_declName_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(v_declName_2727_, v___y_2728_);
lean_dec(v___y_2728_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1(lean_object* v_declName_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v___x_2735_; 
v___x_2735_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(v_declName_2731_, v___y_2733_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___boxed(lean_object* v_declName_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1(v_declName_2736_, v___y_2737_, v___y_2738_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0(lean_object* v_declName_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_){
_start:
{
lean_object* v___x_2745_; lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2761_; 
v___x_2745_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(v_declName_2741_, v___y_2743_);
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2748_ = v___x_2745_;
v_isShared_2749_ = v_isSharedCheck_2761_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2745_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2761_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
uint8_t v___x_2750_; 
v___x_2750_ = lean_unbox(v_a_2746_);
lean_dec(v_a_2746_);
if (v___x_2750_ == 2)
{
uint8_t v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2754_; 
v___x_2751_ = 1;
v___x_2752_ = lean_box(v___x_2751_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 0, v___x_2752_);
v___x_2754_ = v___x_2748_;
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
else
{
uint8_t v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2759_; 
v___x_2756_ = 0;
v___x_2757_ = lean_box(v___x_2756_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 0, v___x_2757_);
v___x_2759_ = v___x_2748_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2757_);
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
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0___boxed(lean_object* v_declName_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0(v_declName_2762_, v___y_2763_, v___y_2764_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0(lean_object* v_canUnfold_x3f_2767_, lean_object* v_cfg_2768_, lean_object* v_info_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_){
_start:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2773_ = l_Lean_ConstantInfo_name(v_info_2769_);
v___x_2774_ = l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(v___x_2773_, v___y_2771_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v_a_2775_; uint8_t v___x_2776_; 
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_a_2775_);
v___x_2776_ = lean_unbox(v_a_2775_);
lean_dec(v_a_2775_);
if (v___x_2776_ == 0)
{
if (lean_obj_tag(v_canUnfold_x3f_2767_) == 0)
{
uint8_t v_transparency_2777_; uint8_t v___x_2778_; 
lean_dec_ref(v_info_2769_);
v_transparency_2777_ = lean_ctor_get_uint8(v_cfg_2768_, 9);
lean_dec_ref(v_cfg_2768_);
v___x_2778_ = 1;
switch(v_transparency_2777_)
{
case 4:
{
lean_dec(v___x_2773_);
return v___x_2774_;
}
case 0:
{
lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2786_; 
lean_dec(v___x_2773_);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2786_ == 0)
{
lean_object* v_unused_2787_; 
v_unused_2787_ = lean_ctor_get(v___x_2774_, 0);
lean_dec(v_unused_2787_);
v___x_2780_ = v___x_2774_;
v_isShared_2781_ = v_isSharedCheck_2786_;
goto v_resetjp_2779_;
}
else
{
lean_dec(v___x_2774_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2786_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2782_; lean_object* v___x_2784_; 
v___x_2782_ = lean_box(v___x_2778_);
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v___x_2782_);
v___x_2784_ = v___x_2780_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v___x_2782_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
case 1:
{
lean_object* v___x_2788_; 
lean_dec_ref_known(v___x_2774_, 1);
v___x_2788_ = l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0(v___x_2773_, v___y_2770_, v___y_2771_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2799_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2791_ = v___x_2788_;
v_isShared_2792_ = v_isSharedCheck_2799_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2788_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2799_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
uint8_t v___x_2793_; uint8_t v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2797_; 
v___x_2793_ = lean_unbox(v_a_2789_);
lean_dec(v_a_2789_);
v___x_2794_ = lean_bool_not(v___x_2793_);
v___x_2795_ = lean_box(v___x_2794_);
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 0, v___x_2795_);
v___x_2797_ = v___x_2791_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2795_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
else
{
return v___x_2788_;
}
}
default: 
{
lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2844_; 
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2844_ == 0)
{
lean_object* v_unused_2845_; 
v_unused_2845_ = lean_ctor_get(v___x_2774_, 0);
lean_dec(v_unused_2845_);
v___x_2801_ = v___x_2774_;
v_isShared_2802_ = v_isSharedCheck_2844_;
goto v_resetjp_2800_;
}
else
{
lean_dec(v___x_2774_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2844_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2803_; lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2843_; 
v___x_2803_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(v___x_2773_, v___y_2771_);
v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2806_ = v___x_2803_;
v_isShared_2807_ = v_isSharedCheck_2843_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2803_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2843_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
uint8_t v___y_2809_; uint8_t v___y_2819_; uint8_t v___x_2829_; uint8_t v___x_2830_; uint8_t v___x_2831_; 
v___x_2829_ = 0;
v___x_2830_ = lean_unbox(v_a_2804_);
v___x_2831_ = l_Lean_instBEqReducibilityStatus_beq(v___x_2830_, v___x_2829_);
if (v___x_2831_ == 0)
{
uint8_t v___x_2832_; uint8_t v___x_2833_; uint8_t v___x_2834_; 
v___x_2832_ = 4;
v___x_2833_ = lean_unbox(v_a_2804_);
v___x_2834_ = l_Lean_instBEqReducibilityStatus_beq(v___x_2833_, v___x_2832_);
if (v___x_2834_ == 0)
{
v___y_2819_ = v___x_2834_;
goto v___jp_2818_;
}
else
{
uint8_t v___x_2835_; uint8_t v___x_2836_; 
v___x_2835_ = 3;
v___x_2836_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2777_, v___x_2835_);
if (v___x_2836_ == 0)
{
uint8_t v___x_2837_; uint8_t v___x_2838_; 
v___x_2837_ = 5;
v___x_2838_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2777_, v___x_2837_);
v___y_2819_ = v___x_2838_;
goto v___jp_2818_;
}
else
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
lean_del_object(v___x_2806_);
lean_dec(v_a_2804_);
lean_del_object(v___x_2801_);
v___x_2839_ = lean_box(v___x_2778_);
v___x_2840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2839_);
return v___x_2840_;
}
}
}
else
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
lean_del_object(v___x_2806_);
lean_dec(v_a_2804_);
lean_del_object(v___x_2801_);
v___x_2841_ = lean_box(v___x_2778_);
v___x_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2841_);
return v___x_2842_;
}
v___jp_2808_:
{
if (v___y_2809_ == 0)
{
lean_object* v___x_2810_; lean_object* v___x_2812_; 
v___x_2810_ = lean_box(v___y_2809_);
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 0, v___x_2810_);
v___x_2812_ = v___x_2806_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2810_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
else
{
lean_object* v___x_2814_; lean_object* v___x_2816_; 
v___x_2814_ = lean_box(v___x_2778_);
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 0, v___x_2814_);
v___x_2816_ = v___x_2806_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2814_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
v___jp_2818_:
{
if (v___y_2819_ == 0)
{
uint8_t v___x_2820_; uint8_t v___x_2821_; uint8_t v___x_2822_; 
lean_del_object(v___x_2801_);
v___x_2820_ = 3;
v___x_2821_ = lean_unbox(v_a_2804_);
lean_dec(v_a_2804_);
v___x_2822_ = l_Lean_instBEqReducibilityStatus_beq(v___x_2821_, v___x_2820_);
if (v___x_2822_ == 0)
{
v___y_2809_ = v___x_2822_;
goto v___jp_2808_;
}
else
{
uint8_t v___x_2823_; uint8_t v___x_2824_; 
v___x_2823_ = 5;
v___x_2824_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2777_, v___x_2823_);
v___y_2809_ = v___x_2824_;
goto v___jp_2808_;
}
}
else
{
lean_object* v___x_2825_; lean_object* v___x_2827_; 
lean_del_object(v___x_2806_);
lean_dec(v_a_2804_);
v___x_2825_ = lean_box(v___x_2778_);
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 0, v___x_2825_);
v___x_2827_ = v___x_2801_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v___x_2825_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
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
lean_object* v_val_2846_; lean_object* v___x_2847_; 
lean_dec_ref_known(v___x_2774_, 1);
lean_dec(v___x_2773_);
v_val_2846_ = lean_ctor_get(v_canUnfold_x3f_2767_, 0);
lean_inc(v_val_2846_);
lean_dec_ref_known(v_canUnfold_x3f_2767_, 1);
lean_inc(v___y_2771_);
lean_inc_ref(v___y_2770_);
v___x_2847_ = lean_apply_5(v_val_2846_, v_cfg_2768_, v_info_2769_, v___y_2770_, v___y_2771_, lean_box(0));
return v___x_2847_;
}
}
else
{
lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2856_; 
lean_dec(v___x_2773_);
lean_dec_ref(v_info_2769_);
lean_dec_ref(v_cfg_2768_);
lean_dec(v_canUnfold_x3f_2767_);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2856_ == 0)
{
lean_object* v_unused_2857_; 
v_unused_2857_ = lean_ctor_get(v___x_2774_, 0);
lean_dec(v_unused_2857_);
v___x_2849_ = v___x_2774_;
v_isShared_2850_ = v_isSharedCheck_2856_;
goto v_resetjp_2848_;
}
else
{
lean_dec(v___x_2774_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2856_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
uint8_t v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2854_; 
v___x_2851_ = 0;
v___x_2852_ = lean_box(v___x_2851_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 0, v___x_2852_);
v___x_2854_ = v___x_2849_;
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
lean_dec(v___x_2773_);
lean_dec_ref(v_info_2769_);
lean_dec_ref(v_cfg_2768_);
lean_dec(v_canUnfold_x3f_2767_);
return v___x_2774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0___boxed(lean_object* v_canUnfold_x3f_2858_, lean_object* v_cfg_2859_, lean_object* v_info_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0(v_canUnfold_x3f_2858_, v_cfg_2859_, v_info_2860_, v___y_2861_, v___y_2862_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(lean_object* v_x_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_){
_start:
{
lean_object* v_keyedConfig_2871_; uint8_t v_trackZetaDelta_2872_; lean_object* v_zetaDeltaSet_2873_; lean_object* v_lctx_2874_; lean_object* v_localInstances_2875_; lean_object* v_defEqCtx_x3f_2876_; lean_object* v_synthPendingDepth_2877_; lean_object* v_canUnfold_x3f_2878_; uint8_t v_univApprox_2879_; uint8_t v_inTypeClassResolution_2880_; uint8_t v_cacheInferType_2881_; lean_object* v___f_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v_keyedConfig_2871_ = lean_ctor_get(v_a_2866_, 0);
v_trackZetaDelta_2872_ = lean_ctor_get_uint8(v_a_2866_, sizeof(void*)*7);
v_zetaDeltaSet_2873_ = lean_ctor_get(v_a_2866_, 1);
v_lctx_2874_ = lean_ctor_get(v_a_2866_, 2);
v_localInstances_2875_ = lean_ctor_get(v_a_2866_, 3);
v_defEqCtx_x3f_2876_ = lean_ctor_get(v_a_2866_, 4);
v_synthPendingDepth_2877_ = lean_ctor_get(v_a_2866_, 5);
v_canUnfold_x3f_2878_ = lean_ctor_get(v_a_2866_, 6);
v_univApprox_2879_ = lean_ctor_get_uint8(v_a_2866_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2880_ = lean_ctor_get_uint8(v_a_2866_, sizeof(void*)*7 + 2);
v_cacheInferType_2881_ = lean_ctor_get_uint8(v_a_2866_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_2878_);
v___f_2882_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2882_, 0, v_canUnfold_x3f_2878_);
v___x_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2883_, 0, v___f_2882_);
lean_inc(v_synthPendingDepth_2877_);
lean_inc(v_defEqCtx_x3f_2876_);
lean_inc_ref(v_localInstances_2875_);
lean_inc_ref(v_lctx_2874_);
lean_inc(v_zetaDeltaSet_2873_);
lean_inc_ref(v_keyedConfig_2871_);
v___x_2884_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2884_, 0, v_keyedConfig_2871_);
lean_ctor_set(v___x_2884_, 1, v_zetaDeltaSet_2873_);
lean_ctor_set(v___x_2884_, 2, v_lctx_2874_);
lean_ctor_set(v___x_2884_, 3, v_localInstances_2875_);
lean_ctor_set(v___x_2884_, 4, v_defEqCtx_x3f_2876_);
lean_ctor_set(v___x_2884_, 5, v_synthPendingDepth_2877_);
lean_ctor_set(v___x_2884_, 6, v___x_2883_);
lean_ctor_set_uint8(v___x_2884_, sizeof(void*)*7, v_trackZetaDelta_2872_);
lean_ctor_set_uint8(v___x_2884_, sizeof(void*)*7 + 1, v_univApprox_2879_);
lean_ctor_set_uint8(v___x_2884_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2880_);
lean_ctor_set_uint8(v___x_2884_, sizeof(void*)*7 + 3, v_cacheInferType_2881_);
lean_inc(v_a_2869_);
lean_inc_ref(v_a_2868_);
lean_inc(v_a_2867_);
v___x_2885_ = lean_apply_5(v_x_2865_, v___x_2884_, v_a_2867_, v_a_2868_, v_a_2869_, lean_box(0));
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___boxed(lean_object* v_x_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v_x_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_);
lean_dec(v_a_2890_);
lean_dec_ref(v_a_2889_);
lean_dec(v_a_2888_);
lean_dec_ref(v_a_2887_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard(lean_object* v_00_u03b1_2893_, lean_object* v_x_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v_x_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___boxed(lean_object* v_00_u03b1_2901_, lean_object* v_x_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard(v_00_u03b1_2901_, v_x_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond(lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_){
_start:
{
lean_object* v___x_2920_; 
v___x_2920_ = l_Lean_Meta_Sym_Simp_simpCond(v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___boxed(lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond(v_a_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_);
lean_dec(v_a_2930_);
lean_dec_ref(v_a_2929_);
lean_dec(v_a_2928_);
lean_dec_ref(v_a_2927_);
lean_dec(v_a_2926_);
lean_dec_ref(v_a_2925_);
lean_dec(v_a_2924_);
lean_dec_ref(v_a_2923_);
lean_dec(v_a_2922_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_(){
_start:
{
lean_object* v___f_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___f_2959_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_));
v___x_2960_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_));
v___x_2961_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_));
v___x_2962_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_2960_, v___x_2961_, v___f_2959_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15____boxed(lean_object* v_a_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_();
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_17_(){
_start:
{
lean_object* v___f_2966_; lean_object* v___x_2967_; uint8_t v___x_2968_; lean_object* v___x_2969_; 
v___f_2966_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_));
v___x_2967_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_));
v___x_2968_ = 0;
v___x_2969_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_2967_, v___x_2968_, v___f_2966_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_17____boxed(lean_object* v_a_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_17_();
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0(lean_object* v_msgData_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
lean_object* v___x_2978_; lean_object* v_env_2979_; lean_object* v___x_2980_; lean_object* v_mctx_2981_; lean_object* v_lctx_2982_; lean_object* v_options_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2978_ = lean_st_ref_get(v___y_2976_);
v_env_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc_ref(v_env_2979_);
lean_dec(v___x_2978_);
v___x_2980_ = lean_st_ref_get(v___y_2974_);
v_mctx_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc_ref(v_mctx_2981_);
lean_dec(v___x_2980_);
v_lctx_2982_ = lean_ctor_get(v___y_2973_, 2);
v_options_2983_ = lean_ctor_get(v___y_2975_, 2);
lean_inc_ref(v_options_2983_);
lean_inc_ref(v_lctx_2982_);
v___x_2984_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2984_, 0, v_env_2979_);
lean_ctor_set(v___x_2984_, 1, v_mctx_2981_);
lean_ctor_set(v___x_2984_, 2, v_lctx_2982_);
lean_ctor_set(v___x_2984_, 3, v_options_2983_);
v___x_2985_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2984_);
lean_ctor_set(v___x_2985_, 1, v_msgData_2972_);
v___x_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2985_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0___boxed(lean_object* v_msgData_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0(v_msgData_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
return v_res_2993_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2994_; double v___x_2995_; 
v___x_2994_ = lean_unsigned_to_nat(0u);
v___x_2995_ = lean_float_of_nat(v___x_2994_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(lean_object* v_cls_2999_, lean_object* v_msg_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v_ref_3006_; lean_object* v___x_3007_; lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3052_; 
v_ref_3006_ = lean_ctor_get(v___y_3003_, 5);
v___x_3007_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0(v_msg_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3010_ = v___x_3007_;
v_isShared_3011_ = v_isSharedCheck_3052_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_3007_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3052_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3012_; lean_object* v_traceState_3013_; lean_object* v_env_3014_; lean_object* v_nextMacroScope_3015_; lean_object* v_ngen_3016_; lean_object* v_auxDeclNGen_3017_; lean_object* v_cache_3018_; lean_object* v_messages_3019_; lean_object* v_infoState_3020_; lean_object* v_snapshotTasks_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3051_; 
v___x_3012_ = lean_st_ref_take(v___y_3004_);
v_traceState_3013_ = lean_ctor_get(v___x_3012_, 4);
v_env_3014_ = lean_ctor_get(v___x_3012_, 0);
v_nextMacroScope_3015_ = lean_ctor_get(v___x_3012_, 1);
v_ngen_3016_ = lean_ctor_get(v___x_3012_, 2);
v_auxDeclNGen_3017_ = lean_ctor_get(v___x_3012_, 3);
v_cache_3018_ = lean_ctor_get(v___x_3012_, 5);
v_messages_3019_ = lean_ctor_get(v___x_3012_, 6);
v_infoState_3020_ = lean_ctor_get(v___x_3012_, 7);
v_snapshotTasks_3021_ = lean_ctor_get(v___x_3012_, 8);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3023_ = v___x_3012_;
v_isShared_3024_ = v_isSharedCheck_3051_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_snapshotTasks_3021_);
lean_inc(v_infoState_3020_);
lean_inc(v_messages_3019_);
lean_inc(v_cache_3018_);
lean_inc(v_traceState_3013_);
lean_inc(v_auxDeclNGen_3017_);
lean_inc(v_ngen_3016_);
lean_inc(v_nextMacroScope_3015_);
lean_inc(v_env_3014_);
lean_dec(v___x_3012_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3051_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
uint64_t v_tid_3025_; lean_object* v_traces_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3050_; 
v_tid_3025_ = lean_ctor_get_uint64(v_traceState_3013_, sizeof(void*)*1);
v_traces_3026_ = lean_ctor_get(v_traceState_3013_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v_traceState_3013_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3028_ = v_traceState_3013_;
v_isShared_3029_ = v_isSharedCheck_3050_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_traces_3026_);
lean_dec(v_traceState_3013_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3050_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3030_; double v___x_3031_; uint8_t v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3040_; 
v___x_3030_ = lean_box(0);
v___x_3031_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0);
v___x_3032_ = 0;
v___x_3033_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__1));
v___x_3034_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3034_, 0, v_cls_2999_);
lean_ctor_set(v___x_3034_, 1, v___x_3030_);
lean_ctor_set(v___x_3034_, 2, v___x_3033_);
lean_ctor_set_float(v___x_3034_, sizeof(void*)*3, v___x_3031_);
lean_ctor_set_float(v___x_3034_, sizeof(void*)*3 + 8, v___x_3031_);
lean_ctor_set_uint8(v___x_3034_, sizeof(void*)*3 + 16, v___x_3032_);
v___x_3035_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__2));
v___x_3036_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3034_);
lean_ctor_set(v___x_3036_, 1, v_a_3008_);
lean_ctor_set(v___x_3036_, 2, v___x_3035_);
lean_inc(v_ref_3006_);
v___x_3037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3037_, 0, v_ref_3006_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
v___x_3038_ = l_Lean_PersistentArray_push___redArg(v_traces_3026_, v___x_3037_);
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 0, v___x_3038_);
v___x_3040_ = v___x_3028_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3038_);
lean_ctor_set_uint64(v_reuseFailAlloc_3049_, sizeof(void*)*1, v_tid_3025_);
v___x_3040_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
lean_object* v___x_3042_; 
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 4, v___x_3040_);
v___x_3042_ = v___x_3023_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_env_3014_);
lean_ctor_set(v_reuseFailAlloc_3048_, 1, v_nextMacroScope_3015_);
lean_ctor_set(v_reuseFailAlloc_3048_, 2, v_ngen_3016_);
lean_ctor_set(v_reuseFailAlloc_3048_, 3, v_auxDeclNGen_3017_);
lean_ctor_set(v_reuseFailAlloc_3048_, 4, v___x_3040_);
lean_ctor_set(v_reuseFailAlloc_3048_, 5, v_cache_3018_);
lean_ctor_set(v_reuseFailAlloc_3048_, 6, v_messages_3019_);
lean_ctor_set(v_reuseFailAlloc_3048_, 7, v_infoState_3020_);
lean_ctor_set(v_reuseFailAlloc_3048_, 8, v_snapshotTasks_3021_);
v___x_3042_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3046_; 
v___x_3043_ = lean_st_ref_set(v___y_3004_, v___x_3042_);
v___x_3044_ = lean_box(0);
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 0, v___x_3044_);
v___x_3046_ = v___x_3010_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3044_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___boxed(lean_object* v_cls_3053_, lean_object* v_msg_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v_cls_3053_, v_msg_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
return v_res_3060_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5(void){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3071_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2));
v___x_3072_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__4));
v___x_3073_ = l_Lean_Name_append(v___x_3072_, v___x_3071_);
return v___x_3073_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7(void){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3075_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__6));
v___x_3076_ = l_Lean_stringToMessageData(v___x_3075_);
return v___x_3076_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9(void){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3078_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__8));
v___x_3079_ = l_Lean_stringToMessageData(v___x_3078_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(lean_object* v_e_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
lean_inc_ref(v_e_3082_);
v___x_3093_ = lean_alloc_closure((void*)(l_Lean_Meta_reduceRecMatcher_x3f___boxed), 6, 1);
lean_closure_set(v___x_3093_, 0, v_e_3082_);
v___x_3094_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___x_3093_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3152_; 
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3097_ = v___x_3094_;
v_isShared_3098_ = v_isSharedCheck_3152_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3094_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3152_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
if (lean_obj_tag(v_a_3095_) == 1)
{
lean_object* v_val_3099_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v_options_3126_; uint8_t v_hasTrace_3127_; 
lean_del_object(v___x_3097_);
v_val_3099_ = lean_ctor_get(v_a_3095_, 0);
lean_inc(v_val_3099_);
lean_dec_ref_known(v_a_3095_, 1);
v_options_3126_ = lean_ctor_get(v_a_3090_, 2);
v_hasTrace_3127_ = lean_ctor_get_uint8(v_options_3126_, sizeof(void*)*1);
if (v_hasTrace_3127_ == 0)
{
lean_dec_ref(v_e_3082_);
v___y_3101_ = v_a_3086_;
v___y_3102_ = v_a_3087_;
v___y_3103_ = v_a_3088_;
v___y_3104_ = v_a_3089_;
v___y_3105_ = v_a_3090_;
v___y_3106_ = v_a_3091_;
goto v___jp_3100_;
}
else
{
lean_object* v_inheritedTraceOptions_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; uint8_t v___x_3131_; 
v_inheritedTraceOptions_3128_ = lean_ctor_get(v_a_3090_, 13);
v___x_3129_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2));
v___x_3130_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5, &l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5);
v___x_3131_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3128_, v_options_3126_, v___x_3130_);
if (v___x_3131_ == 0)
{
lean_dec_ref(v_e_3082_);
v___y_3101_ = v_a_3086_;
v___y_3102_ = v_a_3087_;
v___y_3103_ = v_a_3088_;
v___y_3104_ = v_a_3089_;
v___y_3105_ = v_a_3090_;
v___y_3106_ = v_a_3091_;
goto v___jp_3100_;
}
else
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3132_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7, &l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7);
v___x_3133_ = l_Lean_indentExpr(v_e_3082_);
v___x_3134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3132_);
lean_ctor_set(v___x_3134_, 1, v___x_3133_);
v___x_3135_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9, &l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9_once, _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9);
v___x_3136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3134_);
lean_ctor_set(v___x_3136_, 1, v___x_3135_);
lean_inc(v_val_3099_);
v___x_3137_ = l_Lean_indentExpr(v_val_3099_);
v___x_3138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3136_);
lean_ctor_set(v___x_3138_, 1, v___x_3137_);
v___x_3139_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v___x_3129_, v___x_3138_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_dec_ref_known(v___x_3139_, 1);
v___y_3101_ = v_a_3086_;
v___y_3102_ = v_a_3087_;
v___y_3103_ = v_a_3088_;
v___y_3104_ = v_a_3089_;
v___y_3105_ = v_a_3090_;
v___y_3106_ = v_a_3091_;
goto v___jp_3100_;
}
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
lean_dec(v_val_3099_);
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3139_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3139_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
}
v___jp_3100_:
{
lean_object* v___x_3107_; 
lean_inc(v_val_3099_);
v___x_3107_ = l_Lean_Meta_Sym_mkEqRefl(v_val_3099_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3117_; 
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3110_ = v___x_3107_;
v_isShared_3111_ = v_isSharedCheck_3117_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3107_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3117_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
uint8_t v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3115_; 
v___x_3112_ = 0;
v___x_3113_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3113_, 0, v_val_3099_);
lean_ctor_set(v___x_3113_, 1, v_a_3108_);
lean_ctor_set_uint8(v___x_3113_, sizeof(void*)*2, v___x_3112_);
lean_ctor_set_uint8(v___x_3113_, sizeof(void*)*2 + 1, v___x_3112_);
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 0, v___x_3113_);
v___x_3115_ = v___x_3110_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3113_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
else
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_dec(v_val_3099_);
v_a_3118_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_3107_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3107_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
}
else
{
lean_object* v___x_3148_; lean_object* v___x_3150_; 
lean_dec(v_a_3095_);
lean_dec_ref(v_e_3082_);
v___x_3148_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__10));
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 0, v___x_3148_);
v___x_3150_ = v___x_3097_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v___x_3148_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
else
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
lean_dec_ref(v_e_3082_);
v_a_3153_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v___x_3094_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3094_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3153_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___boxed(lean_object* v_e_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_e_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_);
lean_dec(v_a_3170_);
lean_dec_ref(v_a_3169_);
lean_dec(v_a_3168_);
lean_dec_ref(v_a_3167_);
lean_dec(v_a_3166_);
lean_dec_ref(v_a_3165_);
lean_dec(v_a_3164_);
lean_dec_ref(v_a_3163_);
lean_dec(v_a_3162_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0(lean_object* v_cls_3173_, lean_object* v_msg_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v___x_3185_; 
v___x_3185_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v_cls_3173_, v_msg_3174_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___boxed(lean_object* v_cls_3186_, lean_object* v_msg_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v_res_3198_; 
v_res_3198_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0(v_cls_3186_, v_msg_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec(v___y_3188_);
return v_res_3198_;
}
}
static uint8_t _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___closed__1(void){
_start:
{
uint8_t v___x_3213_; uint8_t v___x_3214_; 
v___x_3213_ = 0;
v___x_3214_ = lean_bool_not(v___x_3213_);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec(lean_object* v_x_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_){
_start:
{
uint8_t v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3226_ = 0;
v___x_3227_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___closed__0));
lean_inc_ref(v_x_3215_);
v___x_3228_ = l_Lean_Meta_Sym_Simp_simpInterlaced(v_x_3215_, v___x_3227_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_a_3229_; 
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_a_3229_);
if (lean_obj_tag(v_a_3229_) == 0)
{
uint8_t v_done_3230_; 
v_done_3230_ = lean_ctor_get_uint8(v_a_3229_, 0);
if (v_done_3230_ == 0)
{
uint8_t v_contextDependent_3231_; lean_object* v___x_3232_; 
lean_dec_ref_known(v___x_3228_, 1);
v_contextDependent_3231_ = lean_ctor_get_uint8(v_a_3229_, 1);
lean_dec_ref_known(v_a_3229_, 0);
v___x_3232_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_x_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_a_3233_; uint8_t v___y_3235_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_a_3233_);
if (v_contextDependent_3231_ == 0)
{
lean_dec(v_a_3233_);
return v___x_3232_;
}
else
{
uint8_t v___x_3245_; 
v___x_3245_ = lean_uint8_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___closed__1, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___closed__1);
v___y_3235_ = v___x_3245_;
goto v___jp_3234_;
}
v___jp_3234_:
{
if (v___y_3235_ == 0)
{
lean_dec(v_a_3233_);
return v___x_3232_;
}
else
{
lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3243_; 
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3243_ == 0)
{
lean_object* v_unused_3244_; 
v_unused_3244_ = lean_ctor_get(v___x_3232_, 0);
lean_dec(v_unused_3244_);
v___x_3237_ = v___x_3232_;
v_isShared_3238_ = v_isSharedCheck_3243_;
goto v_resetjp_3236_;
}
else
{
lean_dec(v___x_3232_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3243_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3239_; lean_object* v___x_3241_; 
v___x_3239_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3233_);
if (v_isShared_3238_ == 0)
{
lean_ctor_set(v___x_3237_, 0, v___x_3239_);
v___x_3241_ = v___x_3237_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_3239_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
}
}
else
{
return v___x_3232_;
}
}
else
{
lean_dec_ref_known(v_a_3229_, 0);
lean_dec_ref(v_x_3215_);
return v___x_3228_;
}
}
else
{
uint8_t v_done_3246_; 
v_done_3246_ = lean_ctor_get_uint8(v_a_3229_, sizeof(void*)*2);
if (v_done_3246_ == 0)
{
lean_object* v_e_x27_3247_; lean_object* v_proof_3248_; uint8_t v_contextDependent_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3295_; 
lean_dec_ref_known(v___x_3228_, 1);
v_e_x27_3247_ = lean_ctor_get(v_a_3229_, 0);
v_proof_3248_ = lean_ctor_get(v_a_3229_, 1);
v_contextDependent_3249_ = lean_ctor_get_uint8(v_a_3229_, sizeof(void*)*2 + 1);
v_isSharedCheck_3295_ = !lean_is_exclusive(v_a_3229_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3251_ = v_a_3229_;
v_isShared_3252_ = v_isSharedCheck_3295_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_proof_3248_);
lean_inc(v_e_x27_3247_);
lean_dec(v_a_3229_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3295_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3253_; 
lean_inc_ref(v_e_x27_3247_);
v___x_3253_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_e_x27_3247_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3294_; 
v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3256_ = v___x_3253_;
v_isShared_3257_ = v_isSharedCheck_3294_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3253_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3294_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
if (lean_obj_tag(v_a_3254_) == 0)
{
uint8_t v___y_3259_; 
lean_dec_ref_known(v_a_3254_, 0);
lean_dec_ref(v_x_3215_);
if (v_contextDependent_3249_ == 0)
{
v___y_3259_ = v___x_3226_;
goto v___jp_3258_;
}
else
{
v___y_3259_ = v_contextDependent_3249_;
goto v___jp_3258_;
}
v___jp_3258_:
{
lean_object* v___x_3261_; 
if (v_isShared_3252_ == 0)
{
v___x_3261_ = v___x_3251_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_e_x27_3247_);
lean_ctor_set(v_reuseFailAlloc_3265_, 1, v_proof_3248_);
v___x_3261_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
lean_object* v___x_3263_; 
lean_ctor_set_uint8(v___x_3261_, sizeof(void*)*2, v___x_3226_);
lean_ctor_set_uint8(v___x_3261_, sizeof(void*)*2 + 1, v___y_3259_);
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 0, v___x_3261_);
v___x_3263_ = v___x_3256_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v___x_3261_);
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
else
{
lean_object* v_e_x27_3266_; lean_object* v_proof_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3293_; 
lean_del_object(v___x_3256_);
lean_del_object(v___x_3251_);
v_e_x27_3266_ = lean_ctor_get(v_a_3254_, 0);
v_proof_3267_ = lean_ctor_get(v_a_3254_, 1);
v_isSharedCheck_3293_ = !lean_is_exclusive(v_a_3254_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3269_ = v_a_3254_;
v_isShared_3270_ = v_isSharedCheck_3293_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_proof_3267_);
lean_inc(v_e_x27_3266_);
lean_dec(v_a_3254_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3293_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3271_; 
lean_inc_ref(v_e_x27_3266_);
v___x_3271_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_x_3215_, v_e_x27_3247_, v_proof_3248_, v_e_x27_3266_, v_proof_3267_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3284_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3274_ = v___x_3271_;
v_isShared_3275_ = v_isSharedCheck_3284_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3271_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3284_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
uint8_t v___y_3277_; 
if (v_contextDependent_3249_ == 0)
{
v___y_3277_ = v___x_3226_;
goto v___jp_3276_;
}
else
{
v___y_3277_ = v_contextDependent_3249_;
goto v___jp_3276_;
}
v___jp_3276_:
{
lean_object* v___x_3279_; 
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 1, v_a_3272_);
v___x_3279_ = v___x_3269_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_e_x27_3266_);
lean_ctor_set(v_reuseFailAlloc_3283_, 1, v_a_3272_);
v___x_3279_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
lean_object* v___x_3281_; 
lean_ctor_set_uint8(v___x_3279_, sizeof(void*)*2, v___x_3226_);
lean_ctor_set_uint8(v___x_3279_, sizeof(void*)*2 + 1, v___y_3277_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v___x_3279_);
v___x_3281_ = v___x_3274_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v___x_3279_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
}
}
}
else
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
lean_del_object(v___x_3269_);
lean_dec_ref(v_e_x27_3266_);
v_a_3285_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3271_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3271_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3290_; 
if (v_isShared_3288_ == 0)
{
v___x_3290_ = v___x_3287_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3285_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_3251_);
lean_dec_ref(v_proof_3248_);
lean_dec_ref(v_e_x27_3247_);
lean_dec_ref(v_x_3215_);
return v___x_3253_;
}
}
}
else
{
lean_dec_ref_known(v_a_3229_, 2);
lean_dec_ref(v_x_3215_);
return v___x_3228_;
}
}
}
else
{
lean_dec_ref(v_x_3215_);
return v___x_3228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___boxed(lean_object* v_x_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec(v_x_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_);
lean_dec(v_a_3305_);
lean_dec_ref(v_a_3304_);
lean_dec(v_a_3303_);
lean_dec_ref(v_a_3302_);
lean_dec(v_a_3301_);
lean_dec_ref(v_a_3300_);
lean_dec(v_a_3299_);
lean_dec_ref(v_a_3298_);
lean_dec(v_a_3297_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3330_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_));
v___x_3331_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_));
v___x_3332_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___boxed), 11, 0);
v___x_3333_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_3330_, v___x_3331_, v___x_3332_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17____boxed(lean_object* v_a_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_();
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_3337_; uint8_t v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
v___x_3337_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_));
v___x_3338_ = 0;
v___x_3339_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___boxed), 11, 0);
v___x_3340_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_3337_, v___x_3338_, v___x_3339_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_19____boxed(lean_object* v_a_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_19_();
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(lean_object* v_appFn_3344_, lean_object* v_e_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_){
_start:
{
lean_object* v___x_3356_; 
v___x_3356_ = l_Lean_Meta_Tactic_Cbv_getMatchTheorems(v_appFn_3344_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_a_3357_);
lean_dec_ref_known(v___x_3356_, 1);
v___x_3358_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0));
v___x_3359_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_3357_, v___x_3358_, v_e_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
lean_dec(v_a_3357_);
return v___x_3359_;
}
else
{
lean_object* v_a_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3367_; 
lean_dec_ref(v_e_3345_);
v_a_3360_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3362_ = v___x_3356_;
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_a_3360_);
lean_dec(v___x_3356_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v___x_3365_; 
if (v_isShared_3363_ == 0)
{
v___x_3365_ = v___x_3362_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_a_3360_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___boxed(lean_object* v_appFn_3368_, lean_object* v_e_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(v_appFn_3368_, v_e_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_);
lean_dec(v_a_3378_);
lean_dec_ref(v_a_3377_);
lean_dec(v_a_3376_);
lean_dec_ref(v_a_3375_);
lean_dec(v_a_3374_);
lean_dec_ref(v_a_3373_);
lean_dec(v_a_3372_);
lean_dec_ref(v_a_3371_);
lean_dec(v_a_3370_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(lean_object* v_declName_3381_, lean_object* v___y_3382_){
_start:
{
lean_object* v___x_3384_; lean_object* v_env_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3384_ = lean_st_ref_get(v___y_3382_);
v_env_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc_ref(v_env_3385_);
lean_dec(v___x_3384_);
v___x_3386_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_3385_, v_declName_3381_);
v___x_3387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3386_);
return v___x_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg___boxed(lean_object* v_declName_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
lean_object* v_res_3391_; 
v_res_3391_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(v_declName_3388_, v___y_3389_);
lean_dec(v___y_3389_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0(lean_object* v_declName_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v___x_3403_; 
v___x_3403_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(v_declName_3392_, v___y_3401_);
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___boxed(lean_object* v_declName_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
lean_object* v_res_3415_; 
v_res_3415_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0(v_declName_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
return v_res_3415_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2(void){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3422_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1));
v___x_3423_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__4));
v___x_3424_ = l_Lean_Name_append(v___x_3423_, v___x_3422_);
return v___x_3424_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4(void){
_start:
{
lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3426_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__3));
v___x_3427_ = l_Lean_stringToMessageData(v___x_3426_);
return v___x_3427_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6(void){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3429_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__5));
v___x_3430_ = l_Lean_stringToMessageData(v___x_3429_);
return v___x_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher(lean_object* v_e_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_){
_start:
{
uint8_t v___x_3442_; 
v___x_3442_ = l_Lean_Expr_isApp(v_e_3431_);
if (v___x_3442_ == 0)
{
lean_object* v___x_3443_; lean_object* v___x_3444_; 
lean_dec_ref(v_e_3431_);
v___x_3443_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3443_, 0, v___x_3442_);
lean_ctor_set_uint8(v___x_3443_, 1, v___x_3442_);
v___x_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3443_);
return v___x_3444_;
}
else
{
lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3445_ = l_Lean_Expr_getAppFn(v_e_3431_);
v___x_3446_ = l_Lean_Expr_constName_x3f(v___x_3445_);
lean_dec_ref(v___x_3445_);
if (lean_obj_tag(v___x_3446_) == 1)
{
lean_object* v_val_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3596_; 
v_val_3447_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3449_ = v___x_3446_;
v_isShared_3450_ = v_isSharedCheck_3596_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_val_3447_);
lean_dec(v___x_3446_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3596_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v_a_3452_; lean_object* v_e_x27_3453_; lean_object* v___y_3495_; lean_object* v_a_3496_; lean_object* v___y_3499_; lean_object* v___y_3502_; lean_object* v___y_3503_; uint8_t v___y_3504_; lean_object* v___y_3508_; lean_object* v_a_3509_; lean_object* v___y_3517_; lean_object* v___x_3519_; lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3595_; 
lean_inc(v_val_3447_);
v___x_3519_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(v_val_3447_, v_a_3440_);
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3522_ = v___x_3519_;
v_isShared_3523_ = v_isSharedCheck_3595_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3519_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3595_;
goto v_resetjp_3521_;
}
v___jp_3451_:
{
lean_object* v_options_3454_; uint8_t v_hasTrace_3455_; 
v_options_3454_ = lean_ctor_get(v_a_3439_, 2);
v_hasTrace_3455_ = lean_ctor_get_uint8(v_options_3454_, sizeof(void*)*1);
if (v_hasTrace_3455_ == 0)
{
lean_object* v___x_3457_; 
lean_dec_ref(v_e_x27_3453_);
lean_dec(v_val_3447_);
lean_dec_ref(v_e_3431_);
if (v_isShared_3450_ == 0)
{
lean_ctor_set_tag(v___x_3449_, 0);
lean_ctor_set(v___x_3449_, 0, v_a_3452_);
v___x_3457_ = v___x_3449_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_a_3452_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; uint8_t v___x_3462_; 
v_inheritedTraceOptions_3459_ = lean_ctor_get(v_a_3439_, 13);
v___x_3460_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1));
v___x_3461_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2, &l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2);
v___x_3462_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3459_, v_options_3454_, v___x_3461_);
if (v___x_3462_ == 0)
{
lean_object* v___x_3464_; 
lean_dec_ref(v_e_x27_3453_);
lean_dec(v_val_3447_);
lean_dec_ref(v_e_3431_);
if (v_isShared_3450_ == 0)
{
lean_ctor_set_tag(v___x_3449_, 0);
lean_ctor_set(v___x_3449_, 0, v_a_3452_);
v___x_3464_ = v___x_3449_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3452_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
else
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
lean_del_object(v___x_3449_);
v___x_3466_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4, &l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4_once, _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4);
v___x_3467_ = l_Lean_MessageData_ofName(v_val_3447_);
v___x_3468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3466_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
v___x_3469_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6, &l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6);
v___x_3470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3468_);
lean_ctor_set(v___x_3470_, 1, v___x_3469_);
v___x_3471_ = l_Lean_indentExpr(v_e_3431_);
v___x_3472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3470_);
lean_ctor_set(v___x_3472_, 1, v___x_3471_);
v___x_3473_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9, &l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9_once, _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9);
v___x_3474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3472_);
lean_ctor_set(v___x_3474_, 1, v___x_3473_);
v___x_3475_ = l_Lean_indentExpr(v_e_x27_3453_);
v___x_3476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3474_);
lean_ctor_set(v___x_3476_, 1, v___x_3475_);
v___x_3477_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v___x_3460_, v___x_3476_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3484_; 
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3484_ == 0)
{
lean_object* v_unused_3485_; 
v_unused_3485_ = lean_ctor_get(v___x_3477_, 0);
lean_dec(v_unused_3485_);
v___x_3479_ = v___x_3477_;
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
else
{
lean_dec(v___x_3477_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 0, v_a_3452_);
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3452_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
else
{
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3493_; 
lean_dec_ref(v_a_3452_);
v_a_3486_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3488_ = v___x_3477_;
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3477_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3491_; 
if (v_isShared_3489_ == 0)
{
v___x_3491_ = v___x_3488_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3486_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
}
}
}
v___jp_3494_:
{
if (lean_obj_tag(v_a_3496_) == 1)
{
lean_object* v_e_x27_3497_; 
lean_dec_ref(v___y_3495_);
v_e_x27_3497_ = lean_ctor_get(v_a_3496_, 0);
lean_inc_ref(v_e_x27_3497_);
v_a_3452_ = v_a_3496_;
v_e_x27_3453_ = v_e_x27_3497_;
goto v___jp_3451_;
}
else
{
lean_dec_ref(v_a_3496_);
lean_del_object(v___x_3449_);
lean_dec(v_val_3447_);
lean_dec_ref(v_e_3431_);
return v___y_3495_;
}
}
v___jp_3498_:
{
if (lean_obj_tag(v___y_3499_) == 0)
{
lean_object* v_a_3500_; 
v_a_3500_ = lean_ctor_get(v___y_3499_, 0);
lean_inc(v_a_3500_);
v___y_3495_ = v___y_3499_;
v_a_3496_ = v_a_3500_;
goto v___jp_3494_;
}
else
{
lean_del_object(v___x_3449_);
lean_dec(v_val_3447_);
lean_dec_ref(v_e_3431_);
return v___y_3499_;
}
}
v___jp_3501_:
{
if (v___y_3504_ == 0)
{
lean_dec_ref(v___y_3502_);
v___y_3499_ = v___y_3503_;
goto v___jp_3498_;
}
else
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
lean_dec_ref(v___y_3503_);
v___x_3505_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3502_);
lean_inc_ref(v___x_3505_);
v___x_3506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3505_);
v___y_3495_ = v___x_3506_;
v_a_3496_ = v___x_3505_;
goto v___jp_3494_;
}
}
v___jp_3507_:
{
if (lean_obj_tag(v_a_3509_) == 0)
{
uint8_t v_done_3510_; 
v_done_3510_ = lean_ctor_get_uint8(v_a_3509_, 0);
if (v_done_3510_ == 0)
{
uint8_t v_contextDependent_3511_; lean_object* v___x_3512_; 
lean_dec_ref(v___y_3508_);
v_contextDependent_3511_ = lean_ctor_get_uint8(v_a_3509_, 1);
lean_dec_ref_known(v_a_3509_, 0);
lean_inc_ref(v_e_3431_);
v___x_3512_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_e_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_);
if (lean_obj_tag(v___x_3512_) == 0)
{
if (v_contextDependent_3511_ == 0)
{
v___y_3499_ = v___x_3512_;
goto v___jp_3498_;
}
else
{
lean_object* v_a_3513_; uint8_t v___x_3514_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
lean_inc(v_a_3513_);
v___x_3514_ = lean_uint8_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___closed__1, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___closed__1);
v___y_3502_ = v_a_3513_;
v___y_3503_ = v___x_3512_;
v___y_3504_ = v___x_3514_;
goto v___jp_3501_;
}
}
else
{
v___y_3499_ = v___x_3512_;
goto v___jp_3498_;
}
}
else
{
lean_dec_ref_known(v_a_3509_, 0);
lean_del_object(v___x_3449_);
lean_dec(v_val_3447_);
lean_dec_ref(v_e_3431_);
return v___y_3508_;
}
}
else
{
lean_object* v_e_x27_3515_; 
lean_dec_ref(v___y_3508_);
v_e_x27_3515_ = lean_ctor_get(v_a_3509_, 0);
lean_inc_ref(v_e_x27_3515_);
v_a_3452_ = v_a_3509_;
v_e_x27_3453_ = v_e_x27_3515_;
goto v___jp_3451_;
}
}
v___jp_3516_:
{
if (lean_obj_tag(v___y_3517_) == 0)
{
lean_object* v_a_3518_; 
v_a_3518_ = lean_ctor_get(v___y_3517_, 0);
lean_inc(v_a_3518_);
v___y_3508_ = v___y_3517_;
v_a_3509_ = v_a_3518_;
goto v___jp_3507_;
}
else
{
lean_del_object(v___x_3449_);
lean_dec(v_val_3447_);
lean_dec_ref(v_e_3431_);
return v___y_3517_;
}
}
v_resetjp_3521_:
{
if (lean_obj_tag(v_a_3520_) == 1)
{
lean_object* v_val_3524_; lean_object* v_numParams_3525_; lean_object* v_numDiscrs_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
lean_del_object(v___x_3522_);
v_val_3524_ = lean_ctor_get(v_a_3520_, 0);
lean_inc(v_val_3524_);
lean_dec_ref_known(v_a_3520_, 1);
v_numParams_3525_ = lean_ctor_get(v_val_3524_, 0);
lean_inc(v_numParams_3525_);
v_numDiscrs_3526_ = lean_ctor_get(v_val_3524_, 1);
lean_inc(v_numDiscrs_3526_);
lean_dec(v_val_3524_);
v___x_3527_ = lean_unsigned_to_nat(1u);
v___x_3528_ = lean_nat_add(v_numParams_3525_, v___x_3527_);
lean_dec(v_numParams_3525_);
v___x_3529_ = lean_nat_add(v___x_3528_, v_numDiscrs_3526_);
lean_dec(v_numDiscrs_3526_);
lean_inc_ref(v_e_3431_);
v___x_3530_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_e_3431_, v___x_3528_, v___x_3529_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_);
lean_dec(v___x_3529_);
lean_dec(v___x_3528_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3531_);
if (lean_obj_tag(v_a_3531_) == 0)
{
uint8_t v_done_3532_; 
v_done_3532_ = lean_ctor_get_uint8(v_a_3531_, 0);
if (v_done_3532_ == 0)
{
uint8_t v_contextDependent_3533_; lean_object* v___x_3534_; 
lean_dec_ref_known(v___x_3530_, 1);
v_contextDependent_3533_ = lean_ctor_get_uint8(v_a_3531_, 1);
lean_dec_ref_known(v_a_3531_, 0);
lean_inc_ref(v_e_3431_);
lean_inc(v_val_3447_);
v___x_3534_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(v_val_3447_, v_e_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; uint8_t v___y_3537_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_a_3535_);
if (v_contextDependent_3533_ == 0)
{
lean_dec(v_a_3535_);
v___y_3517_ = v___x_3534_;
goto v___jp_3516_;
}
else
{
if (lean_obj_tag(v_a_3535_) == 0)
{
uint8_t v_contextDependent_3547_; uint8_t v___x_3548_; 
v_contextDependent_3547_ = lean_ctor_get_uint8(v_a_3535_, 1);
v___x_3548_ = lean_bool_not(v_contextDependent_3547_);
v___y_3537_ = v___x_3548_;
goto v___jp_3536_;
}
else
{
uint8_t v_contextDependent_3549_; uint8_t v___x_3550_; 
v_contextDependent_3549_ = lean_ctor_get_uint8(v_a_3535_, sizeof(void*)*2 + 1);
v___x_3550_ = lean_bool_not(v_contextDependent_3549_);
v___y_3537_ = v___x_3550_;
goto v___jp_3536_;
}
}
v___jp_3536_:
{
if (v___y_3537_ == 0)
{
lean_dec(v_a_3535_);
v___y_3517_ = v___x_3534_;
goto v___jp_3516_;
}
else
{
lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3545_; 
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3545_ == 0)
{
lean_object* v_unused_3546_; 
v_unused_3546_ = lean_ctor_get(v___x_3534_, 0);
lean_dec(v_unused_3546_);
v___x_3539_ = v___x_3534_;
v_isShared_3540_ = v_isSharedCheck_3545_;
goto v_resetjp_3538_;
}
else
{
lean_dec(v___x_3534_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3545_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3541_; lean_object* v___x_3543_; 
v___x_3541_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3535_);
lean_inc_ref(v___x_3541_);
if (v_isShared_3540_ == 0)
{
lean_ctor_set(v___x_3539_, 0, v___x_3541_);
v___x_3543_ = v___x_3539_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v___x_3541_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
v___y_3508_ = v___x_3543_;
v_a_3509_ = v___x_3541_;
goto v___jp_3507_;
}
}
}
}
}
else
{
v___y_3517_ = v___x_3534_;
goto v___jp_3516_;
}
}
else
{
lean_dec_ref_known(v_a_3531_, 0);
v___y_3517_ = v___x_3530_;
goto v___jp_3516_;
}
}
else
{
uint8_t v_done_3551_; 
v_done_3551_ = lean_ctor_get_uint8(v_a_3531_, sizeof(void*)*2);
if (v_done_3551_ == 0)
{
lean_object* v_e_x27_3552_; lean_object* v_proof_3553_; uint8_t v_contextDependent_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3590_; 
lean_dec_ref_known(v___x_3530_, 1);
v_e_x27_3552_ = lean_ctor_get(v_a_3531_, 0);
v_proof_3553_ = lean_ctor_get(v_a_3531_, 1);
v_contextDependent_3554_ = lean_ctor_get_uint8(v_a_3531_, sizeof(void*)*2 + 1);
v_isSharedCheck_3590_ = !lean_is_exclusive(v_a_3531_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3556_ = v_a_3531_;
v_isShared_3557_ = v_isSharedCheck_3590_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_proof_3553_);
lean_inc(v_e_x27_3552_);
lean_dec(v_a_3531_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3590_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3558_; 
lean_inc_ref(v_e_x27_3552_);
lean_inc(v_val_3447_);
v___x_3558_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(v_val_3447_, v_e_x27_3552_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v_a_3559_; 
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_a_3559_);
lean_dec_ref_known(v___x_3558_, 1);
if (lean_obj_tag(v_a_3559_) == 0)
{
uint8_t v_done_3560_; uint8_t v_contextDependent_3561_; uint8_t v___y_3563_; 
v_done_3560_ = lean_ctor_get_uint8(v_a_3559_, 0);
v_contextDependent_3561_ = lean_ctor_get_uint8(v_a_3559_, 1);
lean_dec_ref_known(v_a_3559_, 0);
if (v_contextDependent_3554_ == 0)
{
v___y_3563_ = v_contextDependent_3561_;
goto v___jp_3562_;
}
else
{
v___y_3563_ = v_contextDependent_3554_;
goto v___jp_3562_;
}
v___jp_3562_:
{
lean_object* v___x_3565_; 
lean_inc_ref(v_e_x27_3552_);
if (v_isShared_3557_ == 0)
{
v___x_3565_ = v___x_3556_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_e_x27_3552_);
lean_ctor_set(v_reuseFailAlloc_3566_, 1, v_proof_3553_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
lean_ctor_set_uint8(v___x_3565_, sizeof(void*)*2, v_done_3560_);
lean_ctor_set_uint8(v___x_3565_, sizeof(void*)*2 + 1, v___y_3563_);
v_a_3452_ = v___x_3565_;
v_e_x27_3453_ = v_e_x27_3552_;
goto v___jp_3451_;
}
}
}
else
{
lean_object* v_e_x27_3567_; lean_object* v_proof_3568_; uint8_t v_done_3569_; uint8_t v_contextDependent_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3589_; 
lean_del_object(v___x_3556_);
v_e_x27_3567_ = lean_ctor_get(v_a_3559_, 0);
v_proof_3568_ = lean_ctor_get(v_a_3559_, 1);
v_done_3569_ = lean_ctor_get_uint8(v_a_3559_, sizeof(void*)*2);
v_contextDependent_3570_ = lean_ctor_get_uint8(v_a_3559_, sizeof(void*)*2 + 1);
v_isSharedCheck_3589_ = !lean_is_exclusive(v_a_3559_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3572_ = v_a_3559_;
v_isShared_3573_ = v_isSharedCheck_3589_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_proof_3568_);
lean_inc(v_e_x27_3567_);
lean_dec(v_a_3559_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3589_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3574_; 
lean_inc_ref(v_e_x27_3567_);
lean_inc_ref(v_e_3431_);
v___x_3574_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_3431_, v_e_x27_3552_, v_proof_3553_, v_e_x27_3567_, v_proof_3568_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_);
if (lean_obj_tag(v___x_3574_) == 0)
{
lean_object* v_a_3575_; uint8_t v___y_3577_; 
v_a_3575_ = lean_ctor_get(v___x_3574_, 0);
lean_inc(v_a_3575_);
lean_dec_ref_known(v___x_3574_, 1);
if (v_contextDependent_3554_ == 0)
{
v___y_3577_ = v_contextDependent_3570_;
goto v___jp_3576_;
}
else
{
v___y_3577_ = v_contextDependent_3554_;
goto v___jp_3576_;
}
v___jp_3576_:
{
lean_object* v___x_3579_; 
lean_inc_ref(v_e_x27_3567_);
if (v_isShared_3573_ == 0)
{
lean_ctor_set(v___x_3572_, 1, v_a_3575_);
v___x_3579_ = v___x_3572_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_e_x27_3567_);
lean_ctor_set(v_reuseFailAlloc_3580_, 1, v_a_3575_);
lean_ctor_set_uint8(v_reuseFailAlloc_3580_, sizeof(void*)*2, v_done_3569_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
lean_ctor_set_uint8(v___x_3579_, sizeof(void*)*2 + 1, v___y_3577_);
v_a_3452_ = v___x_3579_;
v_e_x27_3453_ = v_e_x27_3567_;
goto v___jp_3451_;
}
}
}
else
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3588_; 
lean_del_object(v___x_3572_);
lean_dec_ref(v_e_x27_3567_);
lean_del_object(v___x_3449_);
lean_dec(v_val_3447_);
lean_dec_ref(v_e_3431_);
v_a_3581_ = lean_ctor_get(v___x_3574_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3574_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3583_ = v___x_3574_;
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3574_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3586_; 
if (v_isShared_3584_ == 0)
{
v___x_3586_ = v___x_3583_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_a_3581_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_3556_);
lean_dec_ref(v_proof_3553_);
lean_dec_ref(v_e_x27_3552_);
v___y_3517_ = v___x_3558_;
goto v___jp_3516_;
}
}
}
else
{
lean_dec_ref_known(v_a_3531_, 2);
v___y_3517_ = v___x_3530_;
goto v___jp_3516_;
}
}
}
else
{
v___y_3517_ = v___x_3530_;
goto v___jp_3516_;
}
}
else
{
lean_object* v___x_3591_; lean_object* v___x_3593_; 
lean_dec(v_a_3520_);
lean_del_object(v___x_3449_);
lean_dec(v_val_3447_);
lean_dec_ref(v_e_3431_);
v___x_3591_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__10));
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v___x_3591_);
v___x_3593_ = v___x_3522_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3591_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
}
else
{
lean_object* v___x_3597_; lean_object* v___x_3598_; 
lean_dec(v___x_3446_);
lean_dec_ref(v_e_3431_);
v___x_3597_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__10));
v___x_3598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3597_);
return v___x_3598_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher___boxed(lean_object* v_e_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_){
_start:
{
lean_object* v_res_3610_; 
v_res_3610_ = l_Lean_Meta_Tactic_Cbv_tryMatcher(v_e_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_);
lean_dec(v_a_3608_);
lean_dec_ref(v_a_3607_);
lean_dec(v_a_3606_);
lean_dec_ref(v_a_3605_);
lean_dec(v_a_3604_);
lean_dec_ref(v_a_3603_);
lean_dec(v_a_3602_);
lean_dec_ref(v_a_3601_);
lean_dec(v_a_3600_);
return v_res_3610_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Init_Sym_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_Opaque(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_NoncomputableAttr(uint8_t builtin);
lean_object* runtime_initialize_Init_CbvSimproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_ControlFlow(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Sym_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_Opaque(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_NoncomputableAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Cbv_ControlFlow(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_ControlFlow(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Init_Sym_Lemmas(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cbv_Opaque(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(uint8_t builtin);
lean_object* initialize_Lean_Compiler_NoncomputableAttr(uint8_t builtin);
lean_object* initialize_Init_CbvSimproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Cbv_ControlFlow(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Sym_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv_Opaque(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_NoncomputableAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_ControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Cbv_ControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Cbv_ControlFlow(builtin);
}
#ifdef __cplusplus
}
#endif
