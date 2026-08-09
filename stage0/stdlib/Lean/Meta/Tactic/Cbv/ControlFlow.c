// Lean compiler output
// Module: Lean.Meta.Tactic.Cbv.ControlFlow
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Sym.Simp.Result import Lean.Meta.Sym.Simp.Rewrite import Lean.Meta.Sym.Simp.ControlFlow import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.InferType import Lean.Meta.Sym.Simp.App import Lean.Meta.SynthInstance import Lean.Meta.WHNF import Lean.Meta.AppBuilder import Init.Sym.Lemmas import Lean.Meta.Tactic.Cbv.TheoremsLookup import Lean.Meta.Tactic.Cbv.Opaque import Lean.Meta.Tactic.Cbv.CbvEvalExt import Lean.Compiler.ComputableExt import Init.CbvSimproc import Lean.Meta.Tactic.Cbv.CbvSimproc
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_canUnfoldDefault(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_canUnfoldAtMatcher(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkRflResult(uint8_t, uint8_t);
lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Tactic_Cbv_getCbvEvalLemmas___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_computableExt;
lean_object* l_Lean_isComputableOrIrrelevant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getBoundedAppFn(lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Expr_replaceFn(lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpCond(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpCond___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_isCbvNoncomputable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_isCbvNoncomputable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "ite_eq_right_of_eq_false"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__7_value),LEAN_SCALAR_PTR_LITERAL(85, 26, 223, 35, 242, 130, 83, 13)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ite_eq_left_of_eq_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__9_value),LEAN_SCALAR_PTR_LITERAL(73, 84, 15, 184, 226, 12, 142, 9)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Cbv"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(93, 144, 236, 69, 149, 78, 215, 228)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__9_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ControlFlow"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__9_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__9_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__10_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__9_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(153, 75, 2, 199, 142, 91, 93, 201)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__10_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__10_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__11_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__10_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(252, 60, 118, 117, 62, 213, 206, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__11_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__11_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__12_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__11_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value),LEAN_SCALAR_PTR_LITERAL(157, 4, 12, 27, 152, 101, 133, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__12_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__12_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__13_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__12_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(245, 145, 82, 72, 75, 94, 216, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__13_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__13_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__14_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__13_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value),LEAN_SCALAR_PTR_LITERAL(144, 2, 145, 22, 246, 43, 198, 251)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__14_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__14_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__15_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__15_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__15_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__14_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__15_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(124, 100, 175, 78, 162, 84, 105, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__17_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "simpIteCbv"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__17_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__17_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__17_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(74, 233, 198, 147, 223, 175, 34, 106)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__19_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__1_value),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__19_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__19_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__20_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__19_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__20_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__20_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_19____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "dite_eq_right_of_eq_false"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(181, 72, 248, 145, 136, 9, 228, 221)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "dite_eq_left_of_eq_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(36, 253, 19, 136, 170, 78, 36, 13)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "simpDIteCbv"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(190, 122, 172, 160, 23, 10, 186, 34)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1_value),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_17__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_17__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_17__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_19____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "simpDecideCbv"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(115, 206, 175, 80, 231, 183, 173, 95)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_14__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_14__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_14____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_simpCond___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__13_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(76, 195, 71, 185, 148, 180, 220, 212)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(30, 114, 151, 242, 65, 185, 169, 185)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "simpCbvCond"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(159, 133, 67, 239, 99, 33, 147, 98)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_18____boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "simpDecidableRec"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18__value),LEAN_SCALAR_PTR_LITERAL(80, 52, 244, 154, 141, 147, 125, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rec"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18__value),LEAN_SCALAR_PTR_LITERAL(158, 146, 92, 125, 27, 135, 153, 152)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18__value),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_20_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_20____boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_isCbvNoncomputable(lean_object* v_p_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Lean_Meta_Tactic_Cbv_getCbvEvalLemmas___redArg(v_p_1_, v_a_5_);
if (lean_obj_tag(v___x_7_) == 0)
{
lean_object* v_a_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_37_; 
v_a_8_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_37_ == 0)
{
v___x_10_ = v___x_7_;
v_isShared_11_ = v_isSharedCheck_37_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_a_8_);
lean_dec(v___x_7_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_37_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
if (lean_obj_tag(v_a_8_) == 0)
{
lean_object* v___x_12_; lean_object* v_toEnvExtension_13_; lean_object* v_asyncMode_14_; lean_object* v___x_15_; 
lean_del_object(v___x_10_);
v___x_12_ = l_Lean_computableExt;
v_toEnvExtension_13_ = lean_ctor_get(v___x_12_, 0);
v_asyncMode_14_ = lean_ctor_get(v_toEnvExtension_13_, 2);
v___x_15_ = l_Lean_isComputableOrIrrelevant(v_p_1_, v_asyncMode_14_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_15_) == 0)
{
lean_object* v_a_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_31_; 
v_a_16_ = lean_ctor_get(v___x_15_, 0);
v_isSharedCheck_31_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_31_ == 0)
{
v___x_18_ = v___x_15_;
v_isShared_19_ = v_isSharedCheck_31_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_a_16_);
lean_dec(v___x_15_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_31_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
uint8_t v___x_20_; 
v___x_20_ = lean_unbox(v_a_16_);
lean_dec(v_a_16_);
if (v___x_20_ == 0)
{
uint8_t v___x_21_; lean_object* v___x_22_; lean_object* v___x_24_; 
v___x_21_ = 1;
v___x_22_ = lean_box(v___x_21_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 0, v___x_22_);
v___x_24_ = v___x_18_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v___x_22_);
v___x_24_ = v_reuseFailAlloc_25_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
return v___x_24_;
}
}
else
{
uint8_t v___x_26_; lean_object* v___x_27_; lean_object* v___x_29_; 
v___x_26_ = 0;
v___x_27_ = lean_box(v___x_26_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 0, v___x_27_);
v___x_29_ = v___x_18_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v___x_27_);
v___x_29_ = v_reuseFailAlloc_30_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
return v___x_29_;
}
}
}
}
else
{
return v___x_15_;
}
}
else
{
uint8_t v___x_32_; lean_object* v___x_33_; lean_object* v___x_35_; 
lean_dec_ref_known(v_a_8_, 1);
lean_dec(v_p_1_);
v___x_32_ = 0;
v___x_33_ = lean_box(v___x_32_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 0, v___x_33_);
v___x_35_ = v___x_10_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v___x_33_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
}
else
{
lean_object* v_a_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_45_; 
lean_dec(v_p_1_);
v_a_38_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_45_ == 0)
{
v___x_40_ = v___x_7_;
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_a_38_);
lean_dec(v___x_7_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_43_; 
if (v_isShared_41_ == 0)
{
v___x_43_ = v___x_40_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_a_38_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_isCbvNoncomputable___boxed(lean_object* v_p_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_isCbvNoncomputable(v_p_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
lean_dec(v_a_48_);
lean_dec_ref(v_a_47_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0___redArg(lean_object* v_as_53_, size_t v_i_54_, size_t v_stop_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
uint8_t v___x_61_; 
v___x_61_ = lean_usize_dec_eq(v_i_54_, v_stop_55_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_array_uget_borrowed(v_as_53_, v_i_54_);
lean_inc(v___x_62_);
v___x_63_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_isCbvNoncomputable(v___x_62_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v_a_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_75_; 
v_a_64_ = lean_ctor_get(v___x_63_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_75_ == 0)
{
v___x_66_ = v___x_63_;
v_isShared_67_ = v_isSharedCheck_75_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_a_64_);
lean_dec(v___x_63_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_75_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
uint8_t v___x_68_; 
v___x_68_ = lean_unbox(v_a_64_);
if (v___x_68_ == 0)
{
size_t v___x_69_; size_t v___x_70_; 
lean_del_object(v___x_66_);
lean_dec(v_a_64_);
v___x_69_ = ((size_t)1ULL);
v___x_70_ = lean_usize_add(v_i_54_, v___x_69_);
v_i_54_ = v___x_70_;
goto _start;
}
else
{
lean_object* v___x_73_; 
if (v_isShared_67_ == 0)
{
v___x_73_ = v___x_66_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_a_64_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
}
else
{
return v___x_63_;
}
}
else
{
uint8_t v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = 0;
v___x_77_ = lean_box(v___x_76_);
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0___redArg___boxed(lean_object* v_as_79_, lean_object* v_i_80_, lean_object* v_stop_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
size_t v_i_boxed_87_; size_t v_stop_boxed_88_; lean_object* v_res_89_; 
v_i_boxed_87_ = lean_unbox_usize(v_i_80_);
lean_dec(v_i_80_);
v_stop_boxed_88_ = lean_unbox_usize(v_stop_81_);
lean_dec(v_stop_81_);
v_res_89_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0___redArg(v_as_79_, v_i_boxed_87_, v_stop_boxed_88_, v___y_82_, v___y_83_, v___y_84_, v___y_85_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec_ref(v_as_79_);
return v_res_89_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__2(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_box(0);
v___x_94_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__1));
v___x_95_ = l_Lean_mkConst(v___x_94_, v___x_93_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance(lean_object* v_p_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_104_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__2);
v___x_105_ = l_Lean_Expr_app___override(v___x_104_, v_p_96_);
v___x_106_ = lean_box(0);
v___x_107_ = l_Lean_Meta_trySynthInstance(v___x_105_, v___x_106_, v_a_99_, v_a_100_, v_a_101_, v_a_102_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_165_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_165_ == 0)
{
v___x_110_ = v___x_107_;
v_isShared_111_ = v_isSharedCheck_165_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_107_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_165_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
if (lean_obj_tag(v_a_108_) == 1)
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_161_; 
lean_del_object(v___x_110_);
v_a_112_ = lean_ctor_get(v_a_108_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v_a_108_);
if (v_isSharedCheck_161_ == 0)
{
v___x_114_ = v_a_108_;
v_isShared_115_ = v_isSharedCheck_161_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v_a_108_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_161_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
lean_inc(v_a_112_);
v___x_137_ = l_Lean_Expr_getUsedConstants(v_a_112_);
v___x_138_ = lean_unsigned_to_nat(0u);
v___x_139_ = lean_array_get_size(v___x_137_);
v___x_140_ = lean_nat_dec_lt(v___x_138_, v___x_139_);
if (v___x_140_ == 0)
{
lean_dec_ref(v___x_137_);
goto v___jp_116_;
}
else
{
if (v___x_140_ == 0)
{
lean_dec_ref(v___x_137_);
goto v___jp_116_;
}
else
{
size_t v___x_141_; size_t v___x_142_; lean_object* v___x_143_; 
v___x_141_ = ((size_t)0ULL);
v___x_142_ = lean_usize_of_nat(v___x_139_);
v___x_143_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0___redArg(v___x_137_, v___x_141_, v___x_142_, v_a_99_, v_a_100_, v_a_101_, v_a_102_);
lean_dec_ref(v___x_137_);
if (lean_obj_tag(v___x_143_) == 0)
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_152_; 
v_a_144_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_152_ == 0)
{
v___x_146_ = v___x_143_;
v_isShared_147_ = v_isSharedCheck_152_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_143_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_152_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
uint8_t v___x_148_; 
v___x_148_ = lean_unbox(v_a_144_);
lean_dec(v_a_144_);
if (v___x_148_ == 0)
{
lean_del_object(v___x_146_);
goto v___jp_116_;
}
else
{
lean_object* v___x_150_; 
lean_del_object(v___x_114_);
lean_dec(v_a_112_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 0, v___x_106_);
v___x_150_ = v___x_146_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_106_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
else
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_160_; 
lean_del_object(v___x_114_);
lean_dec(v_a_112_);
v_a_153_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_160_ == 0)
{
v___x_155_ = v___x_143_;
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_143_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_158_; 
if (v_isShared_156_ == 0)
{
v___x_158_ = v___x_155_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_a_153_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
}
v___jp_116_:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_Meta_Sym_shareCommon(v_a_112_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_128_; 
v_a_118_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_128_ == 0)
{
v___x_120_ = v___x_117_;
v_isShared_121_ = v_isSharedCheck_128_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_117_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_128_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v_a_118_);
v___x_123_ = v___x_114_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_118_);
v___x_123_ = v_reuseFailAlloc_127_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
lean_object* v___x_125_; 
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v___x_123_);
v___x_125_ = v___x_120_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_123_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
else
{
lean_object* v_a_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_136_; 
lean_del_object(v___x_114_);
v_a_129_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_136_ == 0)
{
v___x_131_ = v___x_117_;
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_a_129_);
lean_dec(v___x_117_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_134_; 
if (v_isShared_132_ == 0)
{
v___x_134_ = v___x_131_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_a_129_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
}
}
else
{
lean_object* v___x_163_; 
lean_dec(v_a_108_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_106_);
v___x_163_ = v___x_110_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_106_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
}
else
{
lean_object* v_a_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_173_; 
v_a_166_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_173_ == 0)
{
v___x_168_ = v___x_107_;
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_a_166_);
lean_dec(v___x_107_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_171_; 
if (v_isShared_169_ == 0)
{
v___x_171_ = v___x_168_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_a_166_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___boxed(lean_object* v_p_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance(v_p_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
lean_dec(v_a_178_);
lean_dec_ref(v_a_177_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0(lean_object* v_as_183_, size_t v_i_184_, size_t v_stop_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0___redArg(v_as_183_, v_i_184_, v_stop_185_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0___boxed(lean_object* v_as_194_, lean_object* v_i_195_, lean_object* v_stop_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
size_t v_i_boxed_204_; size_t v_stop_boxed_205_; lean_object* v_res_206_; 
v_i_boxed_204_ = lean_unbox_usize(v_i_195_);
lean_dec(v_i_195_);
v_stop_boxed_205_ = lean_unbox_usize(v_stop_196_);
lean_dec(v_stop_196_);
v_res_206_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0(v_as_194_, v_i_boxed_204_, v_stop_boxed_205_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec_ref(v_as_194_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable(lean_object* v_f_227_, lean_object* v_00_u03b1_228_, lean_object* v_c_229_, lean_object* v_inst_230_, lean_object* v_a_231_, lean_object* v_b_232_, lean_object* v_instToMatch_233_, lean_object* v_fallback_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_instToMatch_233_, v_a_241_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_280_; 
v_a_246_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_280_ == 0)
{
v___x_248_ = v___x_245_;
v_isShared_249_ = v_isSharedCheck_280_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_245_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_280_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_250_ = l_Lean_Expr_cleanupAnnotations(v_a_246_);
v___x_251_ = l_Lean_Expr_isApp(v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; 
lean_dec_ref(v___x_250_);
lean_del_object(v___x_248_);
lean_dec_ref(v_b_232_);
lean_dec_ref(v_a_231_);
lean_dec_ref(v_inst_230_);
lean_dec_ref(v_c_229_);
lean_dec_ref(v_00_u03b1_228_);
lean_inc(v_a_243_);
lean_inc_ref(v_a_242_);
lean_inc(v_a_241_);
lean_inc_ref(v_a_240_);
lean_inc(v_a_239_);
lean_inc_ref(v_a_238_);
lean_inc(v_a_237_);
lean_inc_ref(v_a_236_);
lean_inc(v_a_235_);
v___x_252_ = lean_apply_10(v_fallback_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, lean_box(0));
return v___x_252_;
}
else
{
lean_object* v_arg_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v_arg_253_ = lean_ctor_get(v___x_250_, 1);
lean_inc_ref(v_arg_253_);
v___x_254_ = l_Lean_Expr_appFnCleanup___redArg(v___x_250_);
v___x_255_ = l_Lean_Expr_isApp(v___x_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; 
lean_dec_ref(v___x_254_);
lean_dec_ref(v_arg_253_);
lean_del_object(v___x_248_);
lean_dec_ref(v_b_232_);
lean_dec_ref(v_a_231_);
lean_dec_ref(v_inst_230_);
lean_dec_ref(v_c_229_);
lean_dec_ref(v_00_u03b1_228_);
lean_inc(v_a_243_);
lean_inc_ref(v_a_242_);
lean_inc(v_a_241_);
lean_inc_ref(v_a_240_);
lean_inc(v_a_239_);
lean_inc_ref(v_a_238_);
lean_inc(v_a_237_);
lean_inc_ref(v_a_236_);
lean_inc(v_a_235_);
v___x_256_ = lean_apply_10(v_fallback_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, lean_box(0));
return v___x_256_;
}
else
{
lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_257_ = l_Lean_Expr_appFnCleanup___redArg(v___x_254_);
v___x_258_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_259_ = l_Lean_Expr_isConstOf(v___x_257_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_260_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3));
v___x_261_ = l_Lean_Expr_isConstOf(v___x_257_, v___x_260_);
lean_dec_ref(v___x_257_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; 
lean_dec_ref(v_arg_253_);
lean_del_object(v___x_248_);
lean_dec_ref(v_b_232_);
lean_dec_ref(v_a_231_);
lean_dec_ref(v_inst_230_);
lean_dec_ref(v_c_229_);
lean_dec_ref(v_00_u03b1_228_);
lean_inc(v_a_243_);
lean_inc_ref(v_a_242_);
lean_inc(v_a_241_);
lean_inc_ref(v_a_240_);
lean_inc(v_a_239_);
lean_inc_ref(v_a_238_);
lean_inc(v_a_237_);
lean_inc_ref(v_a_236_);
lean_inc(v_a_235_);
v___x_262_ = lean_apply_10(v_fallback_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, lean_box(0));
return v___x_262_;
}
else
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_269_; 
lean_dec_ref(v_fallback_234_);
v___x_263_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7));
v___x_264_ = l_Lean_Expr_constLevels_x21(v_f_227_);
v___x_265_ = l_Lean_mkConst(v___x_263_, v___x_264_);
lean_inc_ref(v_a_231_);
v___x_266_ = l_Lean_mkApp6(v___x_265_, v_00_u03b1_228_, v_c_229_, v_inst_230_, v_a_231_, v_b_232_, v_arg_253_);
v___x_267_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_267_, 0, v_a_231_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*2, v___x_259_);
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*2 + 1, v___x_259_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 0, v___x_267_);
v___x_269_ = v___x_248_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_267_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
else
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
lean_dec_ref(v___x_257_);
lean_dec_ref(v_fallback_234_);
v___x_271_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__9));
v___x_272_ = l_Lean_Expr_constLevels_x21(v_f_227_);
v___x_273_ = l_Lean_mkConst(v___x_271_, v___x_272_);
lean_inc_ref(v_b_232_);
v___x_274_ = l_Lean_mkApp6(v___x_273_, v_00_u03b1_228_, v_c_229_, v_inst_230_, v_a_231_, v_b_232_, v_arg_253_);
v___x_275_ = 0;
v___x_276_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_276_, 0, v_b_232_);
lean_ctor_set(v___x_276_, 1, v___x_274_);
lean_ctor_set_uint8(v___x_276_, sizeof(void*)*2, v___x_275_);
lean_ctor_set_uint8(v___x_276_, sizeof(void*)*2 + 1, v___x_275_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 0, v___x_276_);
v___x_278_ = v___x_248_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_276_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
}
}
else
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
lean_dec_ref(v_fallback_234_);
lean_dec_ref(v_b_232_);
lean_dec_ref(v_a_231_);
lean_dec_ref(v_inst_230_);
lean_dec_ref(v_c_229_);
lean_dec_ref(v_00_u03b1_228_);
v_a_281_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_288_ == 0)
{
v___x_283_ = v___x_245_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_245_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_a_281_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___boxed(lean_object** _args){
lean_object* v_f_289_ = _args[0];
lean_object* v_00_u03b1_290_ = _args[1];
lean_object* v_c_291_ = _args[2];
lean_object* v_inst_292_ = _args[3];
lean_object* v_a_293_ = _args[4];
lean_object* v_b_294_ = _args[5];
lean_object* v_instToMatch_295_ = _args[6];
lean_object* v_fallback_296_ = _args[7];
lean_object* v_a_297_ = _args[8];
lean_object* v_a_298_ = _args[9];
lean_object* v_a_299_ = _args[10];
lean_object* v_a_300_ = _args[11];
lean_object* v_a_301_ = _args[12];
lean_object* v_a_302_ = _args[13];
lean_object* v_a_303_ = _args[14];
lean_object* v_a_304_ = _args[15];
lean_object* v_a_305_ = _args[16];
lean_object* v_a_306_ = _args[17];
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable(v_f_289_, v_00_u03b1_290_, v_c_291_, v_inst_292_, v_a_293_, v_b_294_, v_instToMatch_295_, v_fallback_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec(v_a_297_);
lean_dec_ref(v_f_289_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(lean_object* v_f_318_, lean_object* v_00_u03b1_319_, lean_object* v_c_320_, lean_object* v_inst_321_, lean_object* v_a_322_, lean_object* v_b_323_, lean_object* v_c_x27_324_, lean_object* v_h_325_, lean_object* v_inst_x27_326_, lean_object* v_fallback_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_inst_x27_326_, v_a_334_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_373_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_373_ == 0)
{
v___x_341_ = v___x_338_;
v_isShared_342_ = v_isSharedCheck_373_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_338_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_373_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = l_Lean_Expr_cleanupAnnotations(v_a_339_);
v___x_344_ = l_Lean_Expr_isApp(v___x_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; 
lean_dec_ref(v___x_343_);
lean_del_object(v___x_341_);
lean_dec_ref(v_h_325_);
lean_dec_ref(v_c_x27_324_);
lean_dec_ref(v_b_323_);
lean_dec_ref(v_a_322_);
lean_dec_ref(v_inst_321_);
lean_dec_ref(v_c_320_);
lean_dec_ref(v_00_u03b1_319_);
lean_inc(v_a_336_);
lean_inc_ref(v_a_335_);
lean_inc(v_a_334_);
lean_inc_ref(v_a_333_);
lean_inc(v_a_332_);
lean_inc_ref(v_a_331_);
lean_inc(v_a_330_);
lean_inc_ref(v_a_329_);
lean_inc(v_a_328_);
v___x_345_ = lean_apply_10(v_fallback_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, lean_box(0));
return v___x_345_;
}
else
{
lean_object* v_arg_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v_arg_346_ = lean_ctor_get(v___x_343_, 1);
lean_inc_ref(v_arg_346_);
v___x_347_ = l_Lean_Expr_appFnCleanup___redArg(v___x_343_);
v___x_348_ = l_Lean_Expr_isApp(v___x_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; 
lean_dec_ref(v___x_347_);
lean_dec_ref(v_arg_346_);
lean_del_object(v___x_341_);
lean_dec_ref(v_h_325_);
lean_dec_ref(v_c_x27_324_);
lean_dec_ref(v_b_323_);
lean_dec_ref(v_a_322_);
lean_dec_ref(v_inst_321_);
lean_dec_ref(v_c_320_);
lean_dec_ref(v_00_u03b1_319_);
lean_inc(v_a_336_);
lean_inc_ref(v_a_335_);
lean_inc(v_a_334_);
lean_inc_ref(v_a_333_);
lean_inc(v_a_332_);
lean_inc_ref(v_a_331_);
lean_inc(v_a_330_);
lean_inc_ref(v_a_329_);
lean_inc(v_a_328_);
v___x_349_ = lean_apply_10(v_fallback_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, lean_box(0));
return v___x_349_;
}
else
{
lean_object* v___x_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_350_ = l_Lean_Expr_appFnCleanup___redArg(v___x_347_);
v___x_351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_352_ = l_Lean_Expr_isConstOf(v___x_350_, v___x_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_353_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3));
v___x_354_ = l_Lean_Expr_isConstOf(v___x_350_, v___x_353_);
lean_dec_ref(v___x_350_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; 
lean_dec_ref(v_arg_346_);
lean_del_object(v___x_341_);
lean_dec_ref(v_h_325_);
lean_dec_ref(v_c_x27_324_);
lean_dec_ref(v_b_323_);
lean_dec_ref(v_a_322_);
lean_dec_ref(v_inst_321_);
lean_dec_ref(v_c_320_);
lean_dec_ref(v_00_u03b1_319_);
lean_inc(v_a_336_);
lean_inc_ref(v_a_335_);
lean_inc(v_a_334_);
lean_inc_ref(v_a_333_);
lean_inc(v_a_332_);
lean_inc_ref(v_a_331_);
lean_inc(v_a_330_);
lean_inc_ref(v_a_329_);
lean_inc(v_a_328_);
v___x_355_ = lean_apply_10(v_fallback_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, lean_box(0));
return v___x_355_;
}
else
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
lean_dec_ref(v_fallback_327_);
v___x_356_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__1));
v___x_357_ = l_Lean_Expr_constLevels_x21(v_f_318_);
v___x_358_ = l_Lean_mkConst(v___x_356_, v___x_357_);
lean_inc_ref(v_a_322_);
v___x_359_ = l_Lean_mkApp8(v___x_358_, v_00_u03b1_319_, v_c_320_, v_inst_321_, v_a_322_, v_b_323_, v_c_x27_324_, v_h_325_, v_arg_346_);
v___x_360_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_360_, 0, v_a_322_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*2, v___x_352_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*2 + 1, v___x_352_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v___x_360_);
v___x_362_ = v___x_341_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_360_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
else
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
lean_dec_ref(v___x_350_);
lean_dec_ref(v_fallback_327_);
v___x_364_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__3));
v___x_365_ = l_Lean_Expr_constLevels_x21(v_f_318_);
v___x_366_ = l_Lean_mkConst(v___x_364_, v___x_365_);
lean_inc_ref(v_b_323_);
v___x_367_ = l_Lean_mkApp8(v___x_366_, v_00_u03b1_319_, v_c_320_, v_inst_321_, v_a_322_, v_b_323_, v_c_x27_324_, v_h_325_, v_arg_346_);
v___x_368_ = 0;
v___x_369_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_369_, 0, v_b_323_);
lean_ctor_set(v___x_369_, 1, v___x_367_);
lean_ctor_set_uint8(v___x_369_, sizeof(void*)*2, v___x_368_);
lean_ctor_set_uint8(v___x_369_, sizeof(void*)*2 + 1, v___x_368_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v___x_369_);
v___x_371_ = v___x_341_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec_ref(v_fallback_327_);
lean_dec_ref(v_h_325_);
lean_dec_ref(v_c_x27_324_);
lean_dec_ref(v_b_323_);
lean_dec_ref(v_a_322_);
lean_dec_ref(v_inst_321_);
lean_dec_ref(v_c_320_);
lean_dec_ref(v_00_u03b1_319_);
v_a_374_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_338_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_338_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___boxed(lean_object** _args){
lean_object* v_f_382_ = _args[0];
lean_object* v_00_u03b1_383_ = _args[1];
lean_object* v_c_384_ = _args[2];
lean_object* v_inst_385_ = _args[3];
lean_object* v_a_386_ = _args[4];
lean_object* v_b_387_ = _args[5];
lean_object* v_c_x27_388_ = _args[6];
lean_object* v_h_389_ = _args[7];
lean_object* v_inst_x27_390_ = _args[8];
lean_object* v_fallback_391_ = _args[9];
lean_object* v_a_392_ = _args[10];
lean_object* v_a_393_ = _args[11];
lean_object* v_a_394_ = _args[12];
lean_object* v_a_395_ = _args[13];
lean_object* v_a_396_ = _args[14];
lean_object* v_a_397_ = _args[15];
lean_object* v_a_398_ = _args[16];
lean_object* v_a_399_ = _args[17];
lean_object* v_a_400_ = _args[18];
lean_object* v_a_401_ = _args[19];
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(v_f_382_, v_00_u03b1_383_, v_c_384_, v_inst_385_, v_a_386_, v_b_387_, v_c_x27_388_, v_h_389_, v_inst_x27_390_, v_fallback_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
lean_dec(v_a_400_);
lean_dec_ref(v_a_399_);
lean_dec(v_a_398_);
lean_dec_ref(v_a_397_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_f_382_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(lean_object* v_f_403_, lean_object* v_00_u03b1_404_, lean_object* v_c_405_, lean_object* v_inst_406_, lean_object* v_a_407_, lean_object* v_b_408_, lean_object* v_fallback_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v___x_420_; 
lean_inc(v_a_418_);
lean_inc_ref(v_a_417_);
lean_inc(v_a_416_);
lean_inc_ref(v_a_415_);
lean_inc(v_a_414_);
lean_inc_ref(v_a_413_);
lean_inc(v_a_412_);
lean_inc_ref(v_a_411_);
lean_inc(v_a_410_);
lean_inc_ref(v_inst_406_);
v___x_420_ = lean_sym_simp(v_inst_406_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_a_421_);
lean_dec_ref_known(v___x_420_, 1);
if (lean_obj_tag(v_a_421_) == 0)
{
uint8_t v_contextDependent_422_; lean_object* v___x_423_; 
v_contextDependent_422_ = lean_ctor_get_uint8(v_a_421_, 1);
lean_dec_ref_known(v_a_421_, 0);
lean_inc_ref(v_inst_406_);
v___x_423_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable(v_f_403_, v_00_u03b1_404_, v_c_405_, v_inst_406_, v_a_407_, v_b_408_, v_inst_406_, v_fallback_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; uint8_t v___y_426_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_a_424_);
if (v_contextDependent_422_ == 0)
{
lean_dec(v_a_424_);
return v___x_423_;
}
else
{
if (lean_obj_tag(v_a_424_) == 0)
{
uint8_t v_contextDependent_436_; 
v_contextDependent_436_ = lean_ctor_get_uint8(v_a_424_, 1);
v___y_426_ = v_contextDependent_436_;
goto v___jp_425_;
}
else
{
uint8_t v_contextDependent_437_; 
v_contextDependent_437_ = lean_ctor_get_uint8(v_a_424_, sizeof(void*)*2 + 1);
v___y_426_ = v_contextDependent_437_;
goto v___jp_425_;
}
}
v___jp_425_:
{
if (v___y_426_ == 0)
{
lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_434_; 
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_434_ == 0)
{
lean_object* v_unused_435_; 
v_unused_435_ = lean_ctor_get(v___x_423_, 0);
lean_dec(v_unused_435_);
v___x_428_ = v___x_423_;
v_isShared_429_ = v_isSharedCheck_434_;
goto v_resetjp_427_;
}
else
{
lean_dec(v___x_423_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_434_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_430_; lean_object* v___x_432_; 
v___x_430_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_424_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_430_);
v___x_432_ = v___x_428_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
else
{
lean_dec(v_a_424_);
return v___x_423_;
}
}
}
else
{
return v___x_423_;
}
}
else
{
lean_object* v_e_x27_438_; uint8_t v_contextDependent_439_; lean_object* v___x_440_; 
v_e_x27_438_ = lean_ctor_get(v_a_421_, 0);
lean_inc_ref(v_e_x27_438_);
v_contextDependent_439_ = lean_ctor_get_uint8(v_a_421_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_421_, 2);
v___x_440_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable(v_f_403_, v_00_u03b1_404_, v_c_405_, v_inst_406_, v_a_407_, v_b_408_, v_e_x27_438_, v_fallback_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; uint8_t v___y_443_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
if (v_contextDependent_439_ == 0)
{
lean_dec(v_a_441_);
return v___x_440_;
}
else
{
if (lean_obj_tag(v_a_441_) == 0)
{
uint8_t v_contextDependent_453_; 
v_contextDependent_453_ = lean_ctor_get_uint8(v_a_441_, 1);
v___y_443_ = v_contextDependent_453_;
goto v___jp_442_;
}
else
{
uint8_t v_contextDependent_454_; 
v_contextDependent_454_ = lean_ctor_get_uint8(v_a_441_, sizeof(void*)*2 + 1);
v___y_443_ = v_contextDependent_454_;
goto v___jp_442_;
}
}
v___jp_442_:
{
if (v___y_443_ == 0)
{
lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_451_; 
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_451_ == 0)
{
lean_object* v_unused_452_; 
v_unused_452_ = lean_ctor_get(v___x_440_, 0);
lean_dec(v_unused_452_);
v___x_445_ = v___x_440_;
v_isShared_446_ = v_isSharedCheck_451_;
goto v_resetjp_444_;
}
else
{
lean_dec(v___x_440_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_451_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_447_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_441_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v___x_447_);
v___x_449_ = v___x_445_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
else
{
lean_dec(v_a_441_);
return v___x_440_;
}
}
}
else
{
return v___x_440_;
}
}
}
else
{
lean_dec_ref(v_fallback_409_);
lean_dec_ref(v_b_408_);
lean_dec_ref(v_a_407_);
lean_dec_ref(v_inst_406_);
lean_dec_ref(v_c_405_);
lean_dec_ref(v_00_u03b1_404_);
return v___x_420_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___boxed(lean_object** _args){
lean_object* v_f_455_ = _args[0];
lean_object* v_00_u03b1_456_ = _args[1];
lean_object* v_c_457_ = _args[2];
lean_object* v_inst_458_ = _args[3];
lean_object* v_a_459_ = _args[4];
lean_object* v_b_460_ = _args[5];
lean_object* v_fallback_461_ = _args[6];
lean_object* v_a_462_ = _args[7];
lean_object* v_a_463_ = _args[8];
lean_object* v_a_464_ = _args[9];
lean_object* v_a_465_ = _args[10];
lean_object* v_a_466_ = _args[11];
lean_object* v_a_467_ = _args[12];
lean_object* v_a_468_ = _args[13];
lean_object* v_a_469_ = _args[14];
lean_object* v_a_470_ = _args[15];
lean_object* v_a_471_ = _args[16];
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(v_f_455_, v_00_u03b1_456_, v_c_457_, v_inst_458_, v_a_459_, v_b_460_, v_fallback_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec(v_a_462_);
lean_dec_ref(v_f_455_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr(lean_object* v_f_473_, lean_object* v_00_u03b1_474_, lean_object* v_c_475_, lean_object* v_inst_476_, lean_object* v_a_477_, lean_object* v_b_478_, lean_object* v_c_x27_479_, lean_object* v_h_480_, lean_object* v_inst_x27_481_, lean_object* v_fallback_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v___x_493_; 
lean_inc(v_a_491_);
lean_inc_ref(v_a_490_);
lean_inc(v_a_489_);
lean_inc_ref(v_a_488_);
lean_inc(v_a_487_);
lean_inc_ref(v_a_486_);
lean_inc(v_a_485_);
lean_inc_ref(v_a_484_);
lean_inc(v_a_483_);
lean_inc_ref(v_inst_x27_481_);
v___x_493_ = lean_sym_simp(v_inst_x27_481_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref_known(v___x_493_, 1);
if (lean_obj_tag(v_a_494_) == 0)
{
uint8_t v_contextDependent_495_; lean_object* v___x_496_; 
v_contextDependent_495_ = lean_ctor_get_uint8(v_a_494_, 1);
lean_dec_ref_known(v_a_494_, 0);
v___x_496_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(v_f_473_, v_00_u03b1_474_, v_c_475_, v_inst_476_, v_a_477_, v_b_478_, v_c_x27_479_, v_h_480_, v_inst_x27_481_, v_fallback_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; uint8_t v___y_499_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
if (v_contextDependent_495_ == 0)
{
lean_dec(v_a_497_);
return v___x_496_;
}
else
{
if (lean_obj_tag(v_a_497_) == 0)
{
uint8_t v_contextDependent_509_; 
v_contextDependent_509_ = lean_ctor_get_uint8(v_a_497_, 1);
v___y_499_ = v_contextDependent_509_;
goto v___jp_498_;
}
else
{
uint8_t v_contextDependent_510_; 
v_contextDependent_510_ = lean_ctor_get_uint8(v_a_497_, sizeof(void*)*2 + 1);
v___y_499_ = v_contextDependent_510_;
goto v___jp_498_;
}
}
v___jp_498_:
{
if (v___y_499_ == 0)
{
lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_507_; 
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_507_ == 0)
{
lean_object* v_unused_508_; 
v_unused_508_ = lean_ctor_get(v___x_496_, 0);
lean_dec(v_unused_508_);
v___x_501_ = v___x_496_;
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
else
{
lean_dec(v___x_496_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_503_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_497_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_503_);
v___x_505_ = v___x_501_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
else
{
lean_dec(v_a_497_);
return v___x_496_;
}
}
}
else
{
return v___x_496_;
}
}
else
{
lean_object* v_e_x27_511_; uint8_t v_contextDependent_512_; lean_object* v___x_513_; 
lean_dec_ref(v_inst_x27_481_);
v_e_x27_511_ = lean_ctor_get(v_a_494_, 0);
lean_inc_ref(v_e_x27_511_);
v_contextDependent_512_ = lean_ctor_get_uint8(v_a_494_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_494_, 2);
v___x_513_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(v_f_473_, v_00_u03b1_474_, v_c_475_, v_inst_476_, v_a_477_, v_b_478_, v_c_x27_479_, v_h_480_, v_e_x27_511_, v_fallback_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; uint8_t v___y_516_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
if (v_contextDependent_512_ == 0)
{
lean_dec(v_a_514_);
return v___x_513_;
}
else
{
if (lean_obj_tag(v_a_514_) == 0)
{
uint8_t v_contextDependent_526_; 
v_contextDependent_526_ = lean_ctor_get_uint8(v_a_514_, 1);
v___y_516_ = v_contextDependent_526_;
goto v___jp_515_;
}
else
{
uint8_t v_contextDependent_527_; 
v_contextDependent_527_ = lean_ctor_get_uint8(v_a_514_, sizeof(void*)*2 + 1);
v___y_516_ = v_contextDependent_527_;
goto v___jp_515_;
}
}
v___jp_515_:
{
if (v___y_516_ == 0)
{
lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_524_; 
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_524_ == 0)
{
lean_object* v_unused_525_; 
v_unused_525_ = lean_ctor_get(v___x_513_, 0);
lean_dec(v_unused_525_);
v___x_518_ = v___x_513_;
v_isShared_519_ = v_isSharedCheck_524_;
goto v_resetjp_517_;
}
else
{
lean_dec(v___x_513_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_524_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_520_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_514_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_520_);
v___x_522_ = v___x_518_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
else
{
lean_dec(v_a_514_);
return v___x_513_;
}
}
}
else
{
return v___x_513_;
}
}
}
else
{
lean_dec_ref(v_fallback_482_);
lean_dec_ref(v_inst_x27_481_);
lean_dec_ref(v_h_480_);
lean_dec_ref(v_c_x27_479_);
lean_dec_ref(v_b_478_);
lean_dec_ref(v_a_477_);
lean_dec_ref(v_inst_476_);
lean_dec_ref(v_c_475_);
lean_dec_ref(v_00_u03b1_474_);
return v___x_493_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___boxed(lean_object** _args){
lean_object* v_f_528_ = _args[0];
lean_object* v_00_u03b1_529_ = _args[1];
lean_object* v_c_530_ = _args[2];
lean_object* v_inst_531_ = _args[3];
lean_object* v_a_532_ = _args[4];
lean_object* v_b_533_ = _args[5];
lean_object* v_c_x27_534_ = _args[6];
lean_object* v_h_535_ = _args[7];
lean_object* v_inst_x27_536_ = _args[8];
lean_object* v_fallback_537_ = _args[9];
lean_object* v_a_538_ = _args[10];
lean_object* v_a_539_ = _args[11];
lean_object* v_a_540_ = _args[12];
lean_object* v_a_541_ = _args[13];
lean_object* v_a_542_ = _args[14];
lean_object* v_a_543_ = _args[15];
lean_object* v_a_544_ = _args[16];
lean_object* v_a_545_ = _args[17];
lean_object* v_a_546_ = _args[18];
lean_object* v_a_547_ = _args[19];
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr(v_f_528_, v_00_u03b1_529_, v_c_530_, v_inst_531_, v_a_532_, v_b_533_, v_c_x27_534_, v_h_535_, v_inst_x27_536_, v_fallback_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
lean_dec(v_a_538_);
lean_dec_ref(v_f_528_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0(lean_object* v___x_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_549_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed(lean_object* v___x_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0(v___x_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(lean_object* v_f_573_, lean_object* v_a_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___y_583_; lean_object* v___x_586_; uint8_t v_debug_587_; 
v___x_586_ = lean_st_ref_get(v___y_576_);
v_debug_587_ = lean_ctor_get_uint8(v___x_586_, sizeof(void*)*11);
lean_dec(v___x_586_);
if (v_debug_587_ == 0)
{
v___y_583_ = v___y_576_;
goto v___jp_582_;
}
else
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_573_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v___x_589_; 
lean_dec_ref_known(v___x_588_, 1);
v___x_589_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_dec_ref_known(v___x_589_, 1);
v___y_583_ = v___y_576_;
goto v___jp_582_;
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_dec_ref(v_a_574_);
lean_dec_ref(v_f_573_);
v_a_590_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_589_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_589_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec_ref(v_a_574_);
lean_dec_ref(v_f_573_);
v_a_598_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_588_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_588_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
v___jp_582_:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = l_Lean_Expr_app___override(v_f_573_, v_a_574_);
v___x_585_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_584_, v___y_583_);
return v___x_585_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg___boxed(lean_object* v_f_606_, lean_object* v_a_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(v_f_606_, v_a_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1(lean_object* v_f_616_, lean_object* v_a_u2081_617_, lean_object* v_a_u2082_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(v_f_616_, v_a_u2081_617_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_631_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_a_630_);
lean_dec_ref_known(v___x_629_, 1);
v___x_631_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(v_a_630_, v_a_u2082_618_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
return v___x_631_;
}
else
{
lean_dec_ref(v_a_u2082_618_);
return v___x_629_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___boxed(lean_object* v_f_632_, lean_object* v_a_u2081_633_, lean_object* v_a_u2082_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1(v_f_632_, v_a_u2081_633_, v_a_u2082_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(lean_object* v_f_646_, lean_object* v_a_u2081_647_, lean_object* v_a_u2082_648_, lean_object* v_a_u2083_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1(v_f_646_, v_a_u2081_647_, v_a_u2082_648_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v___x_662_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_a_661_);
lean_dec_ref_known(v___x_660_, 1);
v___x_662_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(v_a_661_, v_a_u2083_649_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
return v___x_662_;
}
else
{
lean_dec_ref(v_a_u2083_649_);
return v___x_660_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___boxed(lean_object* v_f_663_, lean_object* v_a_u2081_664_, lean_object* v_a_u2082_665_, lean_object* v_a_u2083_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(v_f_663_, v_a_u2081_664_, v_a_u2082_665_, v_a_u2083_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(lean_object* v_f_678_, lean_object* v_a_u2081_679_, lean_object* v_a_u2082_680_, lean_object* v_a_u2083_681_, lean_object* v_a_u2084_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(v_f_678_, v_a_u2081_679_, v_a_u2082_680_, v_a_u2083_681_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_695_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_a_694_);
lean_dec_ref_known(v___x_693_, 1);
v___x_695_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(v_a_694_, v_a_u2084_682_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
return v___x_695_;
}
else
{
lean_dec_ref(v_a_u2084_682_);
return v___x_693_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0___boxed(lean_object* v_f_696_, lean_object* v_a_u2081_697_, lean_object* v_a_u2082_698_, lean_object* v_a_u2083_699_, lean_object* v_a_u2084_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(v_f_696_, v_a_u2081_697_, v_a_u2082_698_, v_a_u2083_699_, v_a_u2084_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1(lean_object* v___x_717_, lean_object* v_e_x27_718_, lean_object* v___x_719_, lean_object* v_arg_720_, lean_object* v_arg_721_, lean_object* v_e_722_, lean_object* v_proof_723_, uint8_t v___x_724_, uint8_t v_contextDependent_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v___x_736_; 
lean_inc_ref(v___x_719_);
lean_inc_ref(v_e_x27_718_);
v___x_736_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(v___x_717_, v_e_x27_718_, v___x_719_, v_arg_720_, v_arg_721_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_748_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_748_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_748_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_748_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_741_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__1));
v___x_742_ = l_Lean_Expr_replaceFn(v_e_722_, v___x_741_);
v___x_743_ = l_Lean_mkApp3(v___x_742_, v_e_x27_718_, v___x_719_, v_proof_723_);
v___x_744_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_744_, 0, v_a_737_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
lean_ctor_set_uint8(v___x_744_, sizeof(void*)*2, v___x_724_);
lean_ctor_set_uint8(v___x_744_, sizeof(void*)*2 + 1, v_contextDependent_725_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_744_);
v___x_746_ = v___x_739_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec_ref(v_proof_723_);
lean_dec_ref(v_e_722_);
lean_dec_ref(v___x_719_);
lean_dec_ref(v_e_x27_718_);
v_a_749_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_736_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_736_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___boxed(lean_object** _args){
lean_object* v___x_757_ = _args[0];
lean_object* v_e_x27_758_ = _args[1];
lean_object* v___x_759_ = _args[2];
lean_object* v_arg_760_ = _args[3];
lean_object* v_arg_761_ = _args[4];
lean_object* v_e_762_ = _args[5];
lean_object* v_proof_763_ = _args[6];
lean_object* v___x_764_ = _args[7];
lean_object* v_contextDependent_765_ = _args[8];
lean_object* v___y_766_ = _args[9];
lean_object* v___y_767_ = _args[10];
lean_object* v___y_768_ = _args[11];
lean_object* v___y_769_ = _args[12];
lean_object* v___y_770_ = _args[13];
lean_object* v___y_771_ = _args[14];
lean_object* v___y_772_ = _args[15];
lean_object* v___y_773_ = _args[16];
lean_object* v___y_774_ = _args[17];
lean_object* v___y_775_ = _args[18];
_start:
{
uint8_t v___x_18465__boxed_776_; uint8_t v_contextDependent_18466__boxed_777_; lean_object* v_res_778_; 
v___x_18465__boxed_776_ = lean_unbox(v___x_764_);
v_contextDependent_18466__boxed_777_ = lean_unbox(v_contextDependent_765_);
v_res_778_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1(v___x_757_, v_e_x27_758_, v___x_759_, v_arg_760_, v_arg_761_, v_e_762_, v_proof_763_, v___x_18465__boxed_776_, v_contextDependent_18466__boxed_777_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
return v_res_778_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_789_ = lean_box(0);
v___x_790_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__5));
v___x_791_ = l_Lean_mkConst(v___x_790_, v___x_789_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2(uint8_t v___x_798_, lean_object* v_e_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v___x_813_; uint8_t v___x_814_; 
lean_inc_ref(v_e_799_);
v___x_813_ = l_Lean_Expr_cleanupAnnotations(v_e_799_);
v___x_814_ = l_Lean_Expr_isApp(v___x_813_);
if (v___x_814_ == 0)
{
lean_dec_ref(v___x_813_);
lean_dec_ref(v_e_799_);
goto v___jp_810_;
}
else
{
lean_object* v_arg_815_; lean_object* v___x_816_; uint8_t v___x_817_; 
v_arg_815_ = lean_ctor_get(v___x_813_, 1);
lean_inc_ref(v_arg_815_);
v___x_816_ = l_Lean_Expr_appFnCleanup___redArg(v___x_813_);
v___x_817_ = l_Lean_Expr_isApp(v___x_816_);
if (v___x_817_ == 0)
{
lean_dec_ref(v___x_816_);
lean_dec_ref(v_arg_815_);
lean_dec_ref(v_e_799_);
goto v___jp_810_;
}
else
{
lean_object* v_arg_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v_arg_818_ = lean_ctor_get(v___x_816_, 1);
lean_inc_ref(v_arg_818_);
v___x_819_ = l_Lean_Expr_appFnCleanup___redArg(v___x_816_);
v___x_820_ = l_Lean_Expr_isApp(v___x_819_);
if (v___x_820_ == 0)
{
lean_dec_ref(v___x_819_);
lean_dec_ref(v_arg_818_);
lean_dec_ref(v_arg_815_);
lean_dec_ref(v_e_799_);
goto v___jp_810_;
}
else
{
lean_object* v_arg_821_; lean_object* v___x_822_; uint8_t v___x_823_; 
v_arg_821_ = lean_ctor_get(v___x_819_, 1);
lean_inc_ref(v_arg_821_);
v___x_822_ = l_Lean_Expr_appFnCleanup___redArg(v___x_819_);
v___x_823_ = l_Lean_Expr_isApp(v___x_822_);
if (v___x_823_ == 0)
{
lean_dec_ref(v___x_822_);
lean_dec_ref(v_arg_821_);
lean_dec_ref(v_arg_818_);
lean_dec_ref(v_arg_815_);
lean_dec_ref(v_e_799_);
goto v___jp_810_;
}
else
{
lean_object* v_arg_824_; lean_object* v___x_825_; uint8_t v___x_826_; 
v_arg_824_ = lean_ctor_get(v___x_822_, 1);
lean_inc_ref(v_arg_824_);
v___x_825_ = l_Lean_Expr_appFnCleanup___redArg(v___x_822_);
v___x_826_ = l_Lean_Expr_isApp(v___x_825_);
if (v___x_826_ == 0)
{
lean_dec_ref(v___x_825_);
lean_dec_ref(v_arg_824_);
lean_dec_ref(v_arg_821_);
lean_dec_ref(v_arg_818_);
lean_dec_ref(v_arg_815_);
lean_dec_ref(v_e_799_);
goto v___jp_810_;
}
else
{
lean_object* v_arg_827_; lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v_arg_827_ = lean_ctor_get(v___x_825_, 1);
lean_inc_ref(v_arg_827_);
v___x_828_ = l_Lean_Expr_appFnCleanup___redArg(v___x_825_);
v___x_829_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__1));
v___x_830_ = l_Lean_Expr_isConstOf(v___x_828_, v___x_829_);
if (v___x_830_ == 0)
{
lean_dec_ref(v___x_828_);
lean_dec_ref(v_arg_827_);
lean_dec_ref(v_arg_824_);
lean_dec_ref(v_arg_821_);
lean_dec_ref(v_arg_818_);
lean_dec_ref(v_arg_815_);
lean_dec_ref(v_e_799_);
goto v___jp_810_;
}
else
{
lean_object* v___x_831_; 
lean_inc(v___y_808_);
lean_inc_ref(v___y_807_);
lean_inc(v___y_806_);
lean_inc_ref(v___y_805_);
lean_inc(v___y_804_);
lean_inc_ref(v___y_803_);
lean_inc(v___y_802_);
lean_inc_ref(v___y_801_);
lean_inc(v___y_800_);
lean_inc_ref(v_arg_824_);
v___x_831_ = lean_sym_simp(v_arg_824_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_832_);
lean_dec_ref_known(v___x_831_, 1);
if (lean_obj_tag(v_a_832_) == 0)
{
uint8_t v_contextDependent_833_; lean_object* v___x_834_; 
lean_dec_ref(v_e_799_);
v_contextDependent_833_ = lean_ctor_get_uint8(v_a_832_, 1);
lean_dec_ref_known(v_a_832_, 0);
v___x_834_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_824_, v___y_803_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_875_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_875_ == 0)
{
v___x_837_ = v___x_834_;
v_isShared_838_ = v_isSharedCheck_875_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_834_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_875_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
uint8_t v___x_839_; 
v___x_839_ = lean_unbox(v_a_835_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; 
lean_del_object(v___x_837_);
v___x_840_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_824_, v___y_803_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_858_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_858_ == 0)
{
v___x_843_ = v___x_840_;
v_isShared_844_ = v_isSharedCheck_858_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_840_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_858_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
uint8_t v___x_845_; 
v___x_845_ = lean_unbox(v_a_841_);
lean_dec(v_a_841_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; lean_object* v___f_847_; lean_object* v___x_848_; 
lean_del_object(v___x_843_);
lean_dec(v_a_835_);
v___x_846_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_830_, v_contextDependent_833_);
v___f_847_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_847_, 0, v___x_846_);
v___x_848_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(v___x_828_, v_arg_827_, v_arg_824_, v_arg_821_, v_arg_818_, v_arg_815_, v___f_847_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec_ref(v___x_828_);
return v___x_848_;
}
else
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; uint8_t v___x_854_; lean_object* v___x_856_; 
lean_dec_ref(v_arg_824_);
lean_dec_ref(v_arg_821_);
v___x_849_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__2));
v___x_850_ = l_Lean_Expr_constLevels_x21(v___x_828_);
lean_dec_ref(v___x_828_);
v___x_851_ = l_Lean_mkConst(v___x_849_, v___x_850_);
lean_inc_ref(v_arg_815_);
v___x_852_ = l_Lean_mkApp3(v___x_851_, v_arg_827_, v_arg_818_, v_arg_815_);
v___x_853_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_853_, 0, v_arg_815_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = lean_unbox(v_a_835_);
lean_dec(v_a_835_);
lean_ctor_set_uint8(v___x_853_, sizeof(void*)*2, v___x_854_);
lean_ctor_set_uint8(v___x_853_, sizeof(void*)*2 + 1, v_contextDependent_833_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v___x_853_);
v___x_856_ = v___x_843_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_853_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
else
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
lean_dec(v_a_835_);
lean_dec_ref(v___x_828_);
lean_dec_ref(v_arg_827_);
lean_dec_ref(v_arg_824_);
lean_dec_ref(v_arg_821_);
lean_dec_ref(v_arg_818_);
lean_dec_ref(v_arg_815_);
v_a_859_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_866_ == 0)
{
v___x_861_ = v___x_840_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_840_);
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
else
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_873_; 
lean_dec(v_a_835_);
lean_dec_ref(v_arg_824_);
lean_dec_ref(v_arg_821_);
v___x_867_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__3));
v___x_868_ = l_Lean_Expr_constLevels_x21(v___x_828_);
lean_dec_ref(v___x_828_);
v___x_869_ = l_Lean_mkConst(v___x_867_, v___x_868_);
lean_inc_ref(v_arg_818_);
v___x_870_ = l_Lean_mkApp3(v___x_869_, v_arg_827_, v_arg_818_, v_arg_815_);
v___x_871_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_871_, 0, v_arg_818_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
lean_ctor_set_uint8(v___x_871_, sizeof(void*)*2, v___x_798_);
lean_ctor_set_uint8(v___x_871_, sizeof(void*)*2 + 1, v_contextDependent_833_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v___x_871_);
v___x_873_ = v___x_837_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_871_);
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
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec_ref(v___x_828_);
lean_dec_ref(v_arg_827_);
lean_dec_ref(v_arg_824_);
lean_dec_ref(v_arg_821_);
lean_dec_ref(v_arg_818_);
lean_dec_ref(v_arg_815_);
v_a_876_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_834_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_834_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
else
{
lean_object* v_e_x27_884_; lean_object* v_proof_885_; uint8_t v_contextDependent_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_948_; 
v_e_x27_884_ = lean_ctor_get(v_a_832_, 0);
v_proof_885_ = lean_ctor_get(v_a_832_, 1);
v_contextDependent_886_ = lean_ctor_get_uint8(v_a_832_, sizeof(void*)*2 + 1);
v_isSharedCheck_948_ = !lean_is_exclusive(v_a_832_);
if (v_isSharedCheck_948_ == 0)
{
v___x_888_ = v_a_832_;
v_isShared_889_ = v_isSharedCheck_948_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_proof_885_);
lean_inc(v_e_x27_884_);
lean_dec(v_a_832_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_948_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_884_, v___y_803_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_939_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_939_ == 0)
{
v___x_893_ = v___x_890_;
v_isShared_894_ = v_isSharedCheck_939_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_890_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_939_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
uint8_t v___x_895_; 
v___x_895_ = lean_unbox(v_a_891_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; 
lean_del_object(v___x_893_);
v___x_896_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_884_, v___y_803_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_921_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_921_ == 0)
{
v___x_899_ = v___x_896_;
v_isShared_900_ = v_isSharedCheck_921_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_896_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_921_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
uint8_t v___x_901_; 
v___x_901_ = lean_unbox(v_a_897_);
lean_dec(v_a_897_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___f_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
lean_del_object(v___x_899_);
lean_dec(v_a_891_);
lean_del_object(v___x_888_);
v___x_902_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6);
lean_inc_ref_n(v_proof_885_, 2);
lean_inc_ref_n(v_arg_821_, 2);
lean_inc_ref_n(v_e_x27_884_, 2);
lean_inc_ref_n(v_arg_824_, 2);
v___x_903_ = l_Lean_mkApp4(v___x_902_, v_arg_824_, v_e_x27_884_, v_arg_821_, v_proof_885_);
v___x_904_ = lean_unsigned_to_nat(4u);
v___x_905_ = l_Lean_Expr_getBoundedAppFn(v___x_904_, v_e_799_);
v___x_906_ = lean_box(v___x_830_);
v___x_907_ = lean_box(v_contextDependent_886_);
lean_inc_ref_n(v_arg_815_, 2);
lean_inc_ref_n(v_arg_818_, 2);
lean_inc_ref(v___x_903_);
v___f_908_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___boxed), 19, 9);
lean_closure_set(v___f_908_, 0, v___x_905_);
lean_closure_set(v___f_908_, 1, v_e_x27_884_);
lean_closure_set(v___f_908_, 2, v___x_903_);
lean_closure_set(v___f_908_, 3, v_arg_818_);
lean_closure_set(v___f_908_, 4, v_arg_815_);
lean_closure_set(v___f_908_, 5, v_e_799_);
lean_closure_set(v___f_908_, 6, v_proof_885_);
lean_closure_set(v___f_908_, 7, v___x_906_);
lean_closure_set(v___f_908_, 8, v___x_907_);
lean_inc_ref(v_arg_827_);
lean_inc_ref(v___x_828_);
v___x_909_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___boxed), 20, 10);
lean_closure_set(v___x_909_, 0, v___x_828_);
lean_closure_set(v___x_909_, 1, v_arg_827_);
lean_closure_set(v___x_909_, 2, v_arg_824_);
lean_closure_set(v___x_909_, 3, v_arg_821_);
lean_closure_set(v___x_909_, 4, v_arg_818_);
lean_closure_set(v___x_909_, 5, v_arg_815_);
lean_closure_set(v___x_909_, 6, v_e_x27_884_);
lean_closure_set(v___x_909_, 7, v_proof_885_);
lean_closure_set(v___x_909_, 8, v___x_903_);
lean_closure_set(v___x_909_, 9, v___f_908_);
v___x_910_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(v___x_828_, v_arg_827_, v_arg_824_, v_arg_821_, v_arg_818_, v_arg_815_, v___x_909_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec_ref(v___x_828_);
return v___x_910_;
}
else
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_915_; 
lean_dec_ref(v_e_x27_884_);
lean_dec_ref(v___x_828_);
lean_dec_ref(v_arg_827_);
lean_dec_ref(v_arg_824_);
lean_dec_ref(v_arg_821_);
lean_dec_ref(v_arg_818_);
v___x_911_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__8));
v___x_912_ = l_Lean_Expr_replaceFn(v_e_799_, v___x_911_);
v___x_913_ = l_Lean_Expr_app___override(v___x_912_, v_proof_885_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 1, v___x_913_);
lean_ctor_set(v___x_888_, 0, v_arg_815_);
v___x_915_ = v___x_888_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_arg_815_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v___x_913_);
v___x_915_ = v_reuseFailAlloc_920_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
uint8_t v___x_916_; lean_object* v___x_918_; 
v___x_916_ = lean_unbox(v_a_891_);
lean_dec(v_a_891_);
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*2, v___x_916_);
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*2 + 1, v_contextDependent_886_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_915_);
v___x_918_ = v___x_899_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_915_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec(v_a_891_);
lean_del_object(v___x_888_);
lean_dec_ref(v_proof_885_);
lean_dec_ref(v_e_x27_884_);
lean_dec_ref(v___x_828_);
lean_dec_ref(v_arg_827_);
lean_dec_ref(v_arg_824_);
lean_dec_ref(v_arg_821_);
lean_dec_ref(v_arg_818_);
lean_dec_ref(v_arg_815_);
lean_dec_ref(v_e_799_);
v_a_922_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_896_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_896_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_934_; 
lean_dec(v_a_891_);
lean_dec_ref(v_e_x27_884_);
lean_dec_ref(v___x_828_);
lean_dec_ref(v_arg_827_);
lean_dec_ref(v_arg_824_);
lean_dec_ref(v_arg_821_);
lean_dec_ref(v_arg_815_);
v___x_930_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__10));
v___x_931_ = l_Lean_Expr_replaceFn(v_e_799_, v___x_930_);
v___x_932_ = l_Lean_Expr_app___override(v___x_931_, v_proof_885_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 1, v___x_932_);
lean_ctor_set(v___x_888_, 0, v_arg_818_);
v___x_934_ = v___x_888_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_arg_818_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v___x_932_);
lean_ctor_set_uint8(v_reuseFailAlloc_938_, sizeof(void*)*2 + 1, v_contextDependent_886_);
v___x_934_ = v_reuseFailAlloc_938_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_936_; 
lean_ctor_set_uint8(v___x_934_, sizeof(void*)*2, v___x_798_);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v___x_934_);
v___x_936_ = v___x_893_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_934_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_del_object(v___x_888_);
lean_dec_ref(v_proof_885_);
lean_dec_ref(v_e_x27_884_);
lean_dec_ref(v___x_828_);
lean_dec_ref(v_arg_827_);
lean_dec_ref(v_arg_824_);
lean_dec_ref(v_arg_821_);
lean_dec_ref(v_arg_818_);
lean_dec_ref(v_arg_815_);
lean_dec_ref(v_e_799_);
v_a_940_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_890_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_890_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_828_);
lean_dec_ref(v_arg_827_);
lean_dec_ref(v_arg_824_);
lean_dec_ref(v_arg_821_);
lean_dec_ref(v_arg_818_);
lean_dec_ref(v_arg_815_);
lean_dec_ref(v_e_799_);
return v___x_831_;
}
}
}
}
}
}
}
v___jp_810_:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_811_, 0, v___x_798_);
lean_ctor_set_uint8(v___x_811_, 1, v___x_798_);
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
return v___x_812_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___boxed(lean_object* v___x_949_, lean_object* v_e_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
uint8_t v___x_18600__boxed_961_; lean_object* v_res_962_; 
v___x_18600__boxed_961_ = lean_unbox(v___x_949_);
v_res_962_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2(v___x_18600__boxed_961_, v_e_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv(lean_object* v_e_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_){
_start:
{
lean_object* v_numArgs_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v_numArgs_974_ = l_Lean_Expr_getAppNumArgs(v_e_963_);
v___x_975_ = lean_unsigned_to_nat(5u);
v___x_976_ = lean_nat_dec_lt(v_numArgs_974_, v___x_975_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; lean_object* v___f_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_977_ = lean_box(v___x_976_);
v___f_978_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___boxed), 12, 1);
lean_closure_set(v___f_978_, 0, v___x_977_);
v___x_979_ = lean_nat_sub(v_numArgs_974_, v___x_975_);
lean_dec(v_numArgs_974_);
v___x_980_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_963_, v___x_979_, v___f_978_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
lean_dec(v___x_979_);
return v___x_980_;
}
else
{
uint8_t v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
lean_dec(v_numArgs_974_);
lean_dec_ref(v_e_963_);
v___x_981_ = 0;
v___x_982_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_982_, 0, v___x_976_);
lean_ctor_set_uint8(v___x_982_, 1, v___x_981_);
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
return v___x_983_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___boxed(lean_object* v_e_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv(v_e_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_);
lean_dec(v_a_993_);
lean_dec_ref(v_a_992_);
lean_dec(v_a_991_);
lean_dec_ref(v_a_990_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
lean_dec(v_a_985_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1(lean_object* v_f_996_, lean_object* v_a_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(v_f_996_, v_a_997_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___boxed(lean_object* v_f_1009_, lean_object* v_a_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1(v_f_1009_, v_a_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1079_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_));
v___x_1080_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__20_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_));
v___x_1081_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___boxed), 11, 0);
v___x_1082_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_1079_, v___x_1080_, v___x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17____boxed(lean_object* v_a_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_();
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1086_; uint8_t v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1086_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_));
v___x_1087_ = 0;
v___x_1088_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___boxed), 11, 0);
v___x_1089_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_1086_, v___x_1087_, v___x_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_19____boxed(lean_object* v_a_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_19_();
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(lean_object* v_f_1102_, lean_object* v_00_u03b1_1103_, lean_object* v_c_1104_, lean_object* v_inst_1105_, lean_object* v_a_1106_, lean_object* v_b_1107_, lean_object* v_instToMatch_1108_, lean_object* v_fallback_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_instToMatch_1108_, v_a_1116_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_a_1121_);
lean_dec_ref_known(v___x_1120_, 1);
v___x_1122_ = l_Lean_Expr_cleanupAnnotations(v_a_1121_);
v___x_1123_ = l_Lean_Expr_isApp(v___x_1122_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; 
lean_dec_ref(v___x_1122_);
lean_dec_ref(v_b_1107_);
lean_dec_ref(v_a_1106_);
lean_dec_ref(v_inst_1105_);
lean_dec_ref(v_c_1104_);
lean_dec_ref(v_00_u03b1_1103_);
lean_inc(v_a_1118_);
lean_inc_ref(v_a_1117_);
lean_inc(v_a_1116_);
lean_inc_ref(v_a_1115_);
lean_inc(v_a_1114_);
lean_inc_ref(v_a_1113_);
lean_inc(v_a_1112_);
lean_inc_ref(v_a_1111_);
lean_inc(v_a_1110_);
v___x_1124_ = lean_apply_10(v_fallback_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, lean_box(0));
return v___x_1124_;
}
else
{
lean_object* v_arg_1125_; lean_object* v___x_1126_; uint8_t v___x_1127_; 
v_arg_1125_ = lean_ctor_get(v___x_1122_, 1);
lean_inc_ref(v_arg_1125_);
v___x_1126_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1122_);
v___x_1127_ = l_Lean_Expr_isApp(v___x_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; 
lean_dec_ref(v___x_1126_);
lean_dec_ref(v_arg_1125_);
lean_dec_ref(v_b_1107_);
lean_dec_ref(v_a_1106_);
lean_dec_ref(v_inst_1105_);
lean_dec_ref(v_c_1104_);
lean_dec_ref(v_00_u03b1_1103_);
lean_inc(v_a_1118_);
lean_inc_ref(v_a_1117_);
lean_inc(v_a_1116_);
lean_inc_ref(v_a_1115_);
lean_inc(v_a_1114_);
lean_inc_ref(v_a_1113_);
lean_inc(v_a_1112_);
lean_inc_ref(v_a_1111_);
lean_inc(v_a_1110_);
v___x_1128_ = lean_apply_10(v_fallback_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, lean_box(0));
return v___x_1128_;
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1129_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1126_);
v___x_1130_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_1131_ = l_Lean_Expr_isConstOf(v___x_1129_, v___x_1130_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1132_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3));
v___x_1133_ = l_Lean_Expr_isConstOf(v___x_1129_, v___x_1132_);
lean_dec_ref(v___x_1129_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
lean_dec_ref(v_arg_1125_);
lean_dec_ref(v_b_1107_);
lean_dec_ref(v_a_1106_);
lean_dec_ref(v_inst_1105_);
lean_dec_ref(v_c_1104_);
lean_dec_ref(v_00_u03b1_1103_);
lean_inc(v_a_1118_);
lean_inc_ref(v_a_1117_);
lean_inc(v_a_1116_);
lean_inc_ref(v_a_1115_);
lean_inc(v_a_1114_);
lean_inc_ref(v_a_1113_);
lean_inc(v_a_1112_);
lean_inc_ref(v_a_1111_);
lean_inc(v_a_1110_);
v___x_1134_ = lean_apply_10(v_fallback_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, lean_box(0));
return v___x_1134_;
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_dec_ref(v_fallback_1109_);
v___x_1135_ = lean_unsigned_to_nat(1u);
v___x_1136_ = lean_mk_empty_array_with_capacity(v___x_1135_);
lean_inc_ref(v_arg_1125_);
v___x_1137_ = lean_array_push(v___x_1136_, v_arg_1125_);
lean_inc_ref(v_a_1106_);
v___x_1138_ = l_Lean_Expr_betaRev(v_a_1106_, v___x_1137_, v___x_1131_, v___x_1131_);
lean_dec_ref(v___x_1137_);
v___x_1139_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1138_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1152_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1142_ = v___x_1139_;
v_isShared_1143_ = v_isSharedCheck_1152_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1139_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1152_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1144_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1));
v___x_1145_ = l_Lean_Expr_constLevels_x21(v_f_1102_);
v___x_1146_ = l_Lean_mkConst(v___x_1144_, v___x_1145_);
v___x_1147_ = l_Lean_mkApp6(v___x_1146_, v_00_u03b1_1103_, v_c_1104_, v_inst_1105_, v_a_1106_, v_b_1107_, v_arg_1125_);
v___x_1148_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1148_, 0, v_a_1140_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
lean_ctor_set_uint8(v___x_1148_, sizeof(void*)*2, v___x_1131_);
lean_ctor_set_uint8(v___x_1148_, sizeof(void*)*2 + 1, v___x_1131_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1148_);
v___x_1150_ = v___x_1142_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec_ref(v_arg_1125_);
lean_dec_ref(v_b_1107_);
lean_dec_ref(v_a_1106_);
lean_dec_ref(v_inst_1105_);
lean_dec_ref(v_c_1104_);
lean_dec_ref(v_00_u03b1_1103_);
v_a_1153_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1139_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1139_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_dec_ref(v___x_1129_);
lean_dec_ref(v_fallback_1109_);
v___x_1161_ = lean_unsigned_to_nat(1u);
v___x_1162_ = lean_mk_empty_array_with_capacity(v___x_1161_);
lean_inc_ref(v_arg_1125_);
v___x_1163_ = lean_array_push(v___x_1162_, v_arg_1125_);
v___x_1164_ = 0;
lean_inc_ref(v_b_1107_);
v___x_1165_ = l_Lean_Expr_betaRev(v_b_1107_, v___x_1163_, v___x_1164_, v___x_1164_);
lean_dec_ref(v___x_1163_);
v___x_1166_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1165_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1179_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1169_ = v___x_1166_;
v_isShared_1170_ = v_isSharedCheck_1179_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1166_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1179_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3));
v___x_1172_ = l_Lean_Expr_constLevels_x21(v_f_1102_);
v___x_1173_ = l_Lean_mkConst(v___x_1171_, v___x_1172_);
v___x_1174_ = l_Lean_mkApp6(v___x_1173_, v_00_u03b1_1103_, v_c_1104_, v_inst_1105_, v_a_1106_, v_b_1107_, v_arg_1125_);
v___x_1175_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1175_, 0, v_a_1167_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
lean_ctor_set_uint8(v___x_1175_, sizeof(void*)*2, v___x_1164_);
lean_ctor_set_uint8(v___x_1175_, sizeof(void*)*2 + 1, v___x_1164_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 0, v___x_1175_);
v___x_1177_ = v___x_1169_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec_ref(v_arg_1125_);
lean_dec_ref(v_b_1107_);
lean_dec_ref(v_a_1106_);
lean_dec_ref(v_inst_1105_);
lean_dec_ref(v_c_1104_);
lean_dec_ref(v_00_u03b1_1103_);
v_a_1180_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1166_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1166_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
lean_dec_ref(v_fallback_1109_);
lean_dec_ref(v_b_1107_);
lean_dec_ref(v_a_1106_);
lean_dec_ref(v_inst_1105_);
lean_dec_ref(v_c_1104_);
lean_dec_ref(v_00_u03b1_1103_);
v_a_1188_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1120_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1120_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___boxed(lean_object** _args){
lean_object* v_f_1196_ = _args[0];
lean_object* v_00_u03b1_1197_ = _args[1];
lean_object* v_c_1198_ = _args[2];
lean_object* v_inst_1199_ = _args[3];
lean_object* v_a_1200_ = _args[4];
lean_object* v_b_1201_ = _args[5];
lean_object* v_instToMatch_1202_ = _args[6];
lean_object* v_fallback_1203_ = _args[7];
lean_object* v_a_1204_ = _args[8];
lean_object* v_a_1205_ = _args[9];
lean_object* v_a_1206_ = _args[10];
lean_object* v_a_1207_ = _args[11];
lean_object* v_a_1208_ = _args[12];
lean_object* v_a_1209_ = _args[13];
lean_object* v_a_1210_ = _args[14];
lean_object* v_a_1211_ = _args[15];
lean_object* v_a_1212_ = _args[16];
lean_object* v_a_1213_ = _args[17];
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(v_f_1196_, v_00_u03b1_1197_, v_c_1198_, v_inst_1199_, v_a_1200_, v_b_1201_, v_instToMatch_1202_, v_fallback_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
lean_dec(v_a_1212_);
lean_dec_ref(v_a_1211_);
lean_dec(v_a_1210_);
lean_dec_ref(v_a_1209_);
lean_dec(v_a_1208_);
lean_dec_ref(v_a_1207_);
lean_dec(v_a_1206_);
lean_dec_ref(v_a_1205_);
lean_dec(v_a_1204_);
lean_dec_ref(v_f_1196_);
return v_res_1214_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__3(void){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1220_ = lean_box(0);
v___x_1221_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2));
v___x_1222_ = l_Lean_mkConst(v___x_1221_, v___x_1220_);
return v___x_1222_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__8(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1232_ = lean_box(0);
v___x_1233_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7));
v___x_1234_ = l_Lean_mkConst(v___x_1233_, v___x_1232_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(lean_object* v_f_1240_, lean_object* v_00_u03b1_1241_, lean_object* v_c_1242_, lean_object* v_inst_1243_, lean_object* v_a_1244_, lean_object* v_b_1245_, lean_object* v_c_x27_1246_, lean_object* v_h_1247_, lean_object* v_inst_x27_1248_, lean_object* v_fallback_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_inst_x27_1248_, v_a_1256_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref_known(v___x_1260_, 1);
v___x_1262_ = l_Lean_Expr_cleanupAnnotations(v_a_1261_);
v___x_1263_ = l_Lean_Expr_isApp(v___x_1262_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; 
lean_dec_ref(v___x_1262_);
lean_dec_ref(v_h_1247_);
lean_dec_ref(v_c_x27_1246_);
lean_dec_ref(v_b_1245_);
lean_dec_ref(v_a_1244_);
lean_dec_ref(v_inst_1243_);
lean_dec_ref(v_c_1242_);
lean_dec_ref(v_00_u03b1_1241_);
lean_inc(v_a_1258_);
lean_inc_ref(v_a_1257_);
lean_inc(v_a_1256_);
lean_inc_ref(v_a_1255_);
lean_inc(v_a_1254_);
lean_inc_ref(v_a_1253_);
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
lean_inc(v_a_1250_);
v___x_1264_ = lean_apply_10(v_fallback_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, lean_box(0));
return v___x_1264_;
}
else
{
lean_object* v_arg_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v_arg_1265_ = lean_ctor_get(v___x_1262_, 1);
lean_inc_ref(v_arg_1265_);
v___x_1266_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1262_);
v___x_1267_ = l_Lean_Expr_isApp(v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; 
lean_dec_ref(v___x_1266_);
lean_dec_ref(v_arg_1265_);
lean_dec_ref(v_h_1247_);
lean_dec_ref(v_c_x27_1246_);
lean_dec_ref(v_b_1245_);
lean_dec_ref(v_a_1244_);
lean_dec_ref(v_inst_1243_);
lean_dec_ref(v_c_1242_);
lean_dec_ref(v_00_u03b1_1241_);
lean_inc(v_a_1258_);
lean_inc_ref(v_a_1257_);
lean_inc(v_a_1256_);
lean_inc_ref(v_a_1255_);
lean_inc(v_a_1254_);
lean_inc_ref(v_a_1253_);
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
lean_inc(v_a_1250_);
v___x_1268_ = lean_apply_10(v_fallback_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, lean_box(0));
return v___x_1268_;
}
else
{
lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1269_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1266_);
v___x_1270_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_1271_ = l_Lean_Expr_isConstOf(v___x_1269_, v___x_1270_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1272_; uint8_t v___x_1273_; 
v___x_1272_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3));
v___x_1273_ = l_Lean_Expr_isConstOf(v___x_1269_, v___x_1272_);
lean_dec_ref(v___x_1269_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; 
lean_dec_ref(v_arg_1265_);
lean_dec_ref(v_h_1247_);
lean_dec_ref(v_c_x27_1246_);
lean_dec_ref(v_b_1245_);
lean_dec_ref(v_a_1244_);
lean_dec_ref(v_inst_1243_);
lean_dec_ref(v_c_1242_);
lean_dec_ref(v_00_u03b1_1241_);
lean_inc(v_a_1258_);
lean_inc_ref(v_a_1257_);
lean_inc(v_a_1256_);
lean_inc_ref(v_a_1255_);
lean_inc(v_a_1254_);
lean_inc_ref(v_a_1253_);
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
lean_inc(v_a_1250_);
v___x_1274_ = lean_apply_10(v_fallback_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, lean_box(0));
return v___x_1274_;
}
else
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
lean_dec_ref(v_fallback_1249_);
v___x_1275_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__3, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__3);
lean_inc_ref(v_arg_1265_);
lean_inc_ref(v_h_1247_);
lean_inc_ref(v_c_x27_1246_);
lean_inc_ref(v_c_1242_);
v___x_1276_ = l_Lean_mkApp4(v___x_1275_, v_c_1242_, v_c_x27_1246_, v_h_1247_, v_arg_1265_);
v___x_1277_ = lean_unsigned_to_nat(1u);
v___x_1278_ = lean_mk_empty_array_with_capacity(v___x_1277_);
v___x_1279_ = lean_array_push(v___x_1278_, v___x_1276_);
lean_inc_ref(v_a_1244_);
v___x_1280_ = l_Lean_Expr_betaRev(v_a_1244_, v___x_1279_, v___x_1271_, v___x_1271_);
lean_dec_ref(v___x_1279_);
v___x_1281_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1280_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1294_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1284_ = v___x_1281_;
v_isShared_1285_ = v_isSharedCheck_1294_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1281_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1294_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1292_; 
v___x_1286_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__5));
v___x_1287_ = l_Lean_Expr_constLevels_x21(v_f_1240_);
v___x_1288_ = l_Lean_mkConst(v___x_1286_, v___x_1287_);
v___x_1289_ = l_Lean_mkApp8(v___x_1288_, v_00_u03b1_1241_, v_c_1242_, v_inst_1243_, v_a_1244_, v_b_1245_, v_c_x27_1246_, v_h_1247_, v_arg_1265_);
v___x_1290_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1290_, 0, v_a_1282_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*2, v___x_1271_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*2 + 1, v___x_1271_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v___x_1290_);
v___x_1292_ = v___x_1284_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1290_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec_ref(v_arg_1265_);
lean_dec_ref(v_h_1247_);
lean_dec_ref(v_c_x27_1246_);
lean_dec_ref(v_b_1245_);
lean_dec_ref(v_a_1244_);
lean_dec_ref(v_inst_1243_);
lean_dec_ref(v_c_1242_);
lean_dec_ref(v_00_u03b1_1241_);
v_a_1295_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1281_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1281_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
else
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_dec_ref(v___x_1269_);
lean_dec_ref(v_fallback_1249_);
v___x_1303_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__8);
lean_inc_ref(v_arg_1265_);
lean_inc_ref(v_h_1247_);
lean_inc_ref(v_c_x27_1246_);
lean_inc_ref(v_c_1242_);
v___x_1304_ = l_Lean_mkApp4(v___x_1303_, v_c_1242_, v_c_x27_1246_, v_h_1247_, v_arg_1265_);
v___x_1305_ = lean_unsigned_to_nat(1u);
v___x_1306_ = lean_mk_empty_array_with_capacity(v___x_1305_);
v___x_1307_ = lean_array_push(v___x_1306_, v___x_1304_);
v___x_1308_ = 0;
lean_inc_ref(v_b_1245_);
v___x_1309_ = l_Lean_Expr_betaRev(v_b_1245_, v___x_1307_, v___x_1308_, v___x_1308_);
lean_dec_ref(v___x_1307_);
v___x_1310_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1309_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1323_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1313_ = v___x_1310_;
v_isShared_1314_ = v_isSharedCheck_1323_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1323_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__10));
v___x_1316_ = l_Lean_Expr_constLevels_x21(v_f_1240_);
v___x_1317_ = l_Lean_mkConst(v___x_1315_, v___x_1316_);
v___x_1318_ = l_Lean_mkApp8(v___x_1317_, v_00_u03b1_1241_, v_c_1242_, v_inst_1243_, v_a_1244_, v_b_1245_, v_c_x27_1246_, v_h_1247_, v_arg_1265_);
v___x_1319_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1319_, 0, v_a_1311_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
lean_ctor_set_uint8(v___x_1319_, sizeof(void*)*2, v___x_1308_);
lean_ctor_set_uint8(v___x_1319_, sizeof(void*)*2 + 1, v___x_1308_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1319_);
v___x_1321_ = v___x_1313_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_dec_ref(v_arg_1265_);
lean_dec_ref(v_h_1247_);
lean_dec_ref(v_c_x27_1246_);
lean_dec_ref(v_b_1245_);
lean_dec_ref(v_a_1244_);
lean_dec_ref(v_inst_1243_);
lean_dec_ref(v_c_1242_);
lean_dec_ref(v_00_u03b1_1241_);
v_a_1324_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1310_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1310_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
lean_dec_ref(v_fallback_1249_);
lean_dec_ref(v_h_1247_);
lean_dec_ref(v_c_x27_1246_);
lean_dec_ref(v_b_1245_);
lean_dec_ref(v_a_1244_);
lean_dec_ref(v_inst_1243_);
lean_dec_ref(v_c_1242_);
lean_dec_ref(v_00_u03b1_1241_);
v_a_1332_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1260_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1260_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___boxed(lean_object** _args){
lean_object* v_f_1340_ = _args[0];
lean_object* v_00_u03b1_1341_ = _args[1];
lean_object* v_c_1342_ = _args[2];
lean_object* v_inst_1343_ = _args[3];
lean_object* v_a_1344_ = _args[4];
lean_object* v_b_1345_ = _args[5];
lean_object* v_c_x27_1346_ = _args[6];
lean_object* v_h_1347_ = _args[7];
lean_object* v_inst_x27_1348_ = _args[8];
lean_object* v_fallback_1349_ = _args[9];
lean_object* v_a_1350_ = _args[10];
lean_object* v_a_1351_ = _args[11];
lean_object* v_a_1352_ = _args[12];
lean_object* v_a_1353_ = _args[13];
lean_object* v_a_1354_ = _args[14];
lean_object* v_a_1355_ = _args[15];
lean_object* v_a_1356_ = _args[16];
lean_object* v_a_1357_ = _args[17];
lean_object* v_a_1358_ = _args[18];
lean_object* v_a_1359_ = _args[19];
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(v_f_1340_, v_00_u03b1_1341_, v_c_1342_, v_inst_1343_, v_a_1344_, v_b_1345_, v_c_x27_1346_, v_h_1347_, v_inst_x27_1348_, v_fallback_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
lean_dec(v_a_1358_);
lean_dec_ref(v_a_1357_);
lean_dec(v_a_1356_);
lean_dec_ref(v_a_1355_);
lean_dec(v_a_1354_);
lean_dec_ref(v_a_1353_);
lean_dec(v_a_1352_);
lean_dec_ref(v_a_1351_);
lean_dec(v_a_1350_);
lean_dec_ref(v_f_1340_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(lean_object* v_f_1361_, lean_object* v_00_u03b1_1362_, lean_object* v_c_1363_, lean_object* v_inst_1364_, lean_object* v_a_1365_, lean_object* v_b_1366_, lean_object* v_fallback_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_){
_start:
{
lean_object* v___x_1378_; 
lean_inc(v_a_1376_);
lean_inc_ref(v_a_1375_);
lean_inc(v_a_1374_);
lean_inc_ref(v_a_1373_);
lean_inc(v_a_1372_);
lean_inc_ref(v_a_1371_);
lean_inc(v_a_1370_);
lean_inc_ref(v_a_1369_);
lean_inc(v_a_1368_);
lean_inc_ref(v_inst_1364_);
v___x_1378_ = lean_sym_simp(v_inst_1364_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1379_);
lean_dec_ref_known(v___x_1378_, 1);
if (lean_obj_tag(v_a_1379_) == 0)
{
uint8_t v_contextDependent_1380_; lean_object* v___x_1381_; 
v_contextDependent_1380_ = lean_ctor_get_uint8(v_a_1379_, 1);
lean_dec_ref_known(v_a_1379_, 0);
lean_inc_ref(v_inst_1364_);
v___x_1381_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(v_f_1361_, v_00_u03b1_1362_, v_c_1363_, v_inst_1364_, v_a_1365_, v_b_1366_, v_inst_1364_, v_fallback_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; uint8_t v___y_1384_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
if (v_contextDependent_1380_ == 0)
{
lean_dec(v_a_1382_);
return v___x_1381_;
}
else
{
if (lean_obj_tag(v_a_1382_) == 0)
{
uint8_t v_contextDependent_1394_; 
v_contextDependent_1394_ = lean_ctor_get_uint8(v_a_1382_, 1);
v___y_1384_ = v_contextDependent_1394_;
goto v___jp_1383_;
}
else
{
uint8_t v_contextDependent_1395_; 
v_contextDependent_1395_ = lean_ctor_get_uint8(v_a_1382_, sizeof(void*)*2 + 1);
v___y_1384_ = v_contextDependent_1395_;
goto v___jp_1383_;
}
}
v___jp_1383_:
{
if (v___y_1384_ == 0)
{
lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1392_; 
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1392_ == 0)
{
lean_object* v_unused_1393_; 
v_unused_1393_ = lean_ctor_get(v___x_1381_, 0);
lean_dec(v_unused_1393_);
v___x_1386_ = v___x_1381_;
v_isShared_1387_ = v_isSharedCheck_1392_;
goto v_resetjp_1385_;
}
else
{
lean_dec(v___x_1381_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1392_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; lean_object* v___x_1390_; 
v___x_1388_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1382_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v___x_1388_);
v___x_1390_ = v___x_1386_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1388_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
else
{
lean_dec(v_a_1382_);
return v___x_1381_;
}
}
}
else
{
return v___x_1381_;
}
}
else
{
lean_object* v_e_x27_1396_; uint8_t v_contextDependent_1397_; lean_object* v___x_1398_; 
v_e_x27_1396_ = lean_ctor_get(v_a_1379_, 0);
lean_inc_ref(v_e_x27_1396_);
v_contextDependent_1397_ = lean_ctor_get_uint8(v_a_1379_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1379_, 2);
v___x_1398_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(v_f_1361_, v_00_u03b1_1362_, v_c_1363_, v_inst_1364_, v_a_1365_, v_b_1366_, v_e_x27_1396_, v_fallback_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; uint8_t v___y_1401_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1399_);
if (v_contextDependent_1397_ == 0)
{
lean_dec(v_a_1399_);
return v___x_1398_;
}
else
{
if (lean_obj_tag(v_a_1399_) == 0)
{
uint8_t v_contextDependent_1411_; 
v_contextDependent_1411_ = lean_ctor_get_uint8(v_a_1399_, 1);
v___y_1401_ = v_contextDependent_1411_;
goto v___jp_1400_;
}
else
{
uint8_t v_contextDependent_1412_; 
v_contextDependent_1412_ = lean_ctor_get_uint8(v_a_1399_, sizeof(void*)*2 + 1);
v___y_1401_ = v_contextDependent_1412_;
goto v___jp_1400_;
}
}
v___jp_1400_:
{
if (v___y_1401_ == 0)
{
lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1409_; 
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1409_ == 0)
{
lean_object* v_unused_1410_; 
v_unused_1410_ = lean_ctor_get(v___x_1398_, 0);
lean_dec(v_unused_1410_);
v___x_1403_ = v___x_1398_;
v_isShared_1404_ = v_isSharedCheck_1409_;
goto v_resetjp_1402_;
}
else
{
lean_dec(v___x_1398_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1409_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1405_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1399_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1405_);
v___x_1407_ = v___x_1403_;
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
else
{
lean_dec(v_a_1399_);
return v___x_1398_;
}
}
}
else
{
return v___x_1398_;
}
}
}
else
{
lean_dec_ref(v_fallback_1367_);
lean_dec_ref(v_b_1366_);
lean_dec_ref(v_a_1365_);
lean_dec_ref(v_inst_1364_);
lean_dec_ref(v_c_1363_);
lean_dec_ref(v_00_u03b1_1362_);
return v___x_1378_;
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
uint8_t v_contextDependent_1467_; 
v_contextDependent_1467_ = lean_ctor_get_uint8(v_a_1455_, 1);
v___y_1457_ = v_contextDependent_1467_;
goto v___jp_1456_;
}
else
{
uint8_t v_contextDependent_1468_; 
v_contextDependent_1468_ = lean_ctor_get_uint8(v_a_1455_, sizeof(void*)*2 + 1);
v___y_1457_ = v_contextDependent_1468_;
goto v___jp_1456_;
}
}
v___jp_1456_:
{
if (v___y_1457_ == 0)
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
else
{
lean_dec(v_a_1455_);
return v___x_1454_;
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
lean_object* v_e_x27_1469_; uint8_t v_contextDependent_1470_; lean_object* v___x_1471_; 
lean_dec_ref(v_inst_x27_1439_);
v_e_x27_1469_ = lean_ctor_get(v_a_1452_, 0);
lean_inc_ref(v_e_x27_1469_);
v_contextDependent_1470_ = lean_ctor_get_uint8(v_a_1452_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1452_, 2);
v___x_1471_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(v_f_1431_, v_00_u03b1_1432_, v_c_1433_, v_inst_1434_, v_a_1435_, v_b_1436_, v_c_x27_1437_, v_h_1438_, v_e_x27_1469_, v_fallback_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; uint8_t v___y_1474_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
if (v_contextDependent_1470_ == 0)
{
lean_dec(v_a_1472_);
return v___x_1471_;
}
else
{
if (lean_obj_tag(v_a_1472_) == 0)
{
uint8_t v_contextDependent_1484_; 
v_contextDependent_1484_ = lean_ctor_get_uint8(v_a_1472_, 1);
v___y_1474_ = v_contextDependent_1484_;
goto v___jp_1473_;
}
else
{
uint8_t v_contextDependent_1485_; 
v_contextDependent_1485_ = lean_ctor_get_uint8(v_a_1472_, sizeof(void*)*2 + 1);
v___y_1474_ = v_contextDependent_1485_;
goto v___jp_1473_;
}
}
v___jp_1473_:
{
if (v___y_1474_ == 0)
{
lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1482_; 
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1482_ == 0)
{
lean_object* v_unused_1483_; 
v_unused_1483_ = lean_ctor_get(v___x_1471_, 0);
lean_dec(v_unused_1483_);
v___x_1476_ = v___x_1471_;
v_isShared_1477_ = v_isSharedCheck_1482_;
goto v_resetjp_1475_;
}
else
{
lean_dec(v___x_1471_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1482_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1478_; lean_object* v___x_1480_; 
v___x_1478_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1472_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 0, v___x_1478_);
v___x_1480_ = v___x_1476_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
else
{
lean_dec(v_a_1472_);
return v___x_1471_;
}
}
}
else
{
return v___x_1471_;
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
lean_object* v_f_1486_ = _args[0];
lean_object* v_00_u03b1_1487_ = _args[1];
lean_object* v_c_1488_ = _args[2];
lean_object* v_inst_1489_ = _args[3];
lean_object* v_a_1490_ = _args[4];
lean_object* v_b_1491_ = _args[5];
lean_object* v_c_x27_1492_ = _args[6];
lean_object* v_h_1493_ = _args[7];
lean_object* v_inst_x27_1494_ = _args[8];
lean_object* v_fallback_1495_ = _args[9];
lean_object* v_a_1496_ = _args[10];
lean_object* v_a_1497_ = _args[11];
lean_object* v_a_1498_ = _args[12];
lean_object* v_a_1499_ = _args[13];
lean_object* v_a_1500_ = _args[14];
lean_object* v_a_1501_ = _args[15];
lean_object* v_a_1502_ = _args[16];
lean_object* v_a_1503_ = _args[17];
lean_object* v_a_1504_ = _args[18];
lean_object* v_a_1505_ = _args[19];
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr(v_f_1486_, v_00_u03b1_1487_, v_c_1488_, v_inst_1489_, v_a_1490_, v_b_1491_, v_c_x27_1492_, v_h_1493_, v_inst_x27_1494_, v_fallback_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
lean_dec(v_a_1504_);
lean_dec_ref(v_a_1503_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
lean_dec(v_a_1498_);
lean_dec_ref(v_a_1497_);
lean_dec(v_a_1496_);
lean_dec_ref(v_f_1486_);
return v_res_1506_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = lean_unsigned_to_nat(0u);
v___x_1511_ = l_Lean_mkBVar(v___x_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1(lean_object* v_proof_1517_, lean_object* v___x_1518_, lean_object* v_arg_1519_, lean_object* v_e_x27_1520_, lean_object* v_arg_1521_, uint8_t v_a_1522_, lean_object* v_arg_1523_, lean_object* v___x_1524_, lean_object* v___x_1525_, lean_object* v_e_1526_, uint8_t v___x_1527_, uint8_t v_contextDependent_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = l_Lean_Meta_Sym_shareCommon(v_proof_1517_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1541_; uint8_t v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc_n(v_a_1540_, 2);
lean_dec_ref_known(v___x_1539_, 1);
v___x_1541_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__1));
v___x_1542_ = 0;
v___x_1543_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2));
lean_inc(v___x_1518_);
v___x_1544_ = l_Lean_mkConst(v___x_1543_, v___x_1518_);
v___x_1545_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__2);
lean_inc_ref_n(v_e_x27_1520_, 2);
lean_inc_ref(v_arg_1519_);
v___x_1546_ = l_Lean_mkApp4(v___x_1544_, v_arg_1519_, v_e_x27_1520_, v_a_1540_, v___x_1545_);
v___x_1547_ = lean_unsigned_to_nat(1u);
v___x_1548_ = lean_mk_empty_array_with_capacity(v___x_1547_);
lean_inc_ref(v___x_1548_);
v___x_1549_ = lean_array_push(v___x_1548_, v___x_1546_);
v___x_1550_ = l_Lean_Expr_betaRev(v_arg_1521_, v___x_1549_, v_a_1522_, v_a_1522_);
lean_dec_ref(v___x_1549_);
v___x_1551_ = l_Lean_mkLambda(v___x_1541_, v___x_1542_, v_e_x27_1520_, v___x_1550_);
v___x_1552_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1551_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref_known(v___x_1552_, 1);
lean_inc_ref_n(v_e_x27_1520_, 2);
v___x_1554_ = l_Lean_mkNot(v_e_x27_1520_);
v___x_1555_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7));
v___x_1556_ = l_Lean_mkConst(v___x_1555_, v___x_1518_);
lean_inc(v_a_1540_);
v___x_1557_ = l_Lean_mkApp4(v___x_1556_, v_arg_1519_, v_e_x27_1520_, v_a_1540_, v___x_1545_);
v___x_1558_ = lean_array_push(v___x_1548_, v___x_1557_);
v___x_1559_ = l_Lean_Expr_betaRev(v_arg_1523_, v___x_1558_, v_a_1522_, v_a_1522_);
lean_dec_ref(v___x_1558_);
v___x_1560_ = l_Lean_mkLambda(v___x_1541_, v___x_1542_, v___x_1554_, v___x_1559_);
v___x_1561_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1560_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v___x_1563_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref_known(v___x_1561_, 1);
lean_inc_ref(v___x_1525_);
lean_inc_ref(v_e_x27_1520_);
v___x_1563_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(v___x_1524_, v_e_x27_1520_, v___x_1525_, v_a_1553_, v_a_1562_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1575_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1566_ = v___x_1563_;
v_isShared_1567_ = v_isSharedCheck_1575_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1563_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1575_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1568_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__4));
v___x_1569_ = l_Lean_Expr_replaceFn(v_e_1526_, v___x_1568_);
v___x_1570_ = l_Lean_mkApp3(v___x_1569_, v_e_x27_1520_, v___x_1525_, v_a_1540_);
v___x_1571_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1571_, 0, v_a_1564_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
lean_ctor_set_uint8(v___x_1571_, sizeof(void*)*2, v___x_1527_);
lean_ctor_set_uint8(v___x_1571_, sizeof(void*)*2 + 1, v_contextDependent_1528_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v___x_1571_);
v___x_1573_ = v___x_1566_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_dec(v_a_1540_);
lean_dec_ref(v_e_1526_);
lean_dec_ref(v___x_1525_);
lean_dec_ref(v_e_x27_1520_);
v_a_1576_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1563_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1563_);
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
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_dec(v_a_1553_);
lean_dec(v_a_1540_);
lean_dec_ref(v_e_1526_);
lean_dec_ref(v___x_1525_);
lean_dec_ref(v___x_1524_);
lean_dec_ref(v_e_x27_1520_);
v_a_1584_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1561_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1561_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
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
lean_dec_ref(v___x_1548_);
lean_dec(v_a_1540_);
lean_dec_ref(v_e_1526_);
lean_dec_ref(v___x_1525_);
lean_dec_ref(v___x_1524_);
lean_dec_ref(v_arg_1523_);
lean_dec_ref(v_e_x27_1520_);
lean_dec_ref(v_arg_1519_);
lean_dec(v___x_1518_);
v_a_1592_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1552_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1552_);
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
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
lean_dec_ref(v_e_1526_);
lean_dec_ref(v___x_1525_);
lean_dec_ref(v___x_1524_);
lean_dec_ref(v_arg_1523_);
lean_dec_ref(v_arg_1521_);
lean_dec_ref(v_e_x27_1520_);
lean_dec_ref(v_arg_1519_);
lean_dec(v___x_1518_);
v_a_1600_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1539_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1539_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___boxed(lean_object** _args){
lean_object* v_proof_1608_ = _args[0];
lean_object* v___x_1609_ = _args[1];
lean_object* v_arg_1610_ = _args[2];
lean_object* v_e_x27_1611_ = _args[3];
lean_object* v_arg_1612_ = _args[4];
lean_object* v_a_1613_ = _args[5];
lean_object* v_arg_1614_ = _args[6];
lean_object* v___x_1615_ = _args[7];
lean_object* v___x_1616_ = _args[8];
lean_object* v_e_1617_ = _args[9];
lean_object* v___x_1618_ = _args[10];
lean_object* v_contextDependent_1619_ = _args[11];
lean_object* v___y_1620_ = _args[12];
lean_object* v___y_1621_ = _args[13];
lean_object* v___y_1622_ = _args[14];
lean_object* v___y_1623_ = _args[15];
lean_object* v___y_1624_ = _args[16];
lean_object* v___y_1625_ = _args[17];
lean_object* v___y_1626_ = _args[18];
lean_object* v___y_1627_ = _args[19];
lean_object* v___y_1628_ = _args[20];
lean_object* v___y_1629_ = _args[21];
_start:
{
uint8_t v_a_32592__boxed_1630_; uint8_t v___x_32596__boxed_1631_; uint8_t v_contextDependent_32597__boxed_1632_; lean_object* v_res_1633_; 
v_a_32592__boxed_1630_ = lean_unbox(v_a_1613_);
v___x_32596__boxed_1631_ = lean_unbox(v___x_1618_);
v_contextDependent_32597__boxed_1632_ = lean_unbox(v_contextDependent_1619_);
v_res_1633_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1(v_proof_1608_, v___x_1609_, v_arg_1610_, v_e_x27_1611_, v_arg_1612_, v_a_32592__boxed_1630_, v_arg_1614_, v___x_1615_, v___x_1616_, v_e_1617_, v___x_32596__boxed_1631_, v_contextDependent_32597__boxed_1632_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
return v_res_1633_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1640_ = lean_box(0);
v___x_1641_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
v___x_1642_ = l_Lean_mkConst(v___x_1641_, v___x_1640_);
return v___x_1642_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1643_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4);
v___x_1644_ = lean_unsigned_to_nat(1u);
v___x_1645_ = lean_mk_empty_array_with_capacity(v___x_1644_);
v___x_1646_ = lean_array_push(v___x_1645_, v___x_1643_);
return v___x_1646_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10(void){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1654_ = lean_box(0);
v___x_1655_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9));
v___x_1656_ = l_Lean_mkConst(v___x_1655_, v___x_1654_);
return v___x_1656_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11(void){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1657_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10);
v___x_1658_ = lean_unsigned_to_nat(1u);
v___x_1659_ = lean_mk_empty_array_with_capacity(v___x_1658_);
v___x_1660_ = lean_array_push(v___x_1659_, v___x_1657_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0(uint8_t v___x_1669_, lean_object* v_e_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v___x_1684_; uint8_t v___x_1685_; 
lean_inc_ref(v_e_1670_);
v___x_1684_ = l_Lean_Expr_cleanupAnnotations(v_e_1670_);
v___x_1685_ = l_Lean_Expr_isApp(v___x_1684_);
if (v___x_1685_ == 0)
{
lean_dec_ref(v___x_1684_);
lean_dec_ref(v_e_1670_);
goto v___jp_1681_;
}
else
{
lean_object* v_arg_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
v_arg_1686_ = lean_ctor_get(v___x_1684_, 1);
lean_inc_ref(v_arg_1686_);
v___x_1687_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1684_);
v___x_1688_ = l_Lean_Expr_isApp(v___x_1687_);
if (v___x_1688_ == 0)
{
lean_dec_ref(v___x_1687_);
lean_dec_ref(v_arg_1686_);
lean_dec_ref(v_e_1670_);
goto v___jp_1681_;
}
else
{
lean_object* v_arg_1689_; lean_object* v___x_1690_; uint8_t v___x_1691_; 
v_arg_1689_ = lean_ctor_get(v___x_1687_, 1);
lean_inc_ref(v_arg_1689_);
v___x_1690_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1687_);
v___x_1691_ = l_Lean_Expr_isApp(v___x_1690_);
if (v___x_1691_ == 0)
{
lean_dec_ref(v___x_1690_);
lean_dec_ref(v_arg_1689_);
lean_dec_ref(v_arg_1686_);
lean_dec_ref(v_e_1670_);
goto v___jp_1681_;
}
else
{
lean_object* v_arg_1692_; lean_object* v___x_1693_; uint8_t v___x_1694_; 
v_arg_1692_ = lean_ctor_get(v___x_1690_, 1);
lean_inc_ref(v_arg_1692_);
v___x_1693_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1690_);
v___x_1694_ = l_Lean_Expr_isApp(v___x_1693_);
if (v___x_1694_ == 0)
{
lean_dec_ref(v___x_1693_);
lean_dec_ref(v_arg_1692_);
lean_dec_ref(v_arg_1689_);
lean_dec_ref(v_arg_1686_);
lean_dec_ref(v_e_1670_);
goto v___jp_1681_;
}
else
{
lean_object* v_arg_1695_; lean_object* v___x_1696_; uint8_t v___x_1697_; 
v_arg_1695_ = lean_ctor_get(v___x_1693_, 1);
lean_inc_ref(v_arg_1695_);
v___x_1696_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1693_);
v___x_1697_ = l_Lean_Expr_isApp(v___x_1696_);
if (v___x_1697_ == 0)
{
lean_dec_ref(v___x_1696_);
lean_dec_ref(v_arg_1695_);
lean_dec_ref(v_arg_1692_);
lean_dec_ref(v_arg_1689_);
lean_dec_ref(v_arg_1686_);
lean_dec_ref(v_e_1670_);
goto v___jp_1681_;
}
else
{
lean_object* v_arg_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; uint8_t v___x_1701_; 
v_arg_1698_ = lean_ctor_get(v___x_1696_, 1);
lean_inc_ref(v_arg_1698_);
v___x_1699_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1696_);
v___x_1700_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1));
v___x_1701_ = l_Lean_Expr_isConstOf(v___x_1699_, v___x_1700_);
if (v___x_1701_ == 0)
{
lean_dec_ref(v___x_1699_);
lean_dec_ref(v_arg_1698_);
lean_dec_ref(v_arg_1695_);
lean_dec_ref(v_arg_1692_);
lean_dec_ref(v_arg_1689_);
lean_dec_ref(v_arg_1686_);
lean_dec_ref(v_e_1670_);
goto v___jp_1681_;
}
else
{
lean_object* v___x_1702_; 
lean_inc(v___y_1679_);
lean_inc_ref(v___y_1678_);
lean_inc(v___y_1677_);
lean_inc_ref(v___y_1676_);
lean_inc(v___y_1675_);
lean_inc_ref(v___y_1674_);
lean_inc(v___y_1673_);
lean_inc_ref(v___y_1672_);
lean_inc(v___y_1671_);
lean_inc_ref(v_arg_1695_);
v___x_1702_ = lean_sym_simp(v_arg_1695_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref_known(v___x_1702_, 1);
if (lean_obj_tag(v_a_1703_) == 0)
{
uint8_t v_contextDependent_1704_; lean_object* v___x_1705_; 
lean_dec_ref(v_e_1670_);
v_contextDependent_1704_ = lean_ctor_get_uint8(v_a_1703_, 1);
lean_dec_ref_known(v_a_1703_, 0);
v___x_1705_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_1695_, v___y_1674_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; uint8_t v___x_1707_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref_known(v___x_1705_, 1);
v___x_1707_ = lean_unbox(v_a_1706_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_1695_, v___y_1674_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; uint8_t v___x_1710_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1709_);
lean_dec_ref_known(v___x_1708_, 1);
v___x_1710_ = lean_unbox(v_a_1709_);
lean_dec(v_a_1709_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; lean_object* v___f_1712_; lean_object* v___x_1713_; 
lean_dec(v_a_1706_);
v___x_1711_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_1701_, v_contextDependent_1704_);
v___f_1712_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1712_, 0, v___x_1711_);
v___x_1713_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(v___x_1699_, v_arg_1698_, v_arg_1695_, v_arg_1692_, v_arg_1689_, v_arg_1686_, v___f_1712_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
lean_dec_ref(v___x_1699_);
return v___x_1713_;
}
else
{
lean_object* v___x_1714_; uint8_t v___x_1715_; uint8_t v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
lean_dec_ref(v_arg_1695_);
lean_dec_ref(v_arg_1692_);
v___x_1714_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5);
v___x_1715_ = lean_unbox(v_a_1706_);
v___x_1716_ = lean_unbox(v_a_1706_);
lean_inc_ref(v_arg_1686_);
v___x_1717_ = l_Lean_Expr_betaRev(v_arg_1686_, v___x_1714_, v___x_1715_, v___x_1716_);
v___x_1718_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1717_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1732_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1721_ = v___x_1718_;
v_isShared_1722_ = v_isSharedCheck_1732_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1718_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1732_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; lean_object* v___x_1730_; 
v___x_1723_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6));
v___x_1724_ = l_Lean_Expr_constLevels_x21(v___x_1699_);
lean_dec_ref(v___x_1699_);
v___x_1725_ = l_Lean_mkConst(v___x_1723_, v___x_1724_);
v___x_1726_ = l_Lean_mkApp3(v___x_1725_, v_arg_1698_, v_arg_1689_, v_arg_1686_);
v___x_1727_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1727_, 0, v_a_1719_);
lean_ctor_set(v___x_1727_, 1, v___x_1726_);
v___x_1728_ = lean_unbox(v_a_1706_);
lean_dec(v_a_1706_);
lean_ctor_set_uint8(v___x_1727_, sizeof(void*)*2, v___x_1728_);
lean_ctor_set_uint8(v___x_1727_, sizeof(void*)*2 + 1, v_contextDependent_1704_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 0, v___x_1727_);
v___x_1730_ = v___x_1721_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1727_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_dec(v_a_1706_);
lean_dec_ref(v___x_1699_);
lean_dec_ref(v_arg_1698_);
lean_dec_ref(v_arg_1689_);
lean_dec_ref(v_arg_1686_);
v_a_1733_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1718_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1718_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_dec(v_a_1706_);
lean_dec_ref(v___x_1699_);
lean_dec_ref(v_arg_1698_);
lean_dec_ref(v_arg_1695_);
lean_dec_ref(v_arg_1692_);
lean_dec_ref(v_arg_1689_);
lean_dec_ref(v_arg_1686_);
v_a_1741_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1708_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1708_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
else
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
lean_dec(v_a_1706_);
lean_dec_ref(v_arg_1695_);
lean_dec_ref(v_arg_1692_);
v___x_1749_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11);
lean_inc_ref(v_arg_1689_);
v___x_1750_ = l_Lean_Expr_betaRev(v_arg_1689_, v___x_1749_, v___x_1669_, v___x_1669_);
v___x_1751_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1750_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1764_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1754_ = v___x_1751_;
v_isShared_1755_ = v_isSharedCheck_1764_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1751_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1764_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1762_; 
v___x_1756_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12));
v___x_1757_ = l_Lean_Expr_constLevels_x21(v___x_1699_);
lean_dec_ref(v___x_1699_);
v___x_1758_ = l_Lean_mkConst(v___x_1756_, v___x_1757_);
v___x_1759_ = l_Lean_mkApp3(v___x_1758_, v_arg_1698_, v_arg_1689_, v_arg_1686_);
v___x_1760_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1760_, 0, v_a_1752_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
lean_ctor_set_uint8(v___x_1760_, sizeof(void*)*2, v___x_1669_);
lean_ctor_set_uint8(v___x_1760_, sizeof(void*)*2 + 1, v_contextDependent_1704_);
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 0, v___x_1760_);
v___x_1762_ = v___x_1754_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1760_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
lean_dec_ref(v___x_1699_);
lean_dec_ref(v_arg_1698_);
lean_dec_ref(v_arg_1689_);
lean_dec_ref(v_arg_1686_);
v_a_1765_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1751_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1751_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec_ref(v___x_1699_);
lean_dec_ref(v_arg_1698_);
lean_dec_ref(v_arg_1695_);
lean_dec_ref(v_arg_1692_);
lean_dec_ref(v_arg_1689_);
lean_dec_ref(v_arg_1686_);
v_a_1773_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1705_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1705_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
else
{
lean_object* v_e_x27_1781_; lean_object* v_proof_1782_; uint8_t v_contextDependent_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1898_; 
v_e_x27_1781_ = lean_ctor_get(v_a_1703_, 0);
v_proof_1782_ = lean_ctor_get(v_a_1703_, 1);
v_contextDependent_1783_ = lean_ctor_get_uint8(v_a_1703_, sizeof(void*)*2 + 1);
v_isSharedCheck_1898_ = !lean_is_exclusive(v_a_1703_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1785_ = v_a_1703_;
v_isShared_1786_ = v_isSharedCheck_1898_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_proof_1782_);
lean_inc(v_e_x27_1781_);
lean_dec(v_a_1703_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1898_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1787_; 
v___x_1787_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_1781_, v___y_1674_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; uint8_t v___x_1789_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_a_1788_);
lean_dec_ref_known(v___x_1787_, 1);
v___x_1789_ = lean_unbox(v_a_1788_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_1781_, v___y_1674_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; uint8_t v___x_1792_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v___x_1790_, 1);
v___x_1792_ = lean_unbox(v_a_1791_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___f_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
lean_dec(v_a_1788_);
lean_del_object(v___x_1785_);
v___x_1793_ = lean_box(0);
v___x_1794_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6);
lean_inc_ref_n(v_proof_1782_, 2);
lean_inc_ref_n(v_arg_1692_, 2);
lean_inc_ref_n(v_e_x27_1781_, 2);
lean_inc_ref_n(v_arg_1695_, 3);
v___x_1795_ = l_Lean_mkApp4(v___x_1794_, v_arg_1695_, v_e_x27_1781_, v_arg_1692_, v_proof_1782_);
v___x_1796_ = lean_unsigned_to_nat(4u);
v___x_1797_ = l_Lean_Expr_getBoundedAppFn(v___x_1796_, v_e_1670_);
v___x_1798_ = lean_box(v___x_1701_);
v___x_1799_ = lean_box(v_contextDependent_1783_);
lean_inc_ref(v___x_1795_);
lean_inc_ref_n(v_arg_1686_, 2);
lean_inc_ref_n(v_arg_1689_, 2);
v___f_1800_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___boxed), 22, 12);
lean_closure_set(v___f_1800_, 0, v_proof_1782_);
lean_closure_set(v___f_1800_, 1, v___x_1793_);
lean_closure_set(v___f_1800_, 2, v_arg_1695_);
lean_closure_set(v___f_1800_, 3, v_e_x27_1781_);
lean_closure_set(v___f_1800_, 4, v_arg_1689_);
lean_closure_set(v___f_1800_, 5, v_a_1791_);
lean_closure_set(v___f_1800_, 6, v_arg_1686_);
lean_closure_set(v___f_1800_, 7, v___x_1797_);
lean_closure_set(v___f_1800_, 8, v___x_1795_);
lean_closure_set(v___f_1800_, 9, v_e_1670_);
lean_closure_set(v___f_1800_, 10, v___x_1798_);
lean_closure_set(v___f_1800_, 11, v___x_1799_);
lean_inc_ref(v_arg_1698_);
lean_inc_ref(v___x_1699_);
v___x_1801_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr___boxed), 20, 10);
lean_closure_set(v___x_1801_, 0, v___x_1699_);
lean_closure_set(v___x_1801_, 1, v_arg_1698_);
lean_closure_set(v___x_1801_, 2, v_arg_1695_);
lean_closure_set(v___x_1801_, 3, v_arg_1692_);
lean_closure_set(v___x_1801_, 4, v_arg_1689_);
lean_closure_set(v___x_1801_, 5, v_arg_1686_);
lean_closure_set(v___x_1801_, 6, v_e_x27_1781_);
lean_closure_set(v___x_1801_, 7, v_proof_1782_);
lean_closure_set(v___x_1801_, 8, v___x_1795_);
lean_closure_set(v___x_1801_, 9, v___f_1800_);
v___x_1802_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(v___x_1699_, v_arg_1698_, v_arg_1695_, v_arg_1692_, v_arg_1689_, v_arg_1686_, v___x_1801_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
lean_dec_ref(v___x_1699_);
return v___x_1802_;
}
else
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
lean_dec(v_a_1791_);
lean_dec_ref(v_e_x27_1781_);
lean_dec_ref(v___x_1699_);
lean_dec_ref(v_arg_1698_);
lean_dec_ref(v_arg_1692_);
lean_dec_ref(v_arg_1689_);
lean_inc_ref(v_proof_1782_);
v___x_1803_ = l_Lean_Meta_mkOfEqFalseCore(v_arg_1695_, v_proof_1782_);
v___x_1804_ = l_Lean_Meta_Sym_shareCommon(v___x_1803_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; uint8_t v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_a_1805_);
lean_dec_ref_known(v___x_1804_, 1);
v___x_1806_ = lean_unsigned_to_nat(1u);
v___x_1807_ = lean_mk_empty_array_with_capacity(v___x_1806_);
v___x_1808_ = lean_array_push(v___x_1807_, v_a_1805_);
v___x_1809_ = lean_unbox(v_a_1788_);
v___x_1810_ = lean_unbox(v_a_1788_);
v___x_1811_ = l_Lean_Expr_betaRev(v_arg_1686_, v___x_1808_, v___x_1809_, v___x_1810_);
lean_dec_ref(v___x_1808_);
v___x_1812_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1811_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1827_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1815_ = v___x_1812_;
v_isShared_1816_ = v_isSharedCheck_1827_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1812_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1827_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1817_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14));
v___x_1818_ = l_Lean_Expr_replaceFn(v_e_1670_, v___x_1817_);
v___x_1819_ = l_Lean_Expr_app___override(v___x_1818_, v_proof_1782_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 1, v___x_1819_);
lean_ctor_set(v___x_1785_, 0, v_a_1813_);
v___x_1821_ = v___x_1785_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1813_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
uint8_t v___x_1822_; lean_object* v___x_1824_; 
v___x_1822_ = lean_unbox(v_a_1788_);
lean_dec(v_a_1788_);
lean_ctor_set_uint8(v___x_1821_, sizeof(void*)*2, v___x_1822_);
lean_ctor_set_uint8(v___x_1821_, sizeof(void*)*2 + 1, v_contextDependent_1783_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1821_);
v___x_1824_ = v___x_1815_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1821_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
else
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1835_; 
lean_dec(v_a_1788_);
lean_del_object(v___x_1785_);
lean_dec_ref(v_proof_1782_);
lean_dec_ref(v_e_1670_);
v_a_1828_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1830_ = v___x_1812_;
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1812_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
lean_dec(v_a_1788_);
lean_del_object(v___x_1785_);
lean_dec_ref(v_proof_1782_);
lean_dec_ref(v_arg_1686_);
lean_dec_ref(v_e_1670_);
v_a_1836_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1804_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1804_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_dec(v_a_1788_);
lean_del_object(v___x_1785_);
lean_dec_ref(v_proof_1782_);
lean_dec_ref(v_e_x27_1781_);
lean_dec_ref(v___x_1699_);
lean_dec_ref(v_arg_1698_);
lean_dec_ref(v_arg_1695_);
lean_dec_ref(v_arg_1692_);
lean_dec_ref(v_arg_1689_);
lean_dec_ref(v_arg_1686_);
lean_dec_ref(v_e_1670_);
v_a_1844_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1790_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1790_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
else
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
lean_dec(v_a_1788_);
lean_dec_ref(v_e_x27_1781_);
lean_dec_ref(v___x_1699_);
lean_dec_ref(v_arg_1698_);
lean_dec_ref(v_arg_1692_);
lean_dec_ref(v_arg_1686_);
lean_inc_ref(v_proof_1782_);
v___x_1852_ = l_Lean_Meta_mkOfEqTrueCore(v_arg_1695_, v_proof_1782_);
v___x_1853_ = l_Lean_Meta_Sym_shareCommon(v___x_1852_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1854_);
lean_dec_ref_known(v___x_1853_, 1);
v___x_1855_ = lean_unsigned_to_nat(1u);
v___x_1856_ = lean_mk_empty_array_with_capacity(v___x_1855_);
v___x_1857_ = lean_array_push(v___x_1856_, v_a_1854_);
v___x_1858_ = l_Lean_Expr_betaRev(v_arg_1689_, v___x_1857_, v___x_1669_, v___x_1669_);
lean_dec_ref(v___x_1857_);
v___x_1859_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1858_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1873_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1862_ = v___x_1859_;
v_isShared_1863_ = v_isSharedCheck_1873_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1859_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1873_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1868_; 
v___x_1864_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16));
v___x_1865_ = l_Lean_Expr_replaceFn(v_e_1670_, v___x_1864_);
v___x_1866_ = l_Lean_Expr_app___override(v___x_1865_, v_proof_1782_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 1, v___x_1866_);
lean_ctor_set(v___x_1785_, 0, v_a_1860_);
v___x_1868_ = v___x_1785_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1860_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v___x_1866_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, sizeof(void*)*2 + 1, v_contextDependent_1783_);
v___x_1868_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
lean_object* v___x_1870_; 
lean_ctor_set_uint8(v___x_1868_, sizeof(void*)*2, v___x_1669_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v___x_1868_);
v___x_1870_ = v___x_1862_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1868_);
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
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_del_object(v___x_1785_);
lean_dec_ref(v_proof_1782_);
lean_dec_ref(v_e_1670_);
v_a_1874_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1859_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1859_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
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
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_del_object(v___x_1785_);
lean_dec_ref(v_proof_1782_);
lean_dec_ref(v_arg_1689_);
lean_dec_ref(v_e_1670_);
v_a_1882_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1853_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1853_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
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
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_del_object(v___x_1785_);
lean_dec_ref(v_proof_1782_);
lean_dec_ref(v_e_x27_1781_);
lean_dec_ref(v___x_1699_);
lean_dec_ref(v_arg_1698_);
lean_dec_ref(v_arg_1695_);
lean_dec_ref(v_arg_1692_);
lean_dec_ref(v_arg_1689_);
lean_dec_ref(v_arg_1686_);
lean_dec_ref(v_e_1670_);
v_a_1890_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1787_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1787_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1699_);
lean_dec_ref(v_arg_1698_);
lean_dec_ref(v_arg_1695_);
lean_dec_ref(v_arg_1692_);
lean_dec_ref(v_arg_1689_);
lean_dec_ref(v_arg_1686_);
lean_dec_ref(v_e_1670_);
return v___x_1702_;
}
}
}
}
}
}
}
v___jp_1681_:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1682_, 0, v___x_1669_);
lean_ctor_set_uint8(v___x_1682_, 1, v___x_1669_);
v___x_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1682_);
return v___x_1683_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___boxed(lean_object* v___x_1899_, lean_object* v_e_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
uint8_t v___x_32876__boxed_1911_; lean_object* v_res_1912_; 
v___x_32876__boxed_1911_ = lean_unbox(v___x_1899_);
v_res_1912_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0(v___x_32876__boxed_1911_, v_e_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv(lean_object* v_e_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_){
_start:
{
lean_object* v_numArgs_1924_; lean_object* v___x_1925_; uint8_t v___x_1926_; 
v_numArgs_1924_ = l_Lean_Expr_getAppNumArgs(v_e_1913_);
v___x_1925_ = lean_unsigned_to_nat(5u);
v___x_1926_ = lean_nat_dec_lt(v_numArgs_1924_, v___x_1925_);
if (v___x_1926_ == 0)
{
lean_object* v___x_1927_; lean_object* v___f_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1927_ = lean_box(v___x_1926_);
v___f_1928_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___boxed), 12, 1);
lean_closure_set(v___f_1928_, 0, v___x_1927_);
v___x_1929_ = lean_nat_sub(v_numArgs_1924_, v___x_1925_);
lean_dec(v_numArgs_1924_);
v___x_1930_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_1913_, v___x_1929_, v___f_1928_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
lean_dec(v___x_1929_);
return v___x_1930_;
}
else
{
uint8_t v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
lean_dec(v_numArgs_1924_);
lean_dec_ref(v_e_1913_);
v___x_1931_ = 0;
v___x_1932_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1932_, 0, v___x_1926_);
lean_ctor_set_uint8(v___x_1932_, 1, v___x_1931_);
v___x_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
return v___x_1933_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___boxed(lean_object* v_e_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv(v_e_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
lean_dec(v_a_1939_);
lean_dec_ref(v_a_1938_);
lean_dec(v_a_1937_);
lean_dec_ref(v_a_1936_);
lean_dec(v_a_1935_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1964_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_17_));
v___x_1965_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_17_));
v___x_1966_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___boxed), 11, 0);
v___x_1967_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_1964_, v___x_1965_, v___x_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_17____boxed(lean_object* v_a_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_17_();
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1971_; uint8_t v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1971_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_17_));
v___x_1972_ = 0;
v___x_1973_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___boxed), 11, 0);
v___x_1974_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_1971_, v___x_1972_, v___x_1973_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_19____boxed(lean_object* v_a_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_19_();
return v_res_1976_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2(void){
_start:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1982_ = lean_box(0);
v___x_1983_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1));
v___x_1984_ = l_Lean_mkConst(v___x_1983_, v___x_1982_);
return v___x_1984_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5(void){
_start:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1990_ = lean_box(0);
v___x_1991_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4));
v___x_1992_ = l_Lean_mkConst(v___x_1991_, v___x_1990_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(lean_object* v_p_1993_, lean_object* v_inst_1994_, lean_object* v_instToMatch_1995_, lean_object* v_fallback_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_){
_start:
{
lean_object* v___x_2007_; 
v___x_2007_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_instToMatch_1995_, v_a_2003_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2009_; uint8_t v___x_2010_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref_known(v___x_2007_, 1);
v___x_2009_ = l_Lean_Expr_cleanupAnnotations(v_a_2008_);
v___x_2010_ = l_Lean_Expr_isApp(v___x_2009_);
if (v___x_2010_ == 0)
{
lean_object* v___x_2011_; 
lean_dec_ref(v___x_2009_);
lean_dec_ref(v_inst_1994_);
lean_dec_ref(v_p_1993_);
lean_inc(v_a_2005_);
lean_inc_ref(v_a_2004_);
lean_inc(v_a_2003_);
lean_inc_ref(v_a_2002_);
lean_inc(v_a_2001_);
lean_inc_ref(v_a_2000_);
lean_inc(v_a_1999_);
lean_inc_ref(v_a_1998_);
lean_inc(v_a_1997_);
v___x_2011_ = lean_apply_10(v_fallback_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, lean_box(0));
return v___x_2011_;
}
else
{
lean_object* v_arg_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v_arg_2012_ = lean_ctor_get(v___x_2009_, 1);
lean_inc_ref(v_arg_2012_);
v___x_2013_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2009_);
v___x_2014_ = l_Lean_Expr_isApp(v___x_2013_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; 
lean_dec_ref(v___x_2013_);
lean_dec_ref(v_arg_2012_);
lean_dec_ref(v_inst_1994_);
lean_dec_ref(v_p_1993_);
lean_inc(v_a_2005_);
lean_inc_ref(v_a_2004_);
lean_inc(v_a_2003_);
lean_inc_ref(v_a_2002_);
lean_inc(v_a_2001_);
lean_inc_ref(v_a_2000_);
lean_inc(v_a_1999_);
lean_inc_ref(v_a_1998_);
lean_inc(v_a_1997_);
v___x_2015_ = lean_apply_10(v_fallback_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, lean_box(0));
return v___x_2015_;
}
else
{
lean_object* v___x_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; 
v___x_2016_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2013_);
v___x_2017_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_2018_ = l_Lean_Expr_isConstOf(v___x_2016_, v___x_2017_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; uint8_t v___x_2020_; 
v___x_2019_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3));
v___x_2020_ = l_Lean_Expr_isConstOf(v___x_2016_, v___x_2019_);
lean_dec_ref(v___x_2016_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; 
lean_dec_ref(v_arg_2012_);
lean_dec_ref(v_inst_1994_);
lean_dec_ref(v_p_1993_);
lean_inc(v_a_2005_);
lean_inc_ref(v_a_2004_);
lean_inc(v_a_2003_);
lean_inc_ref(v_a_2002_);
lean_inc(v_a_2001_);
lean_inc_ref(v_a_2000_);
lean_inc(v_a_1999_);
lean_inc_ref(v_a_1998_);
lean_inc(v_a_1997_);
v___x_2021_ = lean_apply_10(v_fallback_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, lean_box(0));
return v___x_2021_;
}
else
{
lean_object* v___x_2022_; 
lean_dec_ref(v_fallback_1996_);
v___x_2022_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2000_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2033_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2025_ = v___x_2022_;
v_isShared_2026_ = v_isSharedCheck_2033_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2022_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2033_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2031_; 
v___x_2027_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2);
v___x_2028_ = l_Lean_mkApp3(v___x_2027_, v_p_1993_, v_inst_1994_, v_arg_2012_);
v___x_2029_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2029_, 0, v_a_2023_);
lean_ctor_set(v___x_2029_, 1, v___x_2028_);
lean_ctor_set_uint8(v___x_2029_, sizeof(void*)*2, v___x_2018_);
lean_ctor_set_uint8(v___x_2029_, sizeof(void*)*2 + 1, v___x_2018_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v___x_2029_);
v___x_2031_ = v___x_2025_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2029_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_dec_ref(v_arg_2012_);
lean_dec_ref(v_inst_1994_);
lean_dec_ref(v_p_1993_);
v_a_2034_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_2022_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2022_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
}
else
{
lean_object* v___x_2042_; 
lean_dec_ref(v___x_2016_);
lean_dec_ref(v_fallback_1996_);
v___x_2042_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2000_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2054_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2045_ = v___x_2042_;
v_isShared_2046_ = v_isSharedCheck_2054_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2042_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2054_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2052_; 
v___x_2047_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5);
v___x_2048_ = l_Lean_mkApp3(v___x_2047_, v_p_1993_, v_inst_1994_, v_arg_2012_);
v___x_2049_ = 0;
v___x_2050_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2050_, 0, v_a_2043_);
lean_ctor_set(v___x_2050_, 1, v___x_2048_);
lean_ctor_set_uint8(v___x_2050_, sizeof(void*)*2, v___x_2049_);
lean_ctor_set_uint8(v___x_2050_, sizeof(void*)*2 + 1, v___x_2049_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 0, v___x_2050_);
v___x_2052_ = v___x_2045_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec_ref(v_arg_2012_);
lean_dec_ref(v_inst_1994_);
lean_dec_ref(v_p_1993_);
v_a_2055_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2042_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2042_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec_ref(v_fallback_1996_);
lean_dec_ref(v_inst_1994_);
lean_dec_ref(v_p_1993_);
v_a_2063_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2007_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2007_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___boxed(lean_object* v_p_2071_, lean_object* v_inst_2072_, lean_object* v_instToMatch_2073_, lean_object* v_fallback_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(v_p_2071_, v_inst_2072_, v_instToMatch_2073_, v_fallback_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
lean_dec(v_a_2075_);
return v_res_2085_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2091_ = lean_box(0);
v___x_2092_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1));
v___x_2093_ = l_Lean_mkConst(v___x_2092_, v___x_2091_);
return v___x_2093_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5(void){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2099_ = lean_box(0);
v___x_2100_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4));
v___x_2101_ = l_Lean_mkConst(v___x_2100_, v___x_2099_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(lean_object* v_p_2102_, lean_object* v_p_x27_2103_, lean_object* v_h_2104_, lean_object* v_inst_2105_, lean_object* v_inst_x27_2106_, lean_object* v_fallback_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_inst_x27_2106_, v_a_2114_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2120_; uint8_t v___x_2121_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref_known(v___x_2118_, 1);
v___x_2120_ = l_Lean_Expr_cleanupAnnotations(v_a_2119_);
v___x_2121_ = l_Lean_Expr_isApp(v___x_2120_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; 
lean_dec_ref(v___x_2120_);
lean_dec_ref(v_inst_2105_);
lean_dec_ref(v_h_2104_);
lean_dec_ref(v_p_x27_2103_);
lean_dec_ref(v_p_2102_);
lean_inc(v_a_2116_);
lean_inc_ref(v_a_2115_);
lean_inc(v_a_2114_);
lean_inc_ref(v_a_2113_);
lean_inc(v_a_2112_);
lean_inc_ref(v_a_2111_);
lean_inc(v_a_2110_);
lean_inc_ref(v_a_2109_);
lean_inc(v_a_2108_);
v___x_2122_ = lean_apply_10(v_fallback_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, lean_box(0));
return v___x_2122_;
}
else
{
lean_object* v_arg_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; 
v_arg_2123_ = lean_ctor_get(v___x_2120_, 1);
lean_inc_ref(v_arg_2123_);
v___x_2124_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2120_);
v___x_2125_ = l_Lean_Expr_isApp(v___x_2124_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; 
lean_dec_ref(v___x_2124_);
lean_dec_ref(v_arg_2123_);
lean_dec_ref(v_inst_2105_);
lean_dec_ref(v_h_2104_);
lean_dec_ref(v_p_x27_2103_);
lean_dec_ref(v_p_2102_);
lean_inc(v_a_2116_);
lean_inc_ref(v_a_2115_);
lean_inc(v_a_2114_);
lean_inc_ref(v_a_2113_);
lean_inc(v_a_2112_);
lean_inc_ref(v_a_2111_);
lean_inc(v_a_2110_);
lean_inc_ref(v_a_2109_);
lean_inc(v_a_2108_);
v___x_2126_ = lean_apply_10(v_fallback_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, lean_box(0));
return v___x_2126_;
}
else
{
lean_object* v___x_2127_; lean_object* v___x_2128_; uint8_t v___x_2129_; 
v___x_2127_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2124_);
v___x_2128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_2129_ = l_Lean_Expr_isConstOf(v___x_2127_, v___x_2128_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2130_; uint8_t v___x_2131_; 
v___x_2130_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3));
v___x_2131_ = l_Lean_Expr_isConstOf(v___x_2127_, v___x_2130_);
lean_dec_ref(v___x_2127_);
if (v___x_2131_ == 0)
{
lean_object* v___x_2132_; 
lean_dec_ref(v_arg_2123_);
lean_dec_ref(v_inst_2105_);
lean_dec_ref(v_h_2104_);
lean_dec_ref(v_p_x27_2103_);
lean_dec_ref(v_p_2102_);
lean_inc(v_a_2116_);
lean_inc_ref(v_a_2115_);
lean_inc(v_a_2114_);
lean_inc_ref(v_a_2113_);
lean_inc(v_a_2112_);
lean_inc_ref(v_a_2111_);
lean_inc(v_a_2110_);
lean_inc_ref(v_a_2109_);
lean_inc(v_a_2108_);
v___x_2132_ = lean_apply_10(v_fallback_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, lean_box(0));
return v___x_2132_;
}
else
{
lean_object* v___x_2133_; 
lean_dec_ref(v_fallback_2107_);
v___x_2133_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2111_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2144_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2144_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2144_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2138_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2);
v___x_2139_ = l_Lean_mkApp5(v___x_2138_, v_p_2102_, v_p_x27_2103_, v_h_2104_, v_inst_2105_, v_arg_2123_);
v___x_2140_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2140_, 0, v_a_2134_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
lean_ctor_set_uint8(v___x_2140_, sizeof(void*)*2, v___x_2129_);
lean_ctor_set_uint8(v___x_2140_, sizeof(void*)*2 + 1, v___x_2129_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 0, v___x_2140_);
v___x_2142_ = v___x_2136_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_dec_ref(v_arg_2123_);
lean_dec_ref(v_inst_2105_);
lean_dec_ref(v_h_2104_);
lean_dec_ref(v_p_x27_2103_);
lean_dec_ref(v_p_2102_);
v_a_2145_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2133_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2133_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
}
else
{
lean_object* v___x_2153_; 
lean_dec_ref(v___x_2127_);
lean_dec_ref(v_fallback_2107_);
v___x_2153_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2111_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2165_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2156_ = v___x_2153_;
v_isShared_2157_ = v_isSharedCheck_2165_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2153_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2165_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; uint8_t v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2163_; 
v___x_2158_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5);
v___x_2159_ = l_Lean_mkApp5(v___x_2158_, v_p_2102_, v_p_x27_2103_, v_h_2104_, v_inst_2105_, v_arg_2123_);
v___x_2160_ = 0;
v___x_2161_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2161_, 0, v_a_2154_);
lean_ctor_set(v___x_2161_, 1, v___x_2159_);
lean_ctor_set_uint8(v___x_2161_, sizeof(void*)*2, v___x_2160_);
lean_ctor_set_uint8(v___x_2161_, sizeof(void*)*2 + 1, v___x_2160_);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v___x_2161_);
v___x_2163_ = v___x_2156_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2161_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
else
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
lean_dec_ref(v_arg_2123_);
lean_dec_ref(v_inst_2105_);
lean_dec_ref(v_h_2104_);
lean_dec_ref(v_p_x27_2103_);
lean_dec_ref(v_p_2102_);
v_a_2166_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2168_ = v___x_2153_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2153_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2169_ == 0)
{
v___x_2171_ = v___x_2168_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2166_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec_ref(v_fallback_2107_);
lean_dec_ref(v_inst_2105_);
lean_dec_ref(v_h_2104_);
lean_dec_ref(v_p_x27_2103_);
lean_dec_ref(v_p_2102_);
v_a_2174_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2118_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2118_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___boxed(lean_object* v_p_2182_, lean_object* v_p_x27_2183_, lean_object* v_h_2184_, lean_object* v_inst_2185_, lean_object* v_inst_x27_2186_, lean_object* v_fallback_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(v_p_2182_, v_p_x27_2183_, v_h_2184_, v_inst_2185_, v_inst_x27_2186_, v_fallback_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
lean_dec(v_a_2194_);
lean_dec_ref(v_a_2193_);
lean_dec(v_a_2192_);
lean_dec_ref(v_a_2191_);
lean_dec(v_a_2190_);
lean_dec_ref(v_a_2189_);
lean_dec(v_a_2188_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(lean_object* v_p_2199_, lean_object* v_inst_2200_, lean_object* v_fallback_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_){
_start:
{
lean_object* v___x_2212_; 
lean_inc(v_a_2210_);
lean_inc_ref(v_a_2209_);
lean_inc(v_a_2208_);
lean_inc_ref(v_a_2207_);
lean_inc(v_a_2206_);
lean_inc_ref(v_a_2205_);
lean_inc(v_a_2204_);
lean_inc_ref(v_a_2203_);
lean_inc(v_a_2202_);
lean_inc_ref(v_inst_2200_);
v___x_2212_ = lean_sym_simp(v_inst_2200_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_a_2213_);
lean_dec_ref_known(v___x_2212_, 1);
if (lean_obj_tag(v_a_2213_) == 0)
{
uint8_t v_contextDependent_2214_; lean_object* v___x_2215_; 
v_contextDependent_2214_ = lean_ctor_get_uint8(v_a_2213_, 1);
lean_dec_ref_known(v_a_2213_, 0);
lean_inc_ref(v_inst_2200_);
v___x_2215_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(v_p_2199_, v_inst_2200_, v_inst_2200_, v_fallback_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; uint8_t v___y_2218_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
if (v_contextDependent_2214_ == 0)
{
lean_dec(v_a_2216_);
return v___x_2215_;
}
else
{
if (lean_obj_tag(v_a_2216_) == 0)
{
uint8_t v_contextDependent_2228_; 
v_contextDependent_2228_ = lean_ctor_get_uint8(v_a_2216_, 1);
v___y_2218_ = v_contextDependent_2228_;
goto v___jp_2217_;
}
else
{
uint8_t v_contextDependent_2229_; 
v_contextDependent_2229_ = lean_ctor_get_uint8(v_a_2216_, sizeof(void*)*2 + 1);
v___y_2218_ = v_contextDependent_2229_;
goto v___jp_2217_;
}
}
v___jp_2217_:
{
if (v___y_2218_ == 0)
{
lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2226_; 
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2226_ == 0)
{
lean_object* v_unused_2227_; 
v_unused_2227_ = lean_ctor_get(v___x_2215_, 0);
lean_dec(v_unused_2227_);
v___x_2220_ = v___x_2215_;
v_isShared_2221_ = v_isSharedCheck_2226_;
goto v_resetjp_2219_;
}
else
{
lean_dec(v___x_2215_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2226_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2222_; lean_object* v___x_2224_; 
v___x_2222_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2216_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 0, v___x_2222_);
v___x_2224_ = v___x_2220_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
else
{
lean_dec(v_a_2216_);
return v___x_2215_;
}
}
}
else
{
return v___x_2215_;
}
}
else
{
lean_object* v_e_x27_2230_; uint8_t v_contextDependent_2231_; lean_object* v___x_2232_; 
v_e_x27_2230_ = lean_ctor_get(v_a_2213_, 0);
lean_inc_ref(v_e_x27_2230_);
v_contextDependent_2231_ = lean_ctor_get_uint8(v_a_2213_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2213_, 2);
v___x_2232_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(v_p_2199_, v_inst_2200_, v_e_x27_2230_, v_fallback_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; uint8_t v___y_2235_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
if (v_contextDependent_2231_ == 0)
{
lean_dec(v_a_2233_);
return v___x_2232_;
}
else
{
if (lean_obj_tag(v_a_2233_) == 0)
{
uint8_t v_contextDependent_2245_; 
v_contextDependent_2245_ = lean_ctor_get_uint8(v_a_2233_, 1);
v___y_2235_ = v_contextDependent_2245_;
goto v___jp_2234_;
}
else
{
uint8_t v_contextDependent_2246_; 
v_contextDependent_2246_ = lean_ctor_get_uint8(v_a_2233_, sizeof(void*)*2 + 1);
v___y_2235_ = v_contextDependent_2246_;
goto v___jp_2234_;
}
}
v___jp_2234_:
{
if (v___y_2235_ == 0)
{
lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2243_; 
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2243_ == 0)
{
lean_object* v_unused_2244_; 
v_unused_2244_ = lean_ctor_get(v___x_2232_, 0);
lean_dec(v_unused_2244_);
v___x_2237_ = v___x_2232_;
v_isShared_2238_ = v_isSharedCheck_2243_;
goto v_resetjp_2236_;
}
else
{
lean_dec(v___x_2232_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2243_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2239_; lean_object* v___x_2241_; 
v___x_2239_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2233_);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 0, v___x_2239_);
v___x_2241_ = v___x_2237_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2239_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
else
{
lean_dec(v_a_2233_);
return v___x_2232_;
}
}
}
else
{
return v___x_2232_;
}
}
}
else
{
lean_dec_ref(v_fallback_2201_);
lean_dec_ref(v_inst_2200_);
lean_dec_ref(v_p_2199_);
return v___x_2212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable___boxed(lean_object* v_p_2247_, lean_object* v_inst_2248_, lean_object* v_fallback_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(v_p_2247_, v_inst_2248_, v_fallback_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_);
lean_dec(v_a_2258_);
lean_dec_ref(v_a_2257_);
lean_dec(v_a_2256_);
lean_dec_ref(v_a_2255_);
lean_dec(v_a_2254_);
lean_dec_ref(v_a_2253_);
lean_dec(v_a_2252_);
lean_dec_ref(v_a_2251_);
lean_dec(v_a_2250_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr(lean_object* v_p_2261_, lean_object* v_p_x27_2262_, lean_object* v_h_2263_, lean_object* v_inst_2264_, lean_object* v_inst_x27_2265_, lean_object* v_fallback_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_){
_start:
{
lean_object* v___x_2277_; 
lean_inc(v_a_2275_);
lean_inc_ref(v_a_2274_);
lean_inc(v_a_2273_);
lean_inc_ref(v_a_2272_);
lean_inc(v_a_2271_);
lean_inc_ref(v_a_2270_);
lean_inc(v_a_2269_);
lean_inc_ref(v_a_2268_);
lean_inc(v_a_2267_);
lean_inc_ref(v_inst_x27_2265_);
v___x_2277_ = lean_sym_simp(v_inst_x27_2265_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_a_2278_; 
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_a_2278_);
lean_dec_ref_known(v___x_2277_, 1);
if (lean_obj_tag(v_a_2278_) == 0)
{
uint8_t v_contextDependent_2279_; lean_object* v___x_2280_; 
v_contextDependent_2279_ = lean_ctor_get_uint8(v_a_2278_, 1);
lean_dec_ref_known(v_a_2278_, 0);
v___x_2280_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(v_p_2261_, v_p_x27_2262_, v_h_2263_, v_inst_2264_, v_inst_x27_2265_, v_fallback_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; uint8_t v___y_2283_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_a_2281_);
if (v_contextDependent_2279_ == 0)
{
lean_dec(v_a_2281_);
return v___x_2280_;
}
else
{
if (lean_obj_tag(v_a_2281_) == 0)
{
uint8_t v_contextDependent_2293_; 
v_contextDependent_2293_ = lean_ctor_get_uint8(v_a_2281_, 1);
v___y_2283_ = v_contextDependent_2293_;
goto v___jp_2282_;
}
else
{
uint8_t v_contextDependent_2294_; 
v_contextDependent_2294_ = lean_ctor_get_uint8(v_a_2281_, sizeof(void*)*2 + 1);
v___y_2283_ = v_contextDependent_2294_;
goto v___jp_2282_;
}
}
v___jp_2282_:
{
if (v___y_2283_ == 0)
{
lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2291_; 
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2291_ == 0)
{
lean_object* v_unused_2292_; 
v_unused_2292_ = lean_ctor_get(v___x_2280_, 0);
lean_dec(v_unused_2292_);
v___x_2285_ = v___x_2280_;
v_isShared_2286_ = v_isSharedCheck_2291_;
goto v_resetjp_2284_;
}
else
{
lean_dec(v___x_2280_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2291_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2287_; lean_object* v___x_2289_; 
v___x_2287_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2281_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 0, v___x_2287_);
v___x_2289_ = v___x_2285_;
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
else
{
lean_dec(v_a_2281_);
return v___x_2280_;
}
}
}
else
{
return v___x_2280_;
}
}
else
{
lean_object* v_e_x27_2295_; uint8_t v_contextDependent_2296_; lean_object* v___x_2297_; 
lean_dec_ref(v_inst_x27_2265_);
v_e_x27_2295_ = lean_ctor_get(v_a_2278_, 0);
lean_inc_ref(v_e_x27_2295_);
v_contextDependent_2296_ = lean_ctor_get_uint8(v_a_2278_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2278_, 2);
v___x_2297_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(v_p_2261_, v_p_x27_2262_, v_h_2263_, v_inst_2264_, v_e_x27_2295_, v_fallback_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; uint8_t v___y_2300_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2298_);
if (v_contextDependent_2296_ == 0)
{
lean_dec(v_a_2298_);
return v___x_2297_;
}
else
{
if (lean_obj_tag(v_a_2298_) == 0)
{
uint8_t v_contextDependent_2310_; 
v_contextDependent_2310_ = lean_ctor_get_uint8(v_a_2298_, 1);
v___y_2300_ = v_contextDependent_2310_;
goto v___jp_2299_;
}
else
{
uint8_t v_contextDependent_2311_; 
v_contextDependent_2311_ = lean_ctor_get_uint8(v_a_2298_, sizeof(void*)*2 + 1);
v___y_2300_ = v_contextDependent_2311_;
goto v___jp_2299_;
}
}
v___jp_2299_:
{
if (v___y_2300_ == 0)
{
lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2308_; 
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2308_ == 0)
{
lean_object* v_unused_2309_; 
v_unused_2309_ = lean_ctor_get(v___x_2297_, 0);
lean_dec(v_unused_2309_);
v___x_2302_ = v___x_2297_;
v_isShared_2303_ = v_isSharedCheck_2308_;
goto v_resetjp_2301_;
}
else
{
lean_dec(v___x_2297_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2308_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2304_; lean_object* v___x_2306_; 
v___x_2304_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2298_);
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 0, v___x_2304_);
v___x_2306_ = v___x_2302_;
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
}
else
{
lean_dec(v_a_2298_);
return v___x_2297_;
}
}
}
else
{
return v___x_2297_;
}
}
}
else
{
lean_dec_ref(v_fallback_2266_);
lean_dec_ref(v_inst_x27_2265_);
lean_dec_ref(v_inst_2264_);
lean_dec_ref(v_h_2263_);
lean_dec_ref(v_p_x27_2262_);
lean_dec_ref(v_p_2261_);
return v___x_2277_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___boxed(lean_object* v_p_2312_, lean_object* v_p_x27_2313_, lean_object* v_h_2314_, lean_object* v_inst_2315_, lean_object* v_inst_x27_2316_, lean_object* v_fallback_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr(v_p_2312_, v_p_x27_2313_, v_h_2314_, v_inst_2315_, v_inst_x27_2316_, v_fallback_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_);
lean_dec(v_a_2326_);
lean_dec_ref(v_a_2325_);
lean_dec(v_a_2324_);
lean_dec_ref(v_a_2323_);
lean_dec(v_a_2322_);
lean_dec_ref(v_a_2321_);
lean_dec(v_a_2320_);
lean_dec_ref(v_a_2319_);
lean_dec(v_a_2318_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1(lean_object* v___x_2330_, lean_object* v_e_x27_2331_, lean_object* v___y_2332_, lean_object* v___x_2333_, lean_object* v___x_2334_, lean_object* v___x_2335_, lean_object* v_arg_2336_, lean_object* v_proof_2337_, lean_object* v_arg_2338_, uint8_t v___x_2339_, uint8_t v_contextDependent_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v___x_2351_; 
v___x_2351_ = l_Lean_Meta_Sym_shareCommon(v___x_2330_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; lean_object* v___x_2353_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_a_2352_);
lean_dec_ref_known(v___x_2351_, 1);
lean_inc_ref(v___y_2332_);
lean_inc_ref(v_e_x27_2331_);
v___x_2353_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1(v_a_2352_, v_e_x27_2331_, v___y_2332_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2366_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2356_ = v___x_2353_;
v_isShared_2357_ = v_isSharedCheck_2366_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2353_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2366_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2364_; 
v___x_2358_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1___closed__0));
v___x_2359_ = l_Lean_Name_mkStr3(v___x_2333_, v___x_2334_, v___x_2358_);
v___x_2360_ = l_Lean_mkConst(v___x_2359_, v___x_2335_);
v___x_2361_ = l_Lean_mkApp5(v___x_2360_, v_arg_2336_, v_e_x27_2331_, v_proof_2337_, v_arg_2338_, v___y_2332_);
v___x_2362_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2362_, 0, v_a_2354_);
lean_ctor_set(v___x_2362_, 1, v___x_2361_);
lean_ctor_set_uint8(v___x_2362_, sizeof(void*)*2, v___x_2339_);
lean_ctor_set_uint8(v___x_2362_, sizeof(void*)*2 + 1, v_contextDependent_2340_);
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 0, v___x_2362_);
v___x_2364_ = v___x_2356_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
lean_dec_ref(v_arg_2338_);
lean_dec_ref(v_proof_2337_);
lean_dec_ref(v_arg_2336_);
lean_dec(v___x_2335_);
lean_dec_ref(v___x_2334_);
lean_dec_ref(v___x_2333_);
lean_dec_ref(v___y_2332_);
lean_dec_ref(v_e_x27_2331_);
v_a_2367_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2353_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2353_);
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
else
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
lean_dec_ref(v_arg_2338_);
lean_dec_ref(v_proof_2337_);
lean_dec_ref(v_arg_2336_);
lean_dec(v___x_2335_);
lean_dec_ref(v___x_2334_);
lean_dec_ref(v___x_2333_);
lean_dec_ref(v___y_2332_);
lean_dec_ref(v_e_x27_2331_);
v_a_2375_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___x_2351_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2351_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1___boxed(lean_object** _args){
lean_object* v___x_2383_ = _args[0];
lean_object* v_e_x27_2384_ = _args[1];
lean_object* v___y_2385_ = _args[2];
lean_object* v___x_2386_ = _args[3];
lean_object* v___x_2387_ = _args[4];
lean_object* v___x_2388_ = _args[5];
lean_object* v_arg_2389_ = _args[6];
lean_object* v_proof_2390_ = _args[7];
lean_object* v_arg_2391_ = _args[8];
lean_object* v___x_2392_ = _args[9];
lean_object* v_contextDependent_2393_ = _args[10];
lean_object* v___y_2394_ = _args[11];
lean_object* v___y_2395_ = _args[12];
lean_object* v___y_2396_ = _args[13];
lean_object* v___y_2397_ = _args[14];
lean_object* v___y_2398_ = _args[15];
lean_object* v___y_2399_ = _args[16];
lean_object* v___y_2400_ = _args[17];
lean_object* v___y_2401_ = _args[18];
lean_object* v___y_2402_ = _args[19];
lean_object* v___y_2403_ = _args[20];
_start:
{
uint8_t v___x_23749__boxed_2404_; uint8_t v_contextDependent_23750__boxed_2405_; lean_object* v_res_2406_; 
v___x_23749__boxed_2404_ = lean_unbox(v___x_2392_);
v_contextDependent_23750__boxed_2405_ = lean_unbox(v_contextDependent_2393_);
v_res_2406_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1(v___x_2383_, v_e_x27_2384_, v___y_2385_, v___x_2386_, v___x_2387_, v___x_2388_, v_arg_2389_, v_proof_2390_, v_arg_2391_, v___x_23749__boxed_2404_, v_contextDependent_23750__boxed_2405_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
return v_res_2406_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2414_ = lean_box(0);
v___x_2415_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__3));
v___x_2416_ = l_Lean_mkConst(v___x_2415_, v___x_2414_);
return v___x_2416_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2420_ = lean_box(0);
v___x_2421_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__6));
v___x_2422_ = l_Lean_mkConst(v___x_2421_, v___x_2420_);
return v___x_2422_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8(void){
_start:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2423_ = lean_box(0);
v___x_2424_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1));
v___x_2425_ = l_Lean_mkConst(v___x_2424_, v___x_2423_);
return v___x_2425_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11(void){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2431_ = lean_box(0);
v___x_2432_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10));
v___x_2433_ = l_Lean_mkConst(v___x_2432_, v___x_2431_);
return v___x_2433_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__14(void){
_start:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2439_ = lean_box(0);
v___x_2440_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__13));
v___x_2441_ = l_Lean_mkConst(v___x_2440_, v___x_2439_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0(uint8_t v___x_2442_, lean_object* v_e_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v___x_2457_; uint8_t v___x_2458_; 
v___x_2457_ = l_Lean_Expr_cleanupAnnotations(v_e_2443_);
v___x_2458_ = l_Lean_Expr_isApp(v___x_2457_);
if (v___x_2458_ == 0)
{
lean_dec_ref(v___x_2457_);
goto v___jp_2454_;
}
else
{
lean_object* v_arg_2459_; lean_object* v___x_2460_; uint8_t v___x_2461_; 
v_arg_2459_ = lean_ctor_get(v___x_2457_, 1);
lean_inc_ref(v_arg_2459_);
v___x_2460_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2457_);
v___x_2461_ = l_Lean_Expr_isApp(v___x_2460_);
if (v___x_2461_ == 0)
{
lean_dec_ref(v___x_2460_);
lean_dec_ref(v_arg_2459_);
goto v___jp_2454_;
}
else
{
lean_object* v_arg_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; 
v_arg_2462_ = lean_ctor_get(v___x_2460_, 1);
lean_inc_ref(v_arg_2462_);
v___x_2463_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2460_);
v___x_2464_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__0));
v___x_2465_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__0));
v___x_2466_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1));
v___x_2467_ = l_Lean_Expr_isConstOf(v___x_2463_, v___x_2466_);
lean_dec_ref(v___x_2463_);
if (v___x_2467_ == 0)
{
lean_dec_ref(v_arg_2462_);
lean_dec_ref(v_arg_2459_);
goto v___jp_2454_;
}
else
{
lean_object* v___x_2468_; 
lean_inc(v___y_2452_);
lean_inc_ref(v___y_2451_);
lean_inc(v___y_2450_);
lean_inc_ref(v___y_2449_);
lean_inc(v___y_2448_);
lean_inc_ref(v___y_2447_);
lean_inc(v___y_2446_);
lean_inc_ref(v___y_2445_);
lean_inc(v___y_2444_);
lean_inc_ref(v_arg_2462_);
v___x_2468_ = lean_sym_simp(v_arg_2462_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_a_2469_);
lean_dec_ref_known(v___x_2468_, 1);
if (lean_obj_tag(v_a_2469_) == 0)
{
uint8_t v_contextDependent_2470_; lean_object* v___x_2471_; 
v_contextDependent_2470_ = lean_ctor_get_uint8(v_a_2469_, 1);
lean_dec_ref_known(v_a_2469_, 0);
v___x_2471_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_2462_, v___y_2447_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; uint8_t v___x_2473_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2472_);
lean_dec_ref_known(v___x_2471_, 1);
v___x_2473_ = lean_unbox(v_a_2472_);
if (v___x_2473_ == 0)
{
lean_object* v___x_2474_; 
v___x_2474_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_2462_, v___y_2447_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; uint8_t v___x_2476_; 
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_a_2475_);
lean_dec_ref_known(v___x_2474_, 1);
v___x_2476_ = lean_unbox(v_a_2475_);
lean_dec(v_a_2475_);
if (v___x_2476_ == 0)
{
lean_object* v___x_2477_; lean_object* v___f_2478_; lean_object* v___x_2479_; 
lean_dec(v_a_2472_);
v___x_2477_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_2467_, v_contextDependent_2470_);
v___f_2478_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2478_, 0, v___x_2477_);
v___x_2479_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(v_arg_2462_, v_arg_2459_, v___f_2478_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
return v___x_2479_;
}
else
{
lean_object* v___x_2480_; 
lean_dec_ref(v_arg_2462_);
v___x_2480_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v___y_2447_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2492_; 
v_a_2481_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2483_ = v___x_2480_;
v_isShared_2484_ = v_isSharedCheck_2492_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2480_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2492_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; uint8_t v___x_2488_; lean_object* v___x_2490_; 
v___x_2485_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__4, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__4);
v___x_2486_ = l_Lean_Expr_app___override(v___x_2485_, v_arg_2459_);
v___x_2487_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2487_, 0, v_a_2481_);
lean_ctor_set(v___x_2487_, 1, v___x_2486_);
v___x_2488_ = lean_unbox(v_a_2472_);
lean_dec(v_a_2472_);
lean_ctor_set_uint8(v___x_2487_, sizeof(void*)*2, v___x_2488_);
lean_ctor_set_uint8(v___x_2487_, sizeof(void*)*2 + 1, v_contextDependent_2470_);
if (v_isShared_2484_ == 0)
{
lean_ctor_set(v___x_2483_, 0, v___x_2487_);
v___x_2490_ = v___x_2483_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2487_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
else
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
lean_dec(v_a_2472_);
lean_dec_ref(v_arg_2459_);
v_a_2493_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___x_2480_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2480_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
}
}
else
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2508_; 
lean_dec(v_a_2472_);
lean_dec_ref(v_arg_2462_);
lean_dec_ref(v_arg_2459_);
v_a_2501_ = lean_ctor_get(v___x_2474_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2503_ = v___x_2474_;
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2474_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2506_; 
if (v_isShared_2504_ == 0)
{
v___x_2506_ = v___x_2503_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2501_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
else
{
lean_object* v___x_2509_; 
lean_dec(v_a_2472_);
lean_dec_ref(v_arg_2462_);
v___x_2509_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v___y_2447_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2520_; 
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2512_ = v___x_2509_;
v_isShared_2513_ = v_isSharedCheck_2520_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2509_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2520_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2514_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7);
v___x_2515_ = l_Lean_Expr_app___override(v___x_2514_, v_arg_2459_);
v___x_2516_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2516_, 0, v_a_2510_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
lean_ctor_set_uint8(v___x_2516_, sizeof(void*)*2, v___x_2442_);
lean_ctor_set_uint8(v___x_2516_, sizeof(void*)*2 + 1, v_contextDependent_2470_);
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 0, v___x_2516_);
v___x_2518_ = v___x_2512_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
lean_dec_ref(v_arg_2459_);
v_a_2521_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v___x_2509_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2509_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2521_);
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
}
else
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2536_; 
lean_dec_ref(v_arg_2462_);
lean_dec_ref(v_arg_2459_);
v_a_2529_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2531_ = v___x_2471_;
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2471_);
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
else
{
lean_object* v_e_x27_2537_; lean_object* v_proof_2538_; uint8_t v_contextDependent_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2631_; 
v_e_x27_2537_ = lean_ctor_get(v_a_2469_, 0);
v_proof_2538_ = lean_ctor_get(v_a_2469_, 1);
v_contextDependent_2539_ = lean_ctor_get_uint8(v_a_2469_, sizeof(void*)*2 + 1);
v_isSharedCheck_2631_ = !lean_is_exclusive(v_a_2469_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2541_ = v_a_2469_;
v_isShared_2542_ = v_isSharedCheck_2631_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_proof_2538_);
lean_inc(v_e_x27_2537_);
lean_dec(v_a_2469_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2631_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2543_; 
v___x_2543_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_2537_, v___y_2447_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; uint8_t v___x_2545_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2544_);
lean_dec_ref_known(v___x_2543_, 1);
v___x_2545_ = lean_unbox(v_a_2544_);
if (v___x_2545_ == 0)
{
lean_object* v___x_2546_; 
v___x_2546_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_2537_, v___y_2447_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; uint8_t v___x_2548_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2547_);
lean_dec_ref_known(v___x_2546_, 1);
v___x_2548_ = lean_unbox(v_a_2547_);
lean_dec(v_a_2547_);
if (v___x_2548_ == 0)
{
lean_object* v___x_2549_; 
lean_dec(v_a_2544_);
lean_del_object(v___x_2541_);
lean_inc_ref(v_e_x27_2537_);
v___x_2549_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance(v_e_x27_2537_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; lean_object* v___y_2552_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_a_2550_);
lean_dec_ref_known(v___x_2549_, 1);
if (lean_obj_tag(v_a_2550_) == 0)
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2559_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6);
lean_inc_ref(v_proof_2538_);
lean_inc_ref(v_arg_2459_);
lean_inc_ref(v_e_x27_2537_);
lean_inc_ref(v_arg_2462_);
v___x_2560_ = l_Lean_mkApp4(v___x_2559_, v_arg_2462_, v_e_x27_2537_, v_arg_2459_, v_proof_2538_);
v___y_2552_ = v___x_2560_;
goto v___jp_2551_;
}
else
{
lean_object* v_val_2561_; 
v_val_2561_ = lean_ctor_get(v_a_2550_, 0);
lean_inc(v_val_2561_);
lean_dec_ref_known(v_a_2550_, 1);
v___y_2552_ = v_val_2561_;
goto v___jp_2551_;
}
v___jp_2551_:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___f_2557_; lean_object* v___x_2558_; 
v___x_2553_ = lean_box(0);
v___x_2554_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8);
v___x_2555_ = lean_box(v___x_2467_);
v___x_2556_ = lean_box(v_contextDependent_2539_);
lean_inc_ref(v_arg_2459_);
lean_inc_ref(v_proof_2538_);
lean_inc_ref(v_arg_2462_);
lean_inc_ref(v___y_2552_);
lean_inc_ref(v_e_x27_2537_);
v___f_2557_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1___boxed), 21, 11);
lean_closure_set(v___f_2557_, 0, v___x_2554_);
lean_closure_set(v___f_2557_, 1, v_e_x27_2537_);
lean_closure_set(v___f_2557_, 2, v___y_2552_);
lean_closure_set(v___f_2557_, 3, v___x_2464_);
lean_closure_set(v___f_2557_, 4, v___x_2465_);
lean_closure_set(v___f_2557_, 5, v___x_2553_);
lean_closure_set(v___f_2557_, 6, v_arg_2462_);
lean_closure_set(v___f_2557_, 7, v_proof_2538_);
lean_closure_set(v___f_2557_, 8, v_arg_2459_);
lean_closure_set(v___f_2557_, 9, v___x_2555_);
lean_closure_set(v___f_2557_, 10, v___x_2556_);
v___x_2558_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr(v_arg_2462_, v_e_x27_2537_, v_proof_2538_, v_arg_2459_, v___y_2552_, v___f_2557_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
return v___x_2558_;
}
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2569_; 
lean_dec_ref(v_proof_2538_);
lean_dec_ref(v_e_x27_2537_);
lean_dec_ref(v_arg_2462_);
lean_dec_ref(v_arg_2459_);
v_a_2562_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2564_ = v___x_2549_;
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2549_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2562_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
else
{
lean_object* v___x_2570_; 
lean_dec_ref(v_e_x27_2537_);
v___x_2570_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v___y_2447_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2584_; 
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2573_ = v___x_2570_;
v_isShared_2574_ = v_isSharedCheck_2584_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2570_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2584_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2578_; 
v___x_2575_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11);
v___x_2576_ = l_Lean_mkApp3(v___x_2575_, v_arg_2462_, v_arg_2459_, v_proof_2538_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 1, v___x_2576_);
lean_ctor_set(v___x_2541_, 0, v_a_2571_);
v___x_2578_ = v___x_2541_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2571_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
uint8_t v___x_2579_; lean_object* v___x_2581_; 
v___x_2579_ = lean_unbox(v_a_2544_);
lean_dec(v_a_2544_);
lean_ctor_set_uint8(v___x_2578_, sizeof(void*)*2, v___x_2579_);
lean_ctor_set_uint8(v___x_2578_, sizeof(void*)*2 + 1, v_contextDependent_2539_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 0, v___x_2578_);
v___x_2581_ = v___x_2573_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2578_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
lean_dec(v_a_2544_);
lean_del_object(v___x_2541_);
lean_dec_ref(v_proof_2538_);
lean_dec_ref(v_arg_2462_);
lean_dec_ref(v_arg_2459_);
v_a_2585_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2570_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2570_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
}
else
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
lean_dec(v_a_2544_);
lean_del_object(v___x_2541_);
lean_dec_ref(v_proof_2538_);
lean_dec_ref(v_e_x27_2537_);
lean_dec_ref(v_arg_2462_);
lean_dec_ref(v_arg_2459_);
v_a_2593_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2595_ = v___x_2546_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2546_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2596_ == 0)
{
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
else
{
lean_object* v___x_2601_; 
lean_dec(v_a_2544_);
lean_dec_ref(v_e_x27_2537_);
v___x_2601_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v___y_2447_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2614_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2604_ = v___x_2601_;
v_isShared_2605_ = v_isSharedCheck_2614_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2601_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2614_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2609_; 
v___x_2606_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__14, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__14_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__14);
v___x_2607_ = l_Lean_mkApp3(v___x_2606_, v_arg_2462_, v_arg_2459_, v_proof_2538_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 1, v___x_2607_);
lean_ctor_set(v___x_2541_, 0, v_a_2602_);
v___x_2609_ = v___x_2541_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2602_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v___x_2607_);
lean_ctor_set_uint8(v_reuseFailAlloc_2613_, sizeof(void*)*2 + 1, v_contextDependent_2539_);
v___x_2609_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
lean_object* v___x_2611_; 
lean_ctor_set_uint8(v___x_2609_, sizeof(void*)*2, v___x_2442_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 0, v___x_2609_);
v___x_2611_ = v___x_2604_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2609_);
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
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_del_object(v___x_2541_);
lean_dec_ref(v_proof_2538_);
lean_dec_ref(v_arg_2462_);
lean_dec_ref(v_arg_2459_);
v_a_2615_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2601_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2601_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
}
else
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
lean_del_object(v___x_2541_);
lean_dec_ref(v_proof_2538_);
lean_dec_ref(v_e_x27_2537_);
lean_dec_ref(v_arg_2462_);
lean_dec_ref(v_arg_2459_);
v_a_2623_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___x_2543_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2543_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_arg_2462_);
lean_dec_ref(v_arg_2459_);
return v___x_2468_;
}
}
}
}
v___jp_2454_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2455_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2455_, 0, v___x_2442_);
lean_ctor_set_uint8(v___x_2455_, 1, v___x_2442_);
v___x_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2455_);
return v___x_2456_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___boxed(lean_object* v___x_2632_, lean_object* v_e_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
uint8_t v___x_23949__boxed_2644_; lean_object* v_res_2645_; 
v___x_23949__boxed_2644_ = lean_unbox(v___x_2632_);
v_res_2645_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0(v___x_23949__boxed_2644_, v_e_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv(lean_object* v_e_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v_numArgs_2657_; lean_object* v___x_2658_; uint8_t v___x_2659_; 
v_numArgs_2657_ = l_Lean_Expr_getAppNumArgs(v_e_2646_);
v___x_2658_ = lean_unsigned_to_nat(2u);
v___x_2659_ = lean_nat_dec_lt(v_numArgs_2657_, v___x_2658_);
if (v___x_2659_ == 0)
{
lean_object* v___x_2660_; lean_object* v___f_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2660_ = lean_box(v___x_2659_);
v___f_2661_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___boxed), 12, 1);
lean_closure_set(v___f_2661_, 0, v___x_2660_);
v___x_2662_ = lean_nat_sub(v_numArgs_2657_, v___x_2658_);
lean_dec(v_numArgs_2657_);
v___x_2663_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_2646_, v___x_2662_, v___f_2661_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
lean_dec(v___x_2662_);
return v___x_2663_;
}
else
{
uint8_t v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
lean_dec(v_numArgs_2657_);
lean_dec_ref(v_e_2646_);
v___x_2664_ = 0;
v___x_2665_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2665_, 0, v___x_2659_);
lean_ctor_set_uint8(v___x_2665_, 1, v___x_2664_);
v___x_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2665_);
return v___x_2666_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___boxed(lean_object* v_e_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv(v_e_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_);
lean_dec(v_a_2676_);
lean_dec_ref(v_a_2675_);
lean_dec(v_a_2674_);
lean_dec_ref(v_a_2673_);
lean_dec(v_a_2672_);
lean_dec_ref(v_a_2671_);
lean_dec(v_a_2670_);
lean_dec_ref(v_a_2669_);
lean_dec(v_a_2668_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2694_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_14_));
v___x_2695_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_14_));
v___x_2696_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___boxed), 11, 0);
v___x_2697_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_2694_, v___x_2695_, v___x_2696_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_14____boxed(lean_object* v_a_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_14_();
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_2701_; uint8_t v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2701_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_14_));
v___x_2702_ = 0;
v___x_2703_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___boxed), 11, 0);
v___x_2704_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_2701_, v___x_2702_, v___x_2703_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_16____boxed(lean_object* v_a_2705_){
_start:
{
lean_object* v_res_2706_; 
v_res_2706_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_16_();
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0(lean_object* v_customCanUnfoldPredicate_x3f_2707_, uint8_t v_canUnfoldPredicateConfig_2708_, lean_object* v_cfg_2709_, lean_object* v_info_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2714_ = l_Lean_ConstantInfo_name(v_info_2710_);
v___x_2715_ = l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(v___x_2714_, v___y_2712_);
lean_dec(v___x_2714_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2730_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2718_ = v___x_2715_;
v_isShared_2719_ = v_isSharedCheck_2730_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2715_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2730_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
uint8_t v___x_2720_; 
v___x_2720_ = lean_unbox(v_a_2716_);
lean_dec(v_a_2716_);
if (v___x_2720_ == 0)
{
lean_del_object(v___x_2718_);
if (lean_obj_tag(v_customCanUnfoldPredicate_x3f_2707_) == 0)
{
if (v_canUnfoldPredicateConfig_2708_ == 0)
{
lean_object* v___x_2721_; 
v___x_2721_ = l_Lean_Meta_canUnfoldDefault(v_cfg_2709_, v_info_2710_, v___y_2711_, v___y_2712_);
lean_dec_ref(v_info_2710_);
lean_dec_ref(v_cfg_2709_);
return v___x_2721_;
}
else
{
lean_object* v___x_2722_; 
v___x_2722_ = l_Lean_Meta_canUnfoldAtMatcher(v_cfg_2709_, v_info_2710_, v___y_2711_, v___y_2712_);
lean_dec_ref(v_info_2710_);
lean_dec_ref(v_cfg_2709_);
return v___x_2722_;
}
}
else
{
lean_object* v_val_2723_; lean_object* v___x_2724_; 
v_val_2723_ = lean_ctor_get(v_customCanUnfoldPredicate_x3f_2707_, 0);
lean_inc(v_val_2723_);
lean_dec_ref_known(v_customCanUnfoldPredicate_x3f_2707_, 1);
lean_inc(v___y_2712_);
lean_inc_ref(v___y_2711_);
v___x_2724_ = lean_apply_5(v_val_2723_, v_cfg_2709_, v_info_2710_, v___y_2711_, v___y_2712_, lean_box(0));
return v___x_2724_;
}
}
else
{
uint8_t v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2728_; 
lean_dec_ref(v_info_2710_);
lean_dec_ref(v_cfg_2709_);
lean_dec(v_customCanUnfoldPredicate_x3f_2707_);
v___x_2725_ = 0;
v___x_2726_ = lean_box(v___x_2725_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v___x_2726_);
v___x_2728_ = v___x_2718_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2726_);
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
lean_dec_ref(v_info_2710_);
lean_dec_ref(v_cfg_2709_);
lean_dec(v_customCanUnfoldPredicate_x3f_2707_);
return v___x_2715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0___boxed(lean_object* v_customCanUnfoldPredicate_x3f_2731_, lean_object* v_canUnfoldPredicateConfig_2732_, lean_object* v_cfg_2733_, lean_object* v_info_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
uint8_t v_canUnfoldPredicateConfig_boxed_2738_; lean_object* v_res_2739_; 
v_canUnfoldPredicateConfig_boxed_2738_ = lean_unbox(v_canUnfoldPredicateConfig_2732_);
v_res_2739_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0(v_customCanUnfoldPredicate_x3f_2731_, v_canUnfoldPredicateConfig_boxed_2738_, v_cfg_2733_, v_info_2734_, v___y_2735_, v___y_2736_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(lean_object* v_x_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_){
_start:
{
lean_object* v_keyedConfig_2746_; uint8_t v_trackZetaDelta_2747_; lean_object* v_zetaDeltaSet_2748_; lean_object* v_lctx_2749_; lean_object* v_localInstances_2750_; lean_object* v_defEqCtx_x3f_2751_; lean_object* v_synthPendingDepth_2752_; lean_object* v_customCanUnfoldPredicate_x3f_2753_; uint8_t v_univApprox_2754_; uint8_t v_inTypeClassResolution_2755_; uint8_t v_cacheInferType_2756_; lean_object* v___x_2757_; uint8_t v_canUnfoldPredicateConfig_2758_; lean_object* v___x_2759_; lean_object* v___f_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v_keyedConfig_2746_ = lean_ctor_get(v_a_2741_, 0);
v_trackZetaDelta_2747_ = lean_ctor_get_uint8(v_a_2741_, sizeof(void*)*7);
v_zetaDeltaSet_2748_ = lean_ctor_get(v_a_2741_, 1);
v_lctx_2749_ = lean_ctor_get(v_a_2741_, 2);
v_localInstances_2750_ = lean_ctor_get(v_a_2741_, 3);
v_defEqCtx_x3f_2751_ = lean_ctor_get(v_a_2741_, 4);
v_synthPendingDepth_2752_ = lean_ctor_get(v_a_2741_, 5);
v_customCanUnfoldPredicate_x3f_2753_ = lean_ctor_get(v_a_2741_, 6);
v_univApprox_2754_ = lean_ctor_get_uint8(v_a_2741_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2755_ = lean_ctor_get_uint8(v_a_2741_, sizeof(void*)*7 + 2);
v_cacheInferType_2756_ = lean_ctor_get_uint8(v_a_2741_, sizeof(void*)*7 + 3);
v___x_2757_ = l_Lean_Meta_Context_config(v_a_2741_);
v_canUnfoldPredicateConfig_2758_ = lean_ctor_get_uint8(v___x_2757_, 19);
lean_dec_ref(v___x_2757_);
v___x_2759_ = lean_box(v_canUnfoldPredicateConfig_2758_);
lean_inc(v_customCanUnfoldPredicate_x3f_2753_);
v___f_2760_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2760_, 0, v_customCanUnfoldPredicate_x3f_2753_);
lean_closure_set(v___f_2760_, 1, v___x_2759_);
v___x_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2761_, 0, v___f_2760_);
lean_inc(v_synthPendingDepth_2752_);
lean_inc(v_defEqCtx_x3f_2751_);
lean_inc_ref(v_localInstances_2750_);
lean_inc_ref(v_lctx_2749_);
lean_inc(v_zetaDeltaSet_2748_);
lean_inc_ref(v_keyedConfig_2746_);
v___x_2762_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2762_, 0, v_keyedConfig_2746_);
lean_ctor_set(v___x_2762_, 1, v_zetaDeltaSet_2748_);
lean_ctor_set(v___x_2762_, 2, v_lctx_2749_);
lean_ctor_set(v___x_2762_, 3, v_localInstances_2750_);
lean_ctor_set(v___x_2762_, 4, v_defEqCtx_x3f_2751_);
lean_ctor_set(v___x_2762_, 5, v_synthPendingDepth_2752_);
lean_ctor_set(v___x_2762_, 6, v___x_2761_);
lean_ctor_set_uint8(v___x_2762_, sizeof(void*)*7, v_trackZetaDelta_2747_);
lean_ctor_set_uint8(v___x_2762_, sizeof(void*)*7 + 1, v_univApprox_2754_);
lean_ctor_set_uint8(v___x_2762_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2755_);
lean_ctor_set_uint8(v___x_2762_, sizeof(void*)*7 + 3, v_cacheInferType_2756_);
lean_inc(v_a_2744_);
lean_inc_ref(v_a_2743_);
lean_inc(v_a_2742_);
v___x_2763_ = lean_apply_5(v_x_2740_, v___x_2762_, v_a_2742_, v_a_2743_, v_a_2744_, lean_box(0));
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___boxed(lean_object* v_x_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v_x_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_);
lean_dec(v_a_2768_);
lean_dec_ref(v_a_2767_);
lean_dec(v_a_2766_);
lean_dec_ref(v_a_2765_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard(lean_object* v_00_u03b1_2771_, lean_object* v_x_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_){
_start:
{
lean_object* v___x_2778_; 
v___x_2778_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v_x_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___boxed(lean_object* v_00_u03b1_2779_, lean_object* v_x_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard(v_00_u03b1_2779_, v_x_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_);
lean_dec(v_a_2784_);
lean_dec_ref(v_a_2783_);
lean_dec(v_a_2782_);
lean_dec_ref(v_a_2781_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond(lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_){
_start:
{
lean_object* v___x_2798_; 
v___x_2798_ = l_Lean_Meta_Sym_Simp_simpCond(v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___boxed(lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond(v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
lean_dec(v_a_2808_);
lean_dec_ref(v_a_2807_);
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2805_);
lean_dec(v_a_2804_);
lean_dec_ref(v_a_2803_);
lean_dec(v_a_2802_);
lean_dec_ref(v_a_2801_);
lean_dec(v_a_2800_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_(){
_start:
{
lean_object* v___f_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___f_2837_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_));
v___x_2838_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_));
v___x_2839_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_));
v___x_2840_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_2838_, v___x_2839_, v___f_2837_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16____boxed(lean_object* v_a_2841_){
_start:
{
lean_object* v_res_2842_; 
v_res_2842_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_();
return v_res_2842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_18_(){
_start:
{
lean_object* v___f_2844_; lean_object* v___x_2845_; uint8_t v___x_2846_; lean_object* v___x_2847_; 
v___f_2844_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_));
v___x_2845_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_));
v___x_2846_ = 0;
v___x_2847_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_2845_, v___x_2846_, v___f_2844_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_18____boxed(lean_object* v_a_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_18_();
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0(lean_object* v_msgData_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_){
_start:
{
lean_object* v___x_2856_; lean_object* v_env_2857_; lean_object* v___x_2858_; lean_object* v_mctx_2859_; lean_object* v_lctx_2860_; lean_object* v_options_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2856_ = lean_st_ref_get(v___y_2854_);
v_env_2857_ = lean_ctor_get(v___x_2856_, 0);
lean_inc_ref(v_env_2857_);
lean_dec(v___x_2856_);
v___x_2858_ = lean_st_ref_get(v___y_2852_);
v_mctx_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc_ref(v_mctx_2859_);
lean_dec(v___x_2858_);
v_lctx_2860_ = lean_ctor_get(v___y_2851_, 2);
v_options_2861_ = lean_ctor_get(v___y_2853_, 2);
lean_inc_ref(v_options_2861_);
lean_inc_ref(v_lctx_2860_);
v___x_2862_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2862_, 0, v_env_2857_);
lean_ctor_set(v___x_2862_, 1, v_mctx_2859_);
lean_ctor_set(v___x_2862_, 2, v_lctx_2860_);
lean_ctor_set(v___x_2862_, 3, v_options_2861_);
v___x_2863_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2862_);
lean_ctor_set(v___x_2863_, 1, v_msgData_2850_);
v___x_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2863_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0___boxed(lean_object* v_msgData_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0(v_msgData_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
return v_res_2871_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2872_; double v___x_2873_; 
v___x_2872_ = lean_unsigned_to_nat(0u);
v___x_2873_ = lean_float_of_nat(v___x_2872_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(lean_object* v_cls_2877_, lean_object* v_msg_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_){
_start:
{
lean_object* v_ref_2884_; lean_object* v___x_2885_; lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2930_; 
v_ref_2884_ = lean_ctor_get(v___y_2881_, 5);
v___x_2885_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0(v_msg_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2888_ = v___x_2885_;
v_isShared_2889_ = v_isSharedCheck_2930_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2885_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2930_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2890_; lean_object* v_traceState_2891_; lean_object* v_env_2892_; lean_object* v_nextMacroScope_2893_; lean_object* v_ngen_2894_; lean_object* v_auxDeclNGen_2895_; lean_object* v_cache_2896_; lean_object* v_messages_2897_; lean_object* v_infoState_2898_; lean_object* v_snapshotTasks_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2929_; 
v___x_2890_ = lean_st_ref_take(v___y_2882_);
v_traceState_2891_ = lean_ctor_get(v___x_2890_, 4);
v_env_2892_ = lean_ctor_get(v___x_2890_, 0);
v_nextMacroScope_2893_ = lean_ctor_get(v___x_2890_, 1);
v_ngen_2894_ = lean_ctor_get(v___x_2890_, 2);
v_auxDeclNGen_2895_ = lean_ctor_get(v___x_2890_, 3);
v_cache_2896_ = lean_ctor_get(v___x_2890_, 5);
v_messages_2897_ = lean_ctor_get(v___x_2890_, 6);
v_infoState_2898_ = lean_ctor_get(v___x_2890_, 7);
v_snapshotTasks_2899_ = lean_ctor_get(v___x_2890_, 8);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2901_ = v___x_2890_;
v_isShared_2902_ = v_isSharedCheck_2929_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_snapshotTasks_2899_);
lean_inc(v_infoState_2898_);
lean_inc(v_messages_2897_);
lean_inc(v_cache_2896_);
lean_inc(v_traceState_2891_);
lean_inc(v_auxDeclNGen_2895_);
lean_inc(v_ngen_2894_);
lean_inc(v_nextMacroScope_2893_);
lean_inc(v_env_2892_);
lean_dec(v___x_2890_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2929_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
uint64_t v_tid_2903_; lean_object* v_traces_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2928_; 
v_tid_2903_ = lean_ctor_get_uint64(v_traceState_2891_, sizeof(void*)*1);
v_traces_2904_ = lean_ctor_get(v_traceState_2891_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v_traceState_2891_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2906_ = v_traceState_2891_;
v_isShared_2907_ = v_isSharedCheck_2928_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_traces_2904_);
lean_dec(v_traceState_2891_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2928_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2908_; double v___x_2909_; uint8_t v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2918_; 
v___x_2908_ = lean_box(0);
v___x_2909_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0);
v___x_2910_ = 0;
v___x_2911_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__1));
v___x_2912_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2912_, 0, v_cls_2877_);
lean_ctor_set(v___x_2912_, 1, v___x_2908_);
lean_ctor_set(v___x_2912_, 2, v___x_2911_);
lean_ctor_set_float(v___x_2912_, sizeof(void*)*3, v___x_2909_);
lean_ctor_set_float(v___x_2912_, sizeof(void*)*3 + 8, v___x_2909_);
lean_ctor_set_uint8(v___x_2912_, sizeof(void*)*3 + 16, v___x_2910_);
v___x_2913_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__2));
v___x_2914_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2912_);
lean_ctor_set(v___x_2914_, 1, v_a_2886_);
lean_ctor_set(v___x_2914_, 2, v___x_2913_);
lean_inc(v_ref_2884_);
v___x_2915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2915_, 0, v_ref_2884_);
lean_ctor_set(v___x_2915_, 1, v___x_2914_);
v___x_2916_ = l_Lean_PersistentArray_push___redArg(v_traces_2904_, v___x_2915_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 0, v___x_2916_);
v___x_2918_ = v___x_2906_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v___x_2916_);
lean_ctor_set_uint64(v_reuseFailAlloc_2927_, sizeof(void*)*1, v_tid_2903_);
v___x_2918_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
lean_object* v___x_2920_; 
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 4, v___x_2918_);
v___x_2920_ = v___x_2901_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_env_2892_);
lean_ctor_set(v_reuseFailAlloc_2926_, 1, v_nextMacroScope_2893_);
lean_ctor_set(v_reuseFailAlloc_2926_, 2, v_ngen_2894_);
lean_ctor_set(v_reuseFailAlloc_2926_, 3, v_auxDeclNGen_2895_);
lean_ctor_set(v_reuseFailAlloc_2926_, 4, v___x_2918_);
lean_ctor_set(v_reuseFailAlloc_2926_, 5, v_cache_2896_);
lean_ctor_set(v_reuseFailAlloc_2926_, 6, v_messages_2897_);
lean_ctor_set(v_reuseFailAlloc_2926_, 7, v_infoState_2898_);
lean_ctor_set(v_reuseFailAlloc_2926_, 8, v_snapshotTasks_2899_);
v___x_2920_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2924_; 
v___x_2921_ = lean_st_ref_set(v___y_2882_, v___x_2920_);
v___x_2922_ = lean_box(0);
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 0, v___x_2922_);
v___x_2924_ = v___x_2888_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2922_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___boxed(lean_object* v_cls_2931_, lean_object* v_msg_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v_cls_2931_, v_msg_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
return v_res_2938_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5(void){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2949_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2));
v___x_2950_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__4));
v___x_2951_ = l_Lean_Name_append(v___x_2950_, v___x_2949_);
return v___x_2951_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7(void){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__6));
v___x_2954_ = l_Lean_stringToMessageData(v___x_2953_);
return v___x_2954_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9(void){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2956_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__8));
v___x_2957_ = l_Lean_stringToMessageData(v___x_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(lean_object* v_e_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_){
_start:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; 
lean_inc_ref(v_e_2960_);
v___x_2971_ = lean_alloc_closure((void*)(l_Lean_Meta_reduceRecMatcher_x3f___boxed), 6, 1);
lean_closure_set(v___x_2971_, 0, v_e_2960_);
v___x_2972_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___x_2971_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_3030_; 
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_2975_ = v___x_2972_;
v_isShared_2976_ = v_isSharedCheck_3030_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2972_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_3030_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
if (lean_obj_tag(v_a_2973_) == 1)
{
lean_object* v_val_2977_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v_options_3004_; uint8_t v_hasTrace_3005_; 
lean_del_object(v___x_2975_);
v_val_2977_ = lean_ctor_get(v_a_2973_, 0);
lean_inc(v_val_2977_);
lean_dec_ref_known(v_a_2973_, 1);
v_options_3004_ = lean_ctor_get(v_a_2968_, 2);
v_hasTrace_3005_ = lean_ctor_get_uint8(v_options_3004_, sizeof(void*)*1);
if (v_hasTrace_3005_ == 0)
{
lean_dec_ref(v_e_2960_);
v___y_2979_ = v_a_2964_;
v___y_2980_ = v_a_2965_;
v___y_2981_ = v_a_2966_;
v___y_2982_ = v_a_2967_;
v___y_2983_ = v_a_2968_;
v___y_2984_ = v_a_2969_;
goto v___jp_2978_;
}
else
{
lean_object* v_inheritedTraceOptions_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; 
v_inheritedTraceOptions_3006_ = lean_ctor_get(v_a_2968_, 13);
v___x_3007_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2));
v___x_3008_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5, &l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5);
v___x_3009_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3006_, v_options_3004_, v___x_3008_);
if (v___x_3009_ == 0)
{
lean_dec_ref(v_e_2960_);
v___y_2979_ = v_a_2964_;
v___y_2980_ = v_a_2965_;
v___y_2981_ = v_a_2966_;
v___y_2982_ = v_a_2967_;
v___y_2983_ = v_a_2968_;
v___y_2984_ = v_a_2969_;
goto v___jp_2978_;
}
else
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3010_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7, &l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7);
v___x_3011_ = l_Lean_indentExpr(v_e_2960_);
v___x_3012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3010_);
lean_ctor_set(v___x_3012_, 1, v___x_3011_);
v___x_3013_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9, &l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9_once, _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9);
v___x_3014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3012_);
lean_ctor_set(v___x_3014_, 1, v___x_3013_);
lean_inc(v_val_2977_);
v___x_3015_ = l_Lean_indentExpr(v_val_2977_);
v___x_3016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3014_);
lean_ctor_set(v___x_3016_, 1, v___x_3015_);
v___x_3017_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v___x_3007_, v___x_3016_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_dec_ref_known(v___x_3017_, 1);
v___y_2979_ = v_a_2964_;
v___y_2980_ = v_a_2965_;
v___y_2981_ = v_a_2966_;
v___y_2982_ = v_a_2967_;
v___y_2983_ = v_a_2968_;
v___y_2984_ = v_a_2969_;
goto v___jp_2978_;
}
else
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
lean_dec(v_val_2977_);
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_3017_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3017_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
}
v___jp_2978_:
{
lean_object* v___x_2985_; 
lean_inc(v_val_2977_);
v___x_2985_ = l_Lean_Meta_Sym_mkEqRefl(v_val_2977_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2995_; 
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2988_ = v___x_2985_;
v_isShared_2989_ = v_isSharedCheck_2995_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2985_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2995_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
uint8_t v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2993_; 
v___x_2990_ = 0;
v___x_2991_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2991_, 0, v_val_2977_);
lean_ctor_set(v___x_2991_, 1, v_a_2986_);
lean_ctor_set_uint8(v___x_2991_, sizeof(void*)*2, v___x_2990_);
lean_ctor_set_uint8(v___x_2991_, sizeof(void*)*2 + 1, v___x_2990_);
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 0, v___x_2991_);
v___x_2993_ = v___x_2988_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v___x_2991_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
else
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
lean_dec(v_val_2977_);
v_a_2996_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v___x_2985_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2985_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2996_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
}
else
{
lean_object* v___x_3026_; lean_object* v___x_3028_; 
lean_dec(v_a_2973_);
lean_dec_ref(v_e_2960_);
v___x_3026_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__10));
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 0, v___x_3026_);
v___x_3028_ = v___x_2975_;
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
}
}
else
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
lean_dec_ref(v_e_2960_);
v_a_3031_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___x_2972_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_2972_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3034_ == 0)
{
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3031_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___boxed(lean_object* v_e_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_e_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_);
lean_dec(v_a_3048_);
lean_dec_ref(v_a_3047_);
lean_dec(v_a_3046_);
lean_dec_ref(v_a_3045_);
lean_dec(v_a_3044_);
lean_dec_ref(v_a_3043_);
lean_dec(v_a_3042_);
lean_dec_ref(v_a_3041_);
lean_dec(v_a_3040_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0(lean_object* v_cls_3051_, lean_object* v_msg_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
lean_object* v___x_3063_; 
v___x_3063_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v_cls_3051_, v_msg_3052_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___boxed(lean_object* v_cls_3064_, lean_object* v_msg_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
lean_object* v_res_3076_; 
v_res_3076_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0(v_cls_3064_, v_msg_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
return v_res_3076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec(lean_object* v_x_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_){
_start:
{
uint8_t v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3102_ = 0;
v___x_3103_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___closed__0));
lean_inc_ref(v_x_3091_);
v___x_3104_ = l_Lean_Meta_Sym_Simp_simpInterlaced(v_x_3091_, v___x_3103_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc(v_a_3105_);
if (lean_obj_tag(v_a_3105_) == 0)
{
uint8_t v_done_3106_; 
v_done_3106_ = lean_ctor_get_uint8(v_a_3105_, 0);
if (v_done_3106_ == 0)
{
lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3119_; 
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3119_ == 0)
{
lean_object* v_unused_3120_; 
v_unused_3120_ = lean_ctor_get(v___x_3104_, 0);
lean_dec(v_unused_3120_);
v___x_3108_ = v___x_3104_;
v_isShared_3109_ = v_isSharedCheck_3119_;
goto v_resetjp_3107_;
}
else
{
lean_dec(v___x_3104_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3119_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
uint8_t v_contextDependent_3110_; lean_object* v___x_3111_; 
v_contextDependent_3110_ = lean_ctor_get_uint8(v_a_3105_, 1);
lean_dec_ref_known(v_a_3105_, 0);
v___x_3111_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_x_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v_a_3112_; uint8_t v___y_3114_; 
v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
lean_inc(v_a_3112_);
if (v_contextDependent_3110_ == 0)
{
lean_dec(v_a_3112_);
lean_del_object(v___x_3108_);
return v___x_3111_;
}
else
{
lean_dec_ref_known(v___x_3111_, 1);
v___y_3114_ = v___x_3102_;
goto v___jp_3113_;
}
v___jp_3113_:
{
lean_object* v___x_3115_; lean_object* v___x_3117_; 
v___x_3115_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3112_);
if (v_isShared_3109_ == 0)
{
lean_ctor_set(v___x_3108_, 0, v___x_3115_);
v___x_3117_ = v___x_3108_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v___x_3115_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
else
{
lean_del_object(v___x_3108_);
return v___x_3111_;
}
}
}
else
{
lean_dec_ref_known(v_a_3105_, 0);
lean_dec_ref(v_x_3091_);
return v___x_3104_;
}
}
else
{
uint8_t v_done_3121_; 
v_done_3121_ = lean_ctor_get_uint8(v_a_3105_, sizeof(void*)*2);
if (v_done_3121_ == 0)
{
lean_object* v_e_x27_3122_; lean_object* v_proof_3123_; uint8_t v_contextDependent_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3170_; 
lean_dec_ref_known(v___x_3104_, 1);
v_e_x27_3122_ = lean_ctor_get(v_a_3105_, 0);
v_proof_3123_ = lean_ctor_get(v_a_3105_, 1);
v_contextDependent_3124_ = lean_ctor_get_uint8(v_a_3105_, sizeof(void*)*2 + 1);
v_isSharedCheck_3170_ = !lean_is_exclusive(v_a_3105_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3126_ = v_a_3105_;
v_isShared_3127_ = v_isSharedCheck_3170_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_proof_3123_);
lean_inc(v_e_x27_3122_);
lean_dec(v_a_3105_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3170_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3128_; 
lean_inc_ref(v_e_x27_3122_);
v___x_3128_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_e_x27_3122_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3169_; 
v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3131_ = v___x_3128_;
v_isShared_3132_ = v_isSharedCheck_3169_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3128_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3169_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
if (lean_obj_tag(v_a_3129_) == 0)
{
uint8_t v___y_3134_; 
lean_dec_ref_known(v_a_3129_, 0);
lean_dec_ref(v_x_3091_);
if (v_contextDependent_3124_ == 0)
{
v___y_3134_ = v___x_3102_;
goto v___jp_3133_;
}
else
{
v___y_3134_ = v_contextDependent_3124_;
goto v___jp_3133_;
}
v___jp_3133_:
{
lean_object* v___x_3136_; 
if (v_isShared_3127_ == 0)
{
v___x_3136_ = v___x_3126_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_e_x27_3122_);
lean_ctor_set(v_reuseFailAlloc_3140_, 1, v_proof_3123_);
v___x_3136_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
lean_object* v___x_3138_; 
lean_ctor_set_uint8(v___x_3136_, sizeof(void*)*2, v___x_3102_);
lean_ctor_set_uint8(v___x_3136_, sizeof(void*)*2 + 1, v___y_3134_);
if (v_isShared_3132_ == 0)
{
lean_ctor_set(v___x_3131_, 0, v___x_3136_);
v___x_3138_ = v___x_3131_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v___x_3136_);
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
else
{
lean_object* v_e_x27_3141_; lean_object* v_proof_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3168_; 
lean_del_object(v___x_3131_);
lean_del_object(v___x_3126_);
v_e_x27_3141_ = lean_ctor_get(v_a_3129_, 0);
v_proof_3142_ = lean_ctor_get(v_a_3129_, 1);
v_isSharedCheck_3168_ = !lean_is_exclusive(v_a_3129_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3144_ = v_a_3129_;
v_isShared_3145_ = v_isSharedCheck_3168_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_proof_3142_);
lean_inc(v_e_x27_3141_);
lean_dec(v_a_3129_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3168_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3146_; 
lean_inc_ref(v_e_x27_3141_);
v___x_3146_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_x_3091_, v_e_x27_3122_, v_proof_3123_, v_e_x27_3141_, v_proof_3142_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3159_; 
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3149_ = v___x_3146_;
v_isShared_3150_ = v_isSharedCheck_3159_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3146_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3159_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
uint8_t v___y_3152_; 
if (v_contextDependent_3124_ == 0)
{
v___y_3152_ = v___x_3102_;
goto v___jp_3151_;
}
else
{
v___y_3152_ = v_contextDependent_3124_;
goto v___jp_3151_;
}
v___jp_3151_:
{
lean_object* v___x_3154_; 
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 1, v_a_3147_);
v___x_3154_ = v___x_3144_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_e_x27_3141_);
lean_ctor_set(v_reuseFailAlloc_3158_, 1, v_a_3147_);
v___x_3154_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
lean_object* v___x_3156_; 
lean_ctor_set_uint8(v___x_3154_, sizeof(void*)*2, v___x_3102_);
lean_ctor_set_uint8(v___x_3154_, sizeof(void*)*2 + 1, v___y_3152_);
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 0, v___x_3154_);
v___x_3156_ = v___x_3149_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v___x_3154_);
v___x_3156_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
return v___x_3156_;
}
}
}
}
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_del_object(v___x_3144_);
lean_dec_ref(v_e_x27_3141_);
v_a_3160_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3146_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3146_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_3126_);
lean_dec_ref(v_proof_3123_);
lean_dec_ref(v_e_x27_3122_);
lean_dec_ref(v_x_3091_);
return v___x_3128_;
}
}
}
else
{
lean_dec_ref_known(v_a_3105_, 2);
lean_dec_ref(v_x_3091_);
return v___x_3104_;
}
}
}
else
{
lean_dec_ref(v_x_3091_);
return v___x_3104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___boxed(lean_object* v_x_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec(v_x_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_);
lean_dec(v_a_3180_);
lean_dec_ref(v_a_3179_);
lean_dec(v_a_3178_);
lean_dec_ref(v_a_3177_);
lean_dec(v_a_3176_);
lean_dec_ref(v_a_3175_);
lean_dec(v_a_3174_);
lean_dec_ref(v_a_3173_);
lean_dec(v_a_3172_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3205_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18_));
v___x_3206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18_));
v___x_3207_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___boxed), 11, 0);
v___x_3208_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_3205_, v___x_3206_, v___x_3207_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18____boxed(lean_object* v_a_3209_){
_start:
{
lean_object* v_res_3210_; 
v_res_3210_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18_();
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_20_(){
_start:
{
lean_object* v___x_3212_; uint8_t v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3212_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18_));
v___x_3213_ = 0;
v___x_3214_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___boxed), 11, 0);
v___x_3215_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_3212_, v___x_3213_, v___x_3214_);
return v___x_3215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_20____boxed(lean_object* v_a_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_20_();
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(lean_object* v_appFn_3219_, lean_object* v_e_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_){
_start:
{
lean_object* v___x_3231_; 
v___x_3231_ = l_Lean_Meta_Tactic_Cbv_getMatchTheorems(v_appFn_3219_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
lean_inc(v_a_3232_);
lean_dec_ref_known(v___x_3231_, 1);
v___x_3233_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0));
v___x_3234_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_3232_, v___x_3233_, v_e_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_);
lean_dec(v_a_3232_);
return v___x_3234_;
}
else
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3242_; 
lean_dec_ref(v_e_3220_);
v_a_3235_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3237_ = v___x_3231_;
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3231_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3240_; 
if (v_isShared_3238_ == 0)
{
v___x_3240_ = v___x_3237_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3235_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___boxed(lean_object* v_appFn_3243_, lean_object* v_e_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(v_appFn_3243_, v_e_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_);
lean_dec(v_a_3253_);
lean_dec_ref(v_a_3252_);
lean_dec(v_a_3251_);
lean_dec_ref(v_a_3250_);
lean_dec(v_a_3249_);
lean_dec_ref(v_a_3248_);
lean_dec(v_a_3247_);
lean_dec_ref(v_a_3246_);
lean_dec(v_a_3245_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(lean_object* v_declName_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v___x_3259_; lean_object* v_env_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3259_ = lean_st_ref_get(v___y_3257_);
v_env_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc_ref(v_env_3260_);
lean_dec(v___x_3259_);
v___x_3261_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_3260_, v_declName_3256_);
v___x_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3261_);
return v___x_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg___boxed(lean_object* v_declName_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
lean_object* v_res_3266_; 
v_res_3266_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(v_declName_3263_, v___y_3264_);
lean_dec(v___y_3264_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0(lean_object* v_declName_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
lean_object* v___x_3278_; 
v___x_3278_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(v_declName_3267_, v___y_3276_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___boxed(lean_object* v_declName_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0(v_declName_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
return v_res_3290_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2(void){
_start:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3297_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1));
v___x_3298_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__4));
v___x_3299_ = l_Lean_Name_append(v___x_3298_, v___x_3297_);
return v___x_3299_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4(void){
_start:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3301_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__3));
v___x_3302_ = l_Lean_stringToMessageData(v___x_3301_);
return v___x_3302_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6(void){
_start:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3304_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__5));
v___x_3305_ = l_Lean_stringToMessageData(v___x_3304_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher(lean_object* v_e_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_){
_start:
{
uint8_t v___x_3317_; 
v___x_3317_ = l_Lean_Expr_isApp(v_e_3306_);
if (v___x_3317_ == 0)
{
lean_object* v___x_3318_; lean_object* v___x_3319_; 
lean_dec_ref(v_e_3306_);
v___x_3318_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3318_, 0, v___x_3317_);
lean_ctor_set_uint8(v___x_3318_, 1, v___x_3317_);
v___x_3319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3318_);
return v___x_3319_;
}
else
{
lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3320_ = l_Lean_Expr_getAppFn(v_e_3306_);
v___x_3321_ = l_Lean_Expr_constName_x3f(v___x_3320_);
lean_dec_ref(v___x_3320_);
if (lean_obj_tag(v___x_3321_) == 1)
{
lean_object* v_val_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3469_; 
v_val_3322_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3324_ = v___x_3321_;
v_isShared_3325_ = v_isSharedCheck_3469_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_val_3322_);
lean_dec(v___x_3321_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3469_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v_a_3327_; lean_object* v_e_x27_3328_; lean_object* v___y_3370_; lean_object* v_a_3371_; lean_object* v___y_3374_; lean_object* v___y_3377_; lean_object* v___y_3378_; uint8_t v___y_3379_; lean_object* v___y_3383_; lean_object* v_a_3384_; lean_object* v___y_3392_; lean_object* v___x_3394_; lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3468_; 
lean_inc(v_val_3322_);
v___x_3394_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(v_val_3322_, v_a_3315_);
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3397_ = v___x_3394_;
v_isShared_3398_ = v_isSharedCheck_3468_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3394_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3468_;
goto v_resetjp_3396_;
}
v___jp_3326_:
{
lean_object* v_options_3329_; uint8_t v_hasTrace_3330_; 
v_options_3329_ = lean_ctor_get(v_a_3314_, 2);
v_hasTrace_3330_ = lean_ctor_get_uint8(v_options_3329_, sizeof(void*)*1);
if (v_hasTrace_3330_ == 0)
{
lean_object* v___x_3332_; 
lean_dec_ref(v_e_x27_3328_);
lean_dec(v_val_3322_);
lean_dec_ref(v_e_3306_);
if (v_isShared_3325_ == 0)
{
lean_ctor_set_tag(v___x_3324_, 0);
lean_ctor_set(v___x_3324_, 0, v_a_3327_);
v___x_3332_ = v___x_3324_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3327_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; uint8_t v___x_3337_; 
v_inheritedTraceOptions_3334_ = lean_ctor_get(v_a_3314_, 13);
v___x_3335_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1));
v___x_3336_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2, &l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2);
v___x_3337_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3334_, v_options_3329_, v___x_3336_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3339_; 
lean_dec_ref(v_e_x27_3328_);
lean_dec(v_val_3322_);
lean_dec_ref(v_e_3306_);
if (v_isShared_3325_ == 0)
{
lean_ctor_set_tag(v___x_3324_, 0);
lean_ctor_set(v___x_3324_, 0, v_a_3327_);
v___x_3339_ = v___x_3324_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_a_3327_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
else
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
lean_del_object(v___x_3324_);
v___x_3341_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4, &l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4_once, _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4);
v___x_3342_ = l_Lean_MessageData_ofName(v_val_3322_);
v___x_3343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3341_);
lean_ctor_set(v___x_3343_, 1, v___x_3342_);
v___x_3344_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6, &l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6);
v___x_3345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3343_);
lean_ctor_set(v___x_3345_, 1, v___x_3344_);
v___x_3346_ = l_Lean_indentExpr(v_e_3306_);
v___x_3347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3345_);
lean_ctor_set(v___x_3347_, 1, v___x_3346_);
v___x_3348_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9, &l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9_once, _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9);
v___x_3349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3347_);
lean_ctor_set(v___x_3349_, 1, v___x_3348_);
v___x_3350_ = l_Lean_indentExpr(v_e_x27_3328_);
v___x_3351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3349_);
lean_ctor_set(v___x_3351_, 1, v___x_3350_);
v___x_3352_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v___x_3335_, v___x_3351_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3359_; 
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3359_ == 0)
{
lean_object* v_unused_3360_; 
v_unused_3360_ = lean_ctor_get(v___x_3352_, 0);
lean_dec(v_unused_3360_);
v___x_3354_ = v___x_3352_;
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
else
{
lean_dec(v___x_3352_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3357_; 
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 0, v_a_3327_);
v___x_3357_ = v___x_3354_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_a_3327_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
else
{
lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3368_; 
lean_dec_ref(v_a_3327_);
v_a_3361_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3363_ = v___x_3352_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3352_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3366_; 
if (v_isShared_3364_ == 0)
{
v___x_3366_ = v___x_3363_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3361_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
}
}
}
v___jp_3369_:
{
if (lean_obj_tag(v_a_3371_) == 1)
{
lean_object* v_e_x27_3372_; 
lean_dec_ref(v___y_3370_);
v_e_x27_3372_ = lean_ctor_get(v_a_3371_, 0);
lean_inc_ref(v_e_x27_3372_);
v_a_3327_ = v_a_3371_;
v_e_x27_3328_ = v_e_x27_3372_;
goto v___jp_3326_;
}
else
{
lean_dec_ref(v_a_3371_);
lean_del_object(v___x_3324_);
lean_dec(v_val_3322_);
lean_dec_ref(v_e_3306_);
return v___y_3370_;
}
}
v___jp_3373_:
{
if (lean_obj_tag(v___y_3374_) == 0)
{
lean_object* v_a_3375_; 
v_a_3375_ = lean_ctor_get(v___y_3374_, 0);
lean_inc(v_a_3375_);
v___y_3370_ = v___y_3374_;
v_a_3371_ = v_a_3375_;
goto v___jp_3369_;
}
else
{
lean_del_object(v___x_3324_);
lean_dec(v_val_3322_);
lean_dec_ref(v_e_3306_);
return v___y_3374_;
}
}
v___jp_3376_:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; 
lean_dec_ref(v___y_3378_);
v___x_3380_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3377_);
lean_inc_ref(v___x_3380_);
v___x_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3380_);
v___y_3370_ = v___x_3381_;
v_a_3371_ = v___x_3380_;
goto v___jp_3369_;
}
v___jp_3382_:
{
if (lean_obj_tag(v_a_3384_) == 0)
{
uint8_t v_done_3385_; 
v_done_3385_ = lean_ctor_get_uint8(v_a_3384_, 0);
if (v_done_3385_ == 0)
{
uint8_t v_contextDependent_3386_; lean_object* v___x_3387_; 
lean_dec_ref(v___y_3383_);
v_contextDependent_3386_ = lean_ctor_get_uint8(v_a_3384_, 1);
lean_dec_ref_known(v_a_3384_, 0);
lean_inc_ref(v_e_3306_);
v___x_3387_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_e_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_);
if (lean_obj_tag(v___x_3387_) == 0)
{
if (v_contextDependent_3386_ == 0)
{
v___y_3374_ = v___x_3387_;
goto v___jp_3373_;
}
else
{
lean_object* v_a_3388_; uint8_t v___x_3389_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_a_3388_);
v___x_3389_ = 0;
v___y_3377_ = v_a_3388_;
v___y_3378_ = v___x_3387_;
v___y_3379_ = v___x_3389_;
goto v___jp_3376_;
}
}
else
{
v___y_3374_ = v___x_3387_;
goto v___jp_3373_;
}
}
else
{
lean_dec_ref_known(v_a_3384_, 0);
lean_del_object(v___x_3324_);
lean_dec(v_val_3322_);
lean_dec_ref(v_e_3306_);
return v___y_3383_;
}
}
else
{
lean_object* v_e_x27_3390_; 
lean_dec_ref(v___y_3383_);
v_e_x27_3390_ = lean_ctor_get(v_a_3384_, 0);
lean_inc_ref(v_e_x27_3390_);
v_a_3327_ = v_a_3384_;
v_e_x27_3328_ = v_e_x27_3390_;
goto v___jp_3326_;
}
}
v___jp_3391_:
{
if (lean_obj_tag(v___y_3392_) == 0)
{
lean_object* v_a_3393_; 
v_a_3393_ = lean_ctor_get(v___y_3392_, 0);
lean_inc(v_a_3393_);
v___y_3383_ = v___y_3392_;
v_a_3384_ = v_a_3393_;
goto v___jp_3382_;
}
else
{
lean_del_object(v___x_3324_);
lean_dec(v_val_3322_);
lean_dec_ref(v_e_3306_);
return v___y_3392_;
}
}
v_resetjp_3396_:
{
if (lean_obj_tag(v_a_3395_) == 1)
{
lean_object* v_val_3399_; lean_object* v_numParams_3400_; lean_object* v_numDiscrs_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
lean_del_object(v___x_3397_);
v_val_3399_ = lean_ctor_get(v_a_3395_, 0);
lean_inc(v_val_3399_);
lean_dec_ref_known(v_a_3395_, 1);
v_numParams_3400_ = lean_ctor_get(v_val_3399_, 0);
lean_inc(v_numParams_3400_);
v_numDiscrs_3401_ = lean_ctor_get(v_val_3399_, 1);
lean_inc(v_numDiscrs_3401_);
lean_dec(v_val_3399_);
v___x_3402_ = lean_unsigned_to_nat(1u);
v___x_3403_ = lean_nat_add(v_numParams_3400_, v___x_3402_);
lean_dec(v_numParams_3400_);
v___x_3404_ = lean_nat_add(v___x_3403_, v_numDiscrs_3401_);
lean_dec(v_numDiscrs_3401_);
lean_inc_ref(v_e_3306_);
v___x_3405_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_e_3306_, v___x_3403_, v___x_3404_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_);
lean_dec(v___x_3404_);
lean_dec(v___x_3403_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
if (lean_obj_tag(v_a_3406_) == 0)
{
uint8_t v_done_3407_; 
v_done_3407_ = lean_ctor_get_uint8(v_a_3406_, 0);
if (v_done_3407_ == 0)
{
uint8_t v_contextDependent_3408_; lean_object* v___x_3409_; 
lean_dec_ref_known(v___x_3405_, 1);
v_contextDependent_3408_ = lean_ctor_get_uint8(v_a_3406_, 1);
lean_dec_ref_known(v_a_3406_, 0);
lean_inc_ref(v_e_3306_);
lean_inc(v_val_3322_);
v___x_3409_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(v_val_3322_, v_e_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v_a_3410_; uint8_t v___y_3412_; 
v_a_3410_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_a_3410_);
if (v_contextDependent_3408_ == 0)
{
lean_dec(v_a_3410_);
v___y_3392_ = v___x_3409_;
goto v___jp_3391_;
}
else
{
if (lean_obj_tag(v_a_3410_) == 0)
{
uint8_t v_contextDependent_3422_; 
v_contextDependent_3422_ = lean_ctor_get_uint8(v_a_3410_, 1);
v___y_3412_ = v_contextDependent_3422_;
goto v___jp_3411_;
}
else
{
uint8_t v_contextDependent_3423_; 
v_contextDependent_3423_ = lean_ctor_get_uint8(v_a_3410_, sizeof(void*)*2 + 1);
v___y_3412_ = v_contextDependent_3423_;
goto v___jp_3411_;
}
}
v___jp_3411_:
{
if (v___y_3412_ == 0)
{
lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3420_; 
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3420_ == 0)
{
lean_object* v_unused_3421_; 
v_unused_3421_ = lean_ctor_get(v___x_3409_, 0);
lean_dec(v_unused_3421_);
v___x_3414_ = v___x_3409_;
v_isShared_3415_ = v_isSharedCheck_3420_;
goto v_resetjp_3413_;
}
else
{
lean_dec(v___x_3409_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3420_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3416_; lean_object* v___x_3418_; 
v___x_3416_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3410_);
lean_inc_ref(v___x_3416_);
if (v_isShared_3415_ == 0)
{
lean_ctor_set(v___x_3414_, 0, v___x_3416_);
v___x_3418_ = v___x_3414_;
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
v___y_3383_ = v___x_3418_;
v_a_3384_ = v___x_3416_;
goto v___jp_3382_;
}
}
}
else
{
lean_dec(v_a_3410_);
v___y_3392_ = v___x_3409_;
goto v___jp_3391_;
}
}
}
else
{
v___y_3392_ = v___x_3409_;
goto v___jp_3391_;
}
}
else
{
lean_dec_ref_known(v_a_3406_, 0);
v___y_3392_ = v___x_3405_;
goto v___jp_3391_;
}
}
else
{
uint8_t v_done_3424_; 
v_done_3424_ = lean_ctor_get_uint8(v_a_3406_, sizeof(void*)*2);
if (v_done_3424_ == 0)
{
lean_object* v_e_x27_3425_; lean_object* v_proof_3426_; uint8_t v_contextDependent_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3463_; 
lean_dec_ref_known(v___x_3405_, 1);
v_e_x27_3425_ = lean_ctor_get(v_a_3406_, 0);
v_proof_3426_ = lean_ctor_get(v_a_3406_, 1);
v_contextDependent_3427_ = lean_ctor_get_uint8(v_a_3406_, sizeof(void*)*2 + 1);
v_isSharedCheck_3463_ = !lean_is_exclusive(v_a_3406_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3429_ = v_a_3406_;
v_isShared_3430_ = v_isSharedCheck_3463_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_proof_3426_);
lean_inc(v_e_x27_3425_);
lean_dec(v_a_3406_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3463_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3431_; 
lean_inc_ref(v_e_x27_3425_);
lean_inc(v_val_3322_);
v___x_3431_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(v_val_3322_, v_e_x27_3425_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3432_);
lean_dec_ref_known(v___x_3431_, 1);
if (lean_obj_tag(v_a_3432_) == 0)
{
uint8_t v_done_3433_; uint8_t v_contextDependent_3434_; uint8_t v___y_3436_; 
v_done_3433_ = lean_ctor_get_uint8(v_a_3432_, 0);
v_contextDependent_3434_ = lean_ctor_get_uint8(v_a_3432_, 1);
lean_dec_ref_known(v_a_3432_, 0);
if (v_contextDependent_3427_ == 0)
{
v___y_3436_ = v_contextDependent_3434_;
goto v___jp_3435_;
}
else
{
v___y_3436_ = v_contextDependent_3427_;
goto v___jp_3435_;
}
v___jp_3435_:
{
lean_object* v___x_3438_; 
lean_inc_ref(v_e_x27_3425_);
if (v_isShared_3430_ == 0)
{
v___x_3438_ = v___x_3429_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_e_x27_3425_);
lean_ctor_set(v_reuseFailAlloc_3439_, 1, v_proof_3426_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
lean_ctor_set_uint8(v___x_3438_, sizeof(void*)*2, v_done_3433_);
lean_ctor_set_uint8(v___x_3438_, sizeof(void*)*2 + 1, v___y_3436_);
v_a_3327_ = v___x_3438_;
v_e_x27_3328_ = v_e_x27_3425_;
goto v___jp_3326_;
}
}
}
else
{
lean_object* v_e_x27_3440_; lean_object* v_proof_3441_; uint8_t v_done_3442_; uint8_t v_contextDependent_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3462_; 
lean_del_object(v___x_3429_);
v_e_x27_3440_ = lean_ctor_get(v_a_3432_, 0);
v_proof_3441_ = lean_ctor_get(v_a_3432_, 1);
v_done_3442_ = lean_ctor_get_uint8(v_a_3432_, sizeof(void*)*2);
v_contextDependent_3443_ = lean_ctor_get_uint8(v_a_3432_, sizeof(void*)*2 + 1);
v_isSharedCheck_3462_ = !lean_is_exclusive(v_a_3432_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3445_ = v_a_3432_;
v_isShared_3446_ = v_isSharedCheck_3462_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_proof_3441_);
lean_inc(v_e_x27_3440_);
lean_dec(v_a_3432_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3462_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3447_; 
lean_inc_ref(v_e_x27_3440_);
lean_inc_ref(v_e_3306_);
v___x_3447_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_3306_, v_e_x27_3425_, v_proof_3426_, v_e_x27_3440_, v_proof_3441_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v_a_3448_; uint8_t v___y_3450_; 
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
lean_inc(v_a_3448_);
lean_dec_ref_known(v___x_3447_, 1);
if (v_contextDependent_3427_ == 0)
{
v___y_3450_ = v_contextDependent_3443_;
goto v___jp_3449_;
}
else
{
v___y_3450_ = v_contextDependent_3427_;
goto v___jp_3449_;
}
v___jp_3449_:
{
lean_object* v___x_3452_; 
lean_inc_ref(v_e_x27_3440_);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 1, v_a_3448_);
v___x_3452_ = v___x_3445_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_e_x27_3440_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v_a_3448_);
lean_ctor_set_uint8(v_reuseFailAlloc_3453_, sizeof(void*)*2, v_done_3442_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
lean_ctor_set_uint8(v___x_3452_, sizeof(void*)*2 + 1, v___y_3450_);
v_a_3327_ = v___x_3452_;
v_e_x27_3328_ = v_e_x27_3440_;
goto v___jp_3326_;
}
}
}
else
{
lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3461_; 
lean_del_object(v___x_3445_);
lean_dec_ref(v_e_x27_3440_);
lean_del_object(v___x_3324_);
lean_dec(v_val_3322_);
lean_dec_ref(v_e_3306_);
v_a_3454_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3456_ = v___x_3447_;
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v___x_3447_);
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
else
{
lean_del_object(v___x_3429_);
lean_dec_ref(v_proof_3426_);
lean_dec_ref(v_e_x27_3425_);
v___y_3392_ = v___x_3431_;
goto v___jp_3391_;
}
}
}
else
{
lean_dec_ref_known(v_a_3406_, 2);
v___y_3392_ = v___x_3405_;
goto v___jp_3391_;
}
}
}
else
{
v___y_3392_ = v___x_3405_;
goto v___jp_3391_;
}
}
else
{
lean_object* v___x_3464_; lean_object* v___x_3466_; 
lean_dec(v_a_3395_);
lean_del_object(v___x_3324_);
lean_dec(v_val_3322_);
lean_dec_ref(v_e_3306_);
v___x_3464_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__10));
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 0, v___x_3464_);
v___x_3466_ = v___x_3397_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3464_);
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
else
{
lean_object* v___x_3470_; lean_object* v___x_3471_; 
lean_dec(v___x_3321_);
lean_dec_ref(v_e_3306_);
v___x_3470_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__10));
v___x_3471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
return v___x_3471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher___boxed(lean_object* v_e_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_){
_start:
{
lean_object* v_res_3483_; 
v_res_3483_ = l_Lean_Meta_Tactic_Cbv_tryMatcher(v_e_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_);
lean_dec(v_a_3481_);
lean_dec_ref(v_a_3480_);
lean_dec(v_a_3479_);
lean_dec_ref(v_a_3478_);
lean_dec(v_a_3477_);
lean_dec_ref(v_a_3476_);
lean_dec(v_a_3475_);
lean_dec_ref(v_a_3474_);
lean_dec(v_a_3473_);
return v_res_3483_;
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
lean_object* runtime_initialize_Lean_Compiler_ComputableExt(uint8_t builtin);
lean_object* runtime_initialize_Init_CbvSimproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_ControlFlow(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = runtime_initialize_Lean_Compiler_ComputableExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_859861108____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1317514424____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_20_();
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
lean_object* initialize_Lean_Compiler_ComputableExt(uint8_t builtin);
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
res = initialize_Lean_Compiler_ComputableExt(builtin);
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
