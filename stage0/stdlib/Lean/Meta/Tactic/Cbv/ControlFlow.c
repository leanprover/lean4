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
uint8_t lean_get_reducibility_status(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getBoundedAppFn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_mkEqRefl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_a_5_);
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
v___x_105_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_100_, v_a_86_);
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
lean_dec_ref(v___x_408_);
if (lean_obj_tag(v_a_409_) == 0)
{
uint8_t v_contextDependent_410_; lean_object* v___x_411_; 
v_contextDependent_410_ = lean_ctor_get_uint8(v_a_409_, 1);
lean_dec_ref(v_a_409_);
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
uint8_t v_contextDependent_424_; 
v_contextDependent_424_ = lean_ctor_get_uint8(v_a_412_, 1);
v___y_414_ = v_contextDependent_424_;
goto v___jp_413_;
}
else
{
uint8_t v_contextDependent_425_; 
v_contextDependent_425_ = lean_ctor_get_uint8(v_a_412_, sizeof(void*)*2 + 1);
v___y_414_ = v_contextDependent_425_;
goto v___jp_413_;
}
}
v___jp_413_:
{
if (v___y_414_ == 0)
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
else
{
lean_dec(v_a_412_);
return v___x_411_;
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
lean_object* v_e_x27_426_; uint8_t v_contextDependent_427_; lean_object* v___x_428_; 
v_e_x27_426_ = lean_ctor_get(v_a_409_, 0);
lean_inc_ref(v_e_x27_426_);
v_contextDependent_427_ = lean_ctor_get_uint8(v_a_409_, sizeof(void*)*2 + 1);
lean_dec_ref(v_a_409_);
v___x_428_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable(v_f_391_, v_00_u03b1_392_, v_c_393_, v_inst_394_, v_a_395_, v_b_396_, v_e_x27_426_, v_fallback_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; uint8_t v___y_431_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_429_);
if (v_contextDependent_427_ == 0)
{
lean_dec(v_a_429_);
return v___x_428_;
}
else
{
if (lean_obj_tag(v_a_429_) == 0)
{
uint8_t v_contextDependent_441_; 
v_contextDependent_441_ = lean_ctor_get_uint8(v_a_429_, 1);
v___y_431_ = v_contextDependent_441_;
goto v___jp_430_;
}
else
{
uint8_t v_contextDependent_442_; 
v_contextDependent_442_ = lean_ctor_get_uint8(v_a_429_, sizeof(void*)*2 + 1);
v___y_431_ = v_contextDependent_442_;
goto v___jp_430_;
}
}
v___jp_430_:
{
if (v___y_431_ == 0)
{
lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_439_; 
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_439_ == 0)
{
lean_object* v_unused_440_; 
v_unused_440_ = lean_ctor_get(v___x_428_, 0);
lean_dec(v_unused_440_);
v___x_433_ = v___x_428_;
v_isShared_434_ = v_isSharedCheck_439_;
goto v_resetjp_432_;
}
else
{
lean_dec(v___x_428_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_439_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_435_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_429_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_435_);
v___x_437_ = v___x_433_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_435_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
else
{
lean_dec(v_a_429_);
return v___x_428_;
}
}
}
else
{
return v___x_428_;
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
lean_object* v_f_443_ = _args[0];
lean_object* v_00_u03b1_444_ = _args[1];
lean_object* v_c_445_ = _args[2];
lean_object* v_inst_446_ = _args[3];
lean_object* v_a_447_ = _args[4];
lean_object* v_b_448_ = _args[5];
lean_object* v_fallback_449_ = _args[6];
lean_object* v_a_450_ = _args[7];
lean_object* v_a_451_ = _args[8];
lean_object* v_a_452_ = _args[9];
lean_object* v_a_453_ = _args[10];
lean_object* v_a_454_ = _args[11];
lean_object* v_a_455_ = _args[12];
lean_object* v_a_456_ = _args[13];
lean_object* v_a_457_ = _args[14];
lean_object* v_a_458_ = _args[15];
lean_object* v_a_459_ = _args[16];
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(v_f_443_, v_00_u03b1_444_, v_c_445_, v_inst_446_, v_a_447_, v_b_448_, v_fallback_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
lean_dec(v_a_450_);
lean_dec_ref(v_f_443_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr(lean_object* v_f_461_, lean_object* v_00_u03b1_462_, lean_object* v_c_463_, lean_object* v_inst_464_, lean_object* v_a_465_, lean_object* v_b_466_, lean_object* v_c_x27_467_, lean_object* v_h_468_, lean_object* v_inst_x27_469_, lean_object* v_fallback_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v___x_481_; 
lean_inc(v_a_479_);
lean_inc_ref(v_a_478_);
lean_inc(v_a_477_);
lean_inc_ref(v_a_476_);
lean_inc(v_a_475_);
lean_inc_ref(v_a_474_);
lean_inc(v_a_473_);
lean_inc_ref(v_a_472_);
lean_inc(v_a_471_);
lean_inc_ref(v_inst_x27_469_);
v___x_481_ = lean_sym_simp(v_inst_x27_469_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_a_482_);
lean_dec_ref(v___x_481_);
if (lean_obj_tag(v_a_482_) == 0)
{
uint8_t v_contextDependent_483_; lean_object* v___x_484_; 
v_contextDependent_483_ = lean_ctor_get_uint8(v_a_482_, 1);
lean_dec_ref(v_a_482_);
v___x_484_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(v_f_461_, v_00_u03b1_462_, v_c_463_, v_inst_464_, v_a_465_, v_b_466_, v_c_x27_467_, v_h_468_, v_inst_x27_469_, v_fallback_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; uint8_t v___y_487_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
if (v_contextDependent_483_ == 0)
{
lean_dec(v_a_485_);
return v___x_484_;
}
else
{
if (lean_obj_tag(v_a_485_) == 0)
{
uint8_t v_contextDependent_497_; 
v_contextDependent_497_ = lean_ctor_get_uint8(v_a_485_, 1);
v___y_487_ = v_contextDependent_497_;
goto v___jp_486_;
}
else
{
uint8_t v_contextDependent_498_; 
v_contextDependent_498_ = lean_ctor_get_uint8(v_a_485_, sizeof(void*)*2 + 1);
v___y_487_ = v_contextDependent_498_;
goto v___jp_486_;
}
}
v___jp_486_:
{
if (v___y_487_ == 0)
{
lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_495_; 
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_495_ == 0)
{
lean_object* v_unused_496_; 
v_unused_496_ = lean_ctor_get(v___x_484_, 0);
lean_dec(v_unused_496_);
v___x_489_ = v___x_484_;
v_isShared_490_ = v_isSharedCheck_495_;
goto v_resetjp_488_;
}
else
{
lean_dec(v___x_484_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_495_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_491_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_485_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_491_);
v___x_493_ = v___x_489_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
else
{
lean_dec(v_a_485_);
return v___x_484_;
}
}
}
else
{
return v___x_484_;
}
}
else
{
lean_object* v_e_x27_499_; uint8_t v_contextDependent_500_; lean_object* v___x_501_; 
lean_dec_ref(v_inst_x27_469_);
v_e_x27_499_ = lean_ctor_get(v_a_482_, 0);
lean_inc_ref(v_e_x27_499_);
v_contextDependent_500_ = lean_ctor_get_uint8(v_a_482_, sizeof(void*)*2 + 1);
lean_dec_ref(v_a_482_);
v___x_501_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(v_f_461_, v_00_u03b1_462_, v_c_463_, v_inst_464_, v_a_465_, v_b_466_, v_c_x27_467_, v_h_468_, v_e_x27_499_, v_fallback_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; uint8_t v___y_504_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
if (v_contextDependent_500_ == 0)
{
lean_dec(v_a_502_);
return v___x_501_;
}
else
{
if (lean_obj_tag(v_a_502_) == 0)
{
uint8_t v_contextDependent_514_; 
v_contextDependent_514_ = lean_ctor_get_uint8(v_a_502_, 1);
v___y_504_ = v_contextDependent_514_;
goto v___jp_503_;
}
else
{
uint8_t v_contextDependent_515_; 
v_contextDependent_515_ = lean_ctor_get_uint8(v_a_502_, sizeof(void*)*2 + 1);
v___y_504_ = v_contextDependent_515_;
goto v___jp_503_;
}
}
v___jp_503_:
{
if (v___y_504_ == 0)
{
lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_512_; 
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_512_ == 0)
{
lean_object* v_unused_513_; 
v_unused_513_ = lean_ctor_get(v___x_501_, 0);
lean_dec(v_unused_513_);
v___x_506_ = v___x_501_;
v_isShared_507_ = v_isSharedCheck_512_;
goto v_resetjp_505_;
}
else
{
lean_dec(v___x_501_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_512_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_508_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_502_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_508_);
v___x_510_ = v___x_506_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
else
{
lean_dec(v_a_502_);
return v___x_501_;
}
}
}
else
{
return v___x_501_;
}
}
}
else
{
lean_dec_ref(v_fallback_470_);
lean_dec_ref(v_inst_x27_469_);
lean_dec_ref(v_h_468_);
lean_dec_ref(v_c_x27_467_);
lean_dec_ref(v_b_466_);
lean_dec_ref(v_a_465_);
lean_dec_ref(v_inst_464_);
lean_dec_ref(v_c_463_);
lean_dec_ref(v_00_u03b1_462_);
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___boxed(lean_object** _args){
lean_object* v_f_516_ = _args[0];
lean_object* v_00_u03b1_517_ = _args[1];
lean_object* v_c_518_ = _args[2];
lean_object* v_inst_519_ = _args[3];
lean_object* v_a_520_ = _args[4];
lean_object* v_b_521_ = _args[5];
lean_object* v_c_x27_522_ = _args[6];
lean_object* v_h_523_ = _args[7];
lean_object* v_inst_x27_524_ = _args[8];
lean_object* v_fallback_525_ = _args[9];
lean_object* v_a_526_ = _args[10];
lean_object* v_a_527_ = _args[11];
lean_object* v_a_528_ = _args[12];
lean_object* v_a_529_ = _args[13];
lean_object* v_a_530_ = _args[14];
lean_object* v_a_531_ = _args[15];
lean_object* v_a_532_ = _args[16];
lean_object* v_a_533_ = _args[17];
lean_object* v_a_534_ = _args[18];
lean_object* v_a_535_ = _args[19];
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr(v_f_516_, v_00_u03b1_517_, v_c_518_, v_inst_519_, v_a_520_, v_b_521_, v_c_x27_522_, v_h_523_, v_inst_x27_524_, v_fallback_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_f_516_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0(lean_object* v___x_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_537_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed(lean_object* v___x_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0(v___x_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(lean_object* v_f_561_, lean_object* v_a_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v___y_571_; lean_object* v___x_574_; uint8_t v_debug_575_; 
v___x_574_ = lean_st_ref_get(v___y_564_);
v_debug_575_ = lean_ctor_get_uint8(v___x_574_, sizeof(void*)*10);
lean_dec(v___x_574_);
if (v_debug_575_ == 0)
{
v___y_571_ = v___y_564_;
goto v___jp_570_;
}
else
{
lean_object* v___x_576_; 
lean_inc_ref(v_f_561_);
v___x_576_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_561_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v___x_577_; 
lean_dec_ref(v___x_576_);
lean_inc_ref(v_a_562_);
v___x_577_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_dec_ref(v___x_577_);
v___y_571_ = v___y_564_;
goto v___jp_570_;
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
lean_dec_ref(v_a_562_);
lean_dec_ref(v_f_561_);
v_a_578_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_577_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_577_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_dec_ref(v_a_562_);
lean_dec_ref(v_f_561_);
v_a_586_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_576_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_576_);
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
v___jp_570_:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = l_Lean_Expr_app___override(v_f_561_, v_a_562_);
v___x_573_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_572_, v___y_571_);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg___boxed(lean_object* v_f_594_, lean_object* v_a_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(v_f_594_, v_a_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1(lean_object* v_f_604_, lean_object* v_a_u2081_605_, lean_object* v_a_u2082_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(v_f_604_, v_a_u2081_605_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_619_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_a_618_);
lean_dec_ref(v___x_617_);
v___x_619_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(v_a_618_, v_a_u2082_606_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
return v___x_619_;
}
else
{
lean_dec_ref(v_a_u2082_606_);
return v___x_617_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___boxed(lean_object* v_f_620_, lean_object* v_a_u2081_621_, lean_object* v_a_u2082_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1(v_f_620_, v_a_u2081_621_, v_a_u2082_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(lean_object* v_f_634_, lean_object* v_a_u2081_635_, lean_object* v_a_u2082_636_, lean_object* v_a_u2083_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1(v_f_634_, v_a_u2081_635_, v_a_u2082_636_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; lean_object* v___x_650_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_a_649_);
lean_dec_ref(v___x_648_);
v___x_650_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(v_a_649_, v_a_u2083_637_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
return v___x_650_;
}
else
{
lean_dec_ref(v_a_u2083_637_);
return v___x_648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___boxed(lean_object* v_f_651_, lean_object* v_a_u2081_652_, lean_object* v_a_u2082_653_, lean_object* v_a_u2083_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(v_f_651_, v_a_u2081_652_, v_a_u2082_653_, v_a_u2083_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(lean_object* v_f_666_, lean_object* v_a_u2081_667_, lean_object* v_a_u2082_668_, lean_object* v_a_u2083_669_, lean_object* v_a_u2084_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(v_f_666_, v_a_u2081_667_, v_a_u2082_668_, v_a_u2083_669_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v___x_683_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_a_682_);
lean_dec_ref(v___x_681_);
v___x_683_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(v_a_682_, v_a_u2084_670_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
return v___x_683_;
}
else
{
lean_dec_ref(v_a_u2084_670_);
return v___x_681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0___boxed(lean_object* v_f_684_, lean_object* v_a_u2081_685_, lean_object* v_a_u2082_686_, lean_object* v_a_u2083_687_, lean_object* v_a_u2084_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(v_f_684_, v_a_u2081_685_, v_a_u2082_686_, v_a_u2083_687_, v_a_u2084_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1(lean_object* v___x_705_, lean_object* v_e_x27_706_, lean_object* v___x_707_, lean_object* v_arg_708_, lean_object* v_arg_709_, lean_object* v_e_710_, lean_object* v_proof_711_, uint8_t v___x_712_, uint8_t v_contextDependent_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___x_724_; 
lean_inc_ref(v___x_707_);
lean_inc_ref(v_e_x27_706_);
v___x_724_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(v___x_705_, v_e_x27_706_, v___x_707_, v_arg_708_, v_arg_709_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_736_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_736_ == 0)
{
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_736_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_736_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_734_; 
v___x_729_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__1));
v___x_730_ = l_Lean_Expr_replaceFn(v_e_710_, v___x_729_);
v___x_731_ = l_Lean_mkApp3(v___x_730_, v_e_x27_706_, v___x_707_, v_proof_711_);
v___x_732_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_732_, 0, v_a_725_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
lean_ctor_set_uint8(v___x_732_, sizeof(void*)*2, v___x_712_);
lean_ctor_set_uint8(v___x_732_, sizeof(void*)*2 + 1, v_contextDependent_713_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___x_732_);
v___x_734_ = v___x_727_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec_ref(v_proof_711_);
lean_dec_ref(v_e_710_);
lean_dec_ref(v___x_707_);
lean_dec_ref(v_e_x27_706_);
v_a_737_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_724_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_724_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___boxed(lean_object** _args){
lean_object* v___x_745_ = _args[0];
lean_object* v_e_x27_746_ = _args[1];
lean_object* v___x_747_ = _args[2];
lean_object* v_arg_748_ = _args[3];
lean_object* v_arg_749_ = _args[4];
lean_object* v_e_750_ = _args[5];
lean_object* v_proof_751_ = _args[6];
lean_object* v___x_752_ = _args[7];
lean_object* v_contextDependent_753_ = _args[8];
lean_object* v___y_754_ = _args[9];
lean_object* v___y_755_ = _args[10];
lean_object* v___y_756_ = _args[11];
lean_object* v___y_757_ = _args[12];
lean_object* v___y_758_ = _args[13];
lean_object* v___y_759_ = _args[14];
lean_object* v___y_760_ = _args[15];
lean_object* v___y_761_ = _args[16];
lean_object* v___y_762_ = _args[17];
lean_object* v___y_763_ = _args[18];
_start:
{
uint8_t v___x_18465__boxed_764_; uint8_t v_contextDependent_18466__boxed_765_; lean_object* v_res_766_; 
v___x_18465__boxed_764_ = lean_unbox(v___x_752_);
v_contextDependent_18466__boxed_765_ = lean_unbox(v_contextDependent_753_);
v_res_766_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1(v___x_745_, v_e_x27_746_, v___x_747_, v_arg_748_, v_arg_749_, v_e_750_, v_proof_751_, v___x_18465__boxed_764_, v_contextDependent_18466__boxed_765_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
return v_res_766_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_777_ = lean_box(0);
v___x_778_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__5));
v___x_779_ = l_Lean_mkConst(v___x_778_, v___x_777_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2(uint8_t v___x_786_, lean_object* v_e_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v___x_801_; uint8_t v___x_802_; 
lean_inc_ref(v_e_787_);
v___x_801_ = l_Lean_Expr_cleanupAnnotations(v_e_787_);
v___x_802_ = l_Lean_Expr_isApp(v___x_801_);
if (v___x_802_ == 0)
{
lean_dec_ref(v___x_801_);
lean_dec_ref(v_e_787_);
goto v___jp_798_;
}
else
{
lean_object* v_arg_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v_arg_803_ = lean_ctor_get(v___x_801_, 1);
lean_inc_ref(v_arg_803_);
v___x_804_ = l_Lean_Expr_appFnCleanup___redArg(v___x_801_);
v___x_805_ = l_Lean_Expr_isApp(v___x_804_);
if (v___x_805_ == 0)
{
lean_dec_ref(v___x_804_);
lean_dec_ref(v_arg_803_);
lean_dec_ref(v_e_787_);
goto v___jp_798_;
}
else
{
lean_object* v_arg_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v_arg_806_ = lean_ctor_get(v___x_804_, 1);
lean_inc_ref(v_arg_806_);
v___x_807_ = l_Lean_Expr_appFnCleanup___redArg(v___x_804_);
v___x_808_ = l_Lean_Expr_isApp(v___x_807_);
if (v___x_808_ == 0)
{
lean_dec_ref(v___x_807_);
lean_dec_ref(v_arg_806_);
lean_dec_ref(v_arg_803_);
lean_dec_ref(v_e_787_);
goto v___jp_798_;
}
else
{
lean_object* v_arg_809_; lean_object* v___x_810_; uint8_t v___x_811_; 
v_arg_809_ = lean_ctor_get(v___x_807_, 1);
lean_inc_ref(v_arg_809_);
v___x_810_ = l_Lean_Expr_appFnCleanup___redArg(v___x_807_);
v___x_811_ = l_Lean_Expr_isApp(v___x_810_);
if (v___x_811_ == 0)
{
lean_dec_ref(v___x_810_);
lean_dec_ref(v_arg_809_);
lean_dec_ref(v_arg_806_);
lean_dec_ref(v_arg_803_);
lean_dec_ref(v_e_787_);
goto v___jp_798_;
}
else
{
lean_object* v_arg_812_; lean_object* v___x_813_; uint8_t v___x_814_; 
v_arg_812_ = lean_ctor_get(v___x_810_, 1);
lean_inc_ref(v_arg_812_);
v___x_813_ = l_Lean_Expr_appFnCleanup___redArg(v___x_810_);
v___x_814_ = l_Lean_Expr_isApp(v___x_813_);
if (v___x_814_ == 0)
{
lean_dec_ref(v___x_813_);
lean_dec_ref(v_arg_812_);
lean_dec_ref(v_arg_809_);
lean_dec_ref(v_arg_806_);
lean_dec_ref(v_arg_803_);
lean_dec_ref(v_e_787_);
goto v___jp_798_;
}
else
{
lean_object* v_arg_815_; lean_object* v___x_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v_arg_815_ = lean_ctor_get(v___x_813_, 1);
lean_inc_ref(v_arg_815_);
v___x_816_ = l_Lean_Expr_appFnCleanup___redArg(v___x_813_);
v___x_817_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__1));
v___x_818_ = l_Lean_Expr_isConstOf(v___x_816_, v___x_817_);
if (v___x_818_ == 0)
{
lean_dec_ref(v___x_816_);
lean_dec_ref(v_arg_815_);
lean_dec_ref(v_arg_812_);
lean_dec_ref(v_arg_809_);
lean_dec_ref(v_arg_806_);
lean_dec_ref(v_arg_803_);
lean_dec_ref(v_e_787_);
goto v___jp_798_;
}
else
{
lean_object* v___x_819_; 
lean_inc(v___y_796_);
lean_inc_ref(v___y_795_);
lean_inc(v___y_794_);
lean_inc_ref(v___y_793_);
lean_inc(v___y_792_);
lean_inc_ref(v___y_791_);
lean_inc(v___y_790_);
lean_inc_ref(v___y_789_);
lean_inc(v___y_788_);
lean_inc_ref(v_arg_812_);
v___x_819_ = lean_sym_simp(v_arg_812_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_a_820_);
lean_dec_ref(v___x_819_);
if (lean_obj_tag(v_a_820_) == 0)
{
uint8_t v_contextDependent_821_; lean_object* v___x_822_; 
lean_dec_ref(v_e_787_);
v_contextDependent_821_ = lean_ctor_get_uint8(v_a_820_, 1);
lean_dec_ref(v_a_820_);
v___x_822_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_812_, v___y_791_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_863_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_863_ == 0)
{
v___x_825_ = v___x_822_;
v_isShared_826_ = v_isSharedCheck_863_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_822_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_863_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
uint8_t v___x_827_; 
v___x_827_ = lean_unbox(v_a_823_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; 
lean_del_object(v___x_825_);
v___x_828_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_812_, v___y_791_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_846_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_846_ == 0)
{
v___x_831_ = v___x_828_;
v_isShared_832_ = v_isSharedCheck_846_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_846_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
uint8_t v___x_833_; 
v___x_833_ = lean_unbox(v_a_829_);
lean_dec(v_a_829_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___f_835_; lean_object* v___x_836_; 
lean_del_object(v___x_831_);
lean_dec(v_a_823_);
v___x_834_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_818_, v_contextDependent_821_);
v___f_835_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_835_, 0, v___x_834_);
v___x_836_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(v___x_816_, v_arg_815_, v_arg_812_, v_arg_809_, v_arg_806_, v_arg_803_, v___f_835_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
lean_dec_ref(v___x_816_);
return v___x_836_;
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; lean_object* v___x_844_; 
lean_dec_ref(v_arg_812_);
lean_dec_ref(v_arg_809_);
v___x_837_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__2));
v___x_838_ = l_Lean_Expr_constLevels_x21(v___x_816_);
lean_dec_ref(v___x_816_);
v___x_839_ = l_Lean_mkConst(v___x_837_, v___x_838_);
lean_inc_ref(v_arg_803_);
v___x_840_ = l_Lean_mkApp3(v___x_839_, v_arg_815_, v_arg_806_, v_arg_803_);
v___x_841_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_841_, 0, v_arg_803_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = lean_unbox(v_a_823_);
lean_dec(v_a_823_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*2, v___x_842_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*2 + 1, v_contextDependent_821_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_841_);
v___x_844_ = v___x_831_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_841_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
lean_dec(v_a_823_);
lean_dec_ref(v___x_816_);
lean_dec_ref(v_arg_815_);
lean_dec_ref(v_arg_812_);
lean_dec_ref(v_arg_809_);
lean_dec_ref(v_arg_806_);
lean_dec_ref(v_arg_803_);
v_a_847_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_828_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_828_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
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
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
lean_dec(v_a_823_);
lean_dec_ref(v_arg_812_);
lean_dec_ref(v_arg_809_);
v___x_855_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__3));
v___x_856_ = l_Lean_Expr_constLevels_x21(v___x_816_);
lean_dec_ref(v___x_816_);
v___x_857_ = l_Lean_mkConst(v___x_855_, v___x_856_);
lean_inc_ref(v_arg_806_);
v___x_858_ = l_Lean_mkApp3(v___x_857_, v_arg_815_, v_arg_806_, v_arg_803_);
v___x_859_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_859_, 0, v_arg_806_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
lean_ctor_set_uint8(v___x_859_, sizeof(void*)*2, v___x_786_);
lean_ctor_set_uint8(v___x_859_, sizeof(void*)*2 + 1, v_contextDependent_821_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_859_);
v___x_861_ = v___x_825_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_dec_ref(v___x_816_);
lean_dec_ref(v_arg_815_);
lean_dec_ref(v_arg_812_);
lean_dec_ref(v_arg_809_);
lean_dec_ref(v_arg_806_);
lean_dec_ref(v_arg_803_);
v_a_864_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_822_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_822_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
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
lean_object* v_e_x27_872_; lean_object* v_proof_873_; uint8_t v_contextDependent_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_936_; 
v_e_x27_872_ = lean_ctor_get(v_a_820_, 0);
v_proof_873_ = lean_ctor_get(v_a_820_, 1);
v_contextDependent_874_ = lean_ctor_get_uint8(v_a_820_, sizeof(void*)*2 + 1);
v_isSharedCheck_936_ = !lean_is_exclusive(v_a_820_);
if (v_isSharedCheck_936_ == 0)
{
v___x_876_ = v_a_820_;
v_isShared_877_ = v_isSharedCheck_936_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_proof_873_);
lean_inc(v_e_x27_872_);
lean_dec(v_a_820_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_936_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_872_, v___y_791_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_927_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_927_ == 0)
{
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_927_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_927_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
uint8_t v___x_883_; 
v___x_883_ = lean_unbox(v_a_879_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; 
lean_del_object(v___x_881_);
v___x_884_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_872_, v___y_791_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_909_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_909_ == 0)
{
v___x_887_ = v___x_884_;
v_isShared_888_ = v_isSharedCheck_909_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_884_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_909_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
uint8_t v___x_889_; 
v___x_889_ = lean_unbox(v_a_885_);
lean_dec(v_a_885_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___f_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
lean_del_object(v___x_887_);
lean_dec(v_a_879_);
lean_del_object(v___x_876_);
v___x_890_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6);
lean_inc_ref_n(v_proof_873_, 2);
lean_inc_ref_n(v_arg_809_, 2);
lean_inc_ref_n(v_e_x27_872_, 2);
lean_inc_ref_n(v_arg_812_, 2);
v___x_891_ = l_Lean_mkApp4(v___x_890_, v_arg_812_, v_e_x27_872_, v_arg_809_, v_proof_873_);
v___x_892_ = lean_unsigned_to_nat(4u);
v___x_893_ = l_Lean_Expr_getBoundedAppFn(v___x_892_, v_e_787_);
v___x_894_ = lean_box(v___x_818_);
v___x_895_ = lean_box(v_contextDependent_874_);
lean_inc_ref_n(v_arg_803_, 2);
lean_inc_ref_n(v_arg_806_, 2);
lean_inc_ref(v___x_891_);
v___f_896_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___boxed), 19, 9);
lean_closure_set(v___f_896_, 0, v___x_893_);
lean_closure_set(v___f_896_, 1, v_e_x27_872_);
lean_closure_set(v___f_896_, 2, v___x_891_);
lean_closure_set(v___f_896_, 3, v_arg_806_);
lean_closure_set(v___f_896_, 4, v_arg_803_);
lean_closure_set(v___f_896_, 5, v_e_787_);
lean_closure_set(v___f_896_, 6, v_proof_873_);
lean_closure_set(v___f_896_, 7, v___x_894_);
lean_closure_set(v___f_896_, 8, v___x_895_);
lean_inc_ref(v_arg_815_);
lean_inc_ref(v___x_816_);
v___x_897_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___boxed), 20, 10);
lean_closure_set(v___x_897_, 0, v___x_816_);
lean_closure_set(v___x_897_, 1, v_arg_815_);
lean_closure_set(v___x_897_, 2, v_arg_812_);
lean_closure_set(v___x_897_, 3, v_arg_809_);
lean_closure_set(v___x_897_, 4, v_arg_806_);
lean_closure_set(v___x_897_, 5, v_arg_803_);
lean_closure_set(v___x_897_, 6, v_e_x27_872_);
lean_closure_set(v___x_897_, 7, v_proof_873_);
lean_closure_set(v___x_897_, 8, v___x_891_);
lean_closure_set(v___x_897_, 9, v___f_896_);
v___x_898_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(v___x_816_, v_arg_815_, v_arg_812_, v_arg_809_, v_arg_806_, v_arg_803_, v___x_897_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
lean_dec_ref(v___x_816_);
return v___x_898_;
}
else
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_903_; 
lean_dec_ref(v_e_x27_872_);
lean_dec_ref(v___x_816_);
lean_dec_ref(v_arg_815_);
lean_dec_ref(v_arg_812_);
lean_dec_ref(v_arg_809_);
lean_dec_ref(v_arg_806_);
v___x_899_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__8));
v___x_900_ = l_Lean_Expr_replaceFn(v_e_787_, v___x_899_);
v___x_901_ = l_Lean_Expr_app___override(v___x_900_, v_proof_873_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 1, v___x_901_);
lean_ctor_set(v___x_876_, 0, v_arg_803_);
v___x_903_ = v___x_876_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_arg_803_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v___x_901_);
v___x_903_ = v_reuseFailAlloc_908_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
uint8_t v___x_904_; lean_object* v___x_906_; 
v___x_904_ = lean_unbox(v_a_879_);
lean_dec(v_a_879_);
lean_ctor_set_uint8(v___x_903_, sizeof(void*)*2, v___x_904_);
lean_ctor_set_uint8(v___x_903_, sizeof(void*)*2 + 1, v_contextDependent_874_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_903_);
v___x_906_ = v___x_887_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_903_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
else
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
lean_dec(v_a_879_);
lean_del_object(v___x_876_);
lean_dec_ref(v_proof_873_);
lean_dec_ref(v_e_x27_872_);
lean_dec_ref(v___x_816_);
lean_dec_ref(v_arg_815_);
lean_dec_ref(v_arg_812_);
lean_dec_ref(v_arg_809_);
lean_dec_ref(v_arg_806_);
lean_dec_ref(v_arg_803_);
lean_dec_ref(v_e_787_);
v_a_910_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_884_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_884_);
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
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_922_; 
lean_dec(v_a_879_);
lean_dec_ref(v_e_x27_872_);
lean_dec_ref(v___x_816_);
lean_dec_ref(v_arg_815_);
lean_dec_ref(v_arg_812_);
lean_dec_ref(v_arg_809_);
lean_dec_ref(v_arg_803_);
v___x_918_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__10));
v___x_919_ = l_Lean_Expr_replaceFn(v_e_787_, v___x_918_);
v___x_920_ = l_Lean_Expr_app___override(v___x_919_, v_proof_873_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 1, v___x_920_);
lean_ctor_set(v___x_876_, 0, v_arg_806_);
v___x_922_ = v___x_876_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_arg_806_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v___x_920_);
lean_ctor_set_uint8(v_reuseFailAlloc_926_, sizeof(void*)*2 + 1, v_contextDependent_874_);
v___x_922_ = v_reuseFailAlloc_926_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_924_; 
lean_ctor_set_uint8(v___x_922_, sizeof(void*)*2, v___x_786_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_922_);
v___x_924_ = v___x_881_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
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
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
lean_del_object(v___x_876_);
lean_dec_ref(v_proof_873_);
lean_dec_ref(v_e_x27_872_);
lean_dec_ref(v___x_816_);
lean_dec_ref(v_arg_815_);
lean_dec_ref(v_arg_812_);
lean_dec_ref(v_arg_809_);
lean_dec_ref(v_arg_806_);
lean_dec_ref(v_arg_803_);
lean_dec_ref(v_e_787_);
v_a_928_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_878_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_878_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_816_);
lean_dec_ref(v_arg_815_);
lean_dec_ref(v_arg_812_);
lean_dec_ref(v_arg_809_);
lean_dec_ref(v_arg_806_);
lean_dec_ref(v_arg_803_);
lean_dec_ref(v_e_787_);
return v___x_819_;
}
}
}
}
}
}
}
v___jp_798_:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_799_, 0, v___x_786_);
lean_ctor_set_uint8(v___x_799_, 1, v___x_786_);
v___x_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
return v___x_800_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___boxed(lean_object* v___x_937_, lean_object* v_e_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
uint8_t v___x_18600__boxed_949_; lean_object* v_res_950_; 
v___x_18600__boxed_949_ = lean_unbox(v___x_937_);
v_res_950_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2(v___x_18600__boxed_949_, v_e_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv(lean_object* v_e_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_numArgs_962_; lean_object* v___x_963_; uint8_t v___x_964_; 
v_numArgs_962_ = l_Lean_Expr_getAppNumArgs(v_e_951_);
v___x_963_ = lean_unsigned_to_nat(5u);
v___x_964_ = lean_nat_dec_lt(v_numArgs_962_, v___x_963_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___f_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_965_ = lean_box(v___x_964_);
v___f_966_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___boxed), 12, 1);
lean_closure_set(v___f_966_, 0, v___x_965_);
v___x_967_ = lean_nat_sub(v_numArgs_962_, v___x_963_);
lean_dec(v_numArgs_962_);
v___x_968_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_951_, v___x_967_, v___f_966_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
lean_dec(v___x_967_);
return v___x_968_;
}
else
{
uint8_t v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
lean_dec(v_numArgs_962_);
lean_dec_ref(v_e_951_);
v___x_969_ = 0;
v___x_970_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_970_, 0, v___x_964_);
lean_ctor_set_uint8(v___x_970_, 1, v___x_969_);
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
return v___x_971_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___boxed(lean_object* v_e_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv(v_e_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
lean_dec(v_a_981_);
lean_dec_ref(v_a_980_);
lean_dec(v_a_979_);
lean_dec_ref(v_a_978_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
lean_dec(v_a_973_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1(lean_object* v_f_984_, lean_object* v_a_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(v_f_984_, v_a_985_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___boxed(lean_object* v_f_997_, lean_object* v_a_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1(v_f_997_, v_a_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1067_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_));
v___x_1068_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__20_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_));
v___x_1069_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___boxed), 11, 0);
v___x_1070_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_1067_, v___x_1068_, v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16____boxed(lean_object* v_a_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_();
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_1074_; uint8_t v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1074_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_));
v___x_1075_ = 0;
v___x_1076_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___boxed), 11, 0);
v___x_1077_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_1074_, v___x_1075_, v___x_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_18____boxed(lean_object* v_a_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_18_();
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(lean_object* v_f_1090_, lean_object* v_00_u03b1_1091_, lean_object* v_c_1092_, lean_object* v_inst_1093_, lean_object* v_a_1094_, lean_object* v_b_1095_, lean_object* v_instToMatch_1096_, lean_object* v_fallback_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_instToMatch_1096_, v_a_1104_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_a_1109_);
lean_dec_ref(v___x_1108_);
v___x_1110_ = l_Lean_Expr_cleanupAnnotations(v_a_1109_);
v___x_1111_ = l_Lean_Expr_isApp(v___x_1110_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; 
lean_dec_ref(v___x_1110_);
lean_dec_ref(v_b_1095_);
lean_dec_ref(v_a_1094_);
lean_dec_ref(v_inst_1093_);
lean_dec_ref(v_c_1092_);
lean_dec_ref(v_00_u03b1_1091_);
lean_inc(v_a_1106_);
lean_inc_ref(v_a_1105_);
lean_inc(v_a_1104_);
lean_inc_ref(v_a_1103_);
lean_inc(v_a_1102_);
lean_inc_ref(v_a_1101_);
lean_inc(v_a_1100_);
lean_inc_ref(v_a_1099_);
lean_inc(v_a_1098_);
v___x_1112_ = lean_apply_10(v_fallback_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, lean_box(0));
return v___x_1112_;
}
else
{
lean_object* v_arg_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v_arg_1113_ = lean_ctor_get(v___x_1110_, 1);
lean_inc_ref(v_arg_1113_);
v___x_1114_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1110_);
v___x_1115_ = l_Lean_Expr_isApp(v___x_1114_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; 
lean_dec_ref(v___x_1114_);
lean_dec_ref(v_arg_1113_);
lean_dec_ref(v_b_1095_);
lean_dec_ref(v_a_1094_);
lean_dec_ref(v_inst_1093_);
lean_dec_ref(v_c_1092_);
lean_dec_ref(v_00_u03b1_1091_);
lean_inc(v_a_1106_);
lean_inc_ref(v_a_1105_);
lean_inc(v_a_1104_);
lean_inc_ref(v_a_1103_);
lean_inc(v_a_1102_);
lean_inc_ref(v_a_1101_);
lean_inc(v_a_1100_);
lean_inc_ref(v_a_1099_);
lean_inc(v_a_1098_);
v___x_1116_ = lean_apply_10(v_fallback_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, lean_box(0));
return v___x_1116_;
}
else
{
lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v___x_1117_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1114_);
v___x_1118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_1119_ = l_Lean_Expr_isConstOf(v___x_1117_, v___x_1118_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; uint8_t v___x_1121_; 
v___x_1120_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3));
v___x_1121_ = l_Lean_Expr_isConstOf(v___x_1117_, v___x_1120_);
lean_dec_ref(v___x_1117_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; 
lean_dec_ref(v_arg_1113_);
lean_dec_ref(v_b_1095_);
lean_dec_ref(v_a_1094_);
lean_dec_ref(v_inst_1093_);
lean_dec_ref(v_c_1092_);
lean_dec_ref(v_00_u03b1_1091_);
lean_inc(v_a_1106_);
lean_inc_ref(v_a_1105_);
lean_inc(v_a_1104_);
lean_inc_ref(v_a_1103_);
lean_inc(v_a_1102_);
lean_inc_ref(v_a_1101_);
lean_inc(v_a_1100_);
lean_inc_ref(v_a_1099_);
lean_inc(v_a_1098_);
v___x_1122_ = lean_apply_10(v_fallback_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, lean_box(0));
return v___x_1122_;
}
else
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_dec_ref(v_fallback_1097_);
v___x_1123_ = lean_unsigned_to_nat(1u);
v___x_1124_ = lean_mk_empty_array_with_capacity(v___x_1123_);
lean_inc_ref(v_arg_1113_);
v___x_1125_ = lean_array_push(v___x_1124_, v_arg_1113_);
lean_inc_ref(v_a_1094_);
v___x_1126_ = l_Lean_Expr_betaRev(v_a_1094_, v___x_1125_, v___x_1119_, v___x_1119_);
lean_dec_ref(v___x_1125_);
v___x_1127_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_1126_, v_a_1102_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1140_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1130_ = v___x_1127_;
v_isShared_1131_ = v_isSharedCheck_1140_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1127_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1140_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1132_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1));
v___x_1133_ = l_Lean_Expr_constLevels_x21(v_f_1090_);
v___x_1134_ = l_Lean_mkConst(v___x_1132_, v___x_1133_);
v___x_1135_ = l_Lean_mkApp6(v___x_1134_, v_00_u03b1_1091_, v_c_1092_, v_inst_1093_, v_a_1094_, v_b_1095_, v_arg_1113_);
v___x_1136_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1136_, 0, v_a_1128_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*2, v___x_1119_);
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*2 + 1, v___x_1119_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v___x_1136_);
v___x_1138_ = v___x_1130_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_dec_ref(v_arg_1113_);
lean_dec_ref(v_b_1095_);
lean_dec_ref(v_a_1094_);
lean_dec_ref(v_inst_1093_);
lean_dec_ref(v_c_1092_);
lean_dec_ref(v_00_u03b1_1091_);
v_a_1141_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1127_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1127_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
else
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; uint8_t v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
lean_dec_ref(v___x_1117_);
lean_dec_ref(v_fallback_1097_);
v___x_1149_ = lean_unsigned_to_nat(1u);
v___x_1150_ = lean_mk_empty_array_with_capacity(v___x_1149_);
lean_inc_ref(v_arg_1113_);
v___x_1151_ = lean_array_push(v___x_1150_, v_arg_1113_);
v___x_1152_ = 0;
lean_inc_ref(v_b_1095_);
v___x_1153_ = l_Lean_Expr_betaRev(v_b_1095_, v___x_1151_, v___x_1152_, v___x_1152_);
lean_dec_ref(v___x_1151_);
v___x_1154_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_1153_, v_a_1102_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1167_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1167_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1167_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1159_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3));
v___x_1160_ = l_Lean_Expr_constLevels_x21(v_f_1090_);
v___x_1161_ = l_Lean_mkConst(v___x_1159_, v___x_1160_);
v___x_1162_ = l_Lean_mkApp6(v___x_1161_, v_00_u03b1_1091_, v_c_1092_, v_inst_1093_, v_a_1094_, v_b_1095_, v_arg_1113_);
v___x_1163_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1163_, 0, v_a_1155_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
lean_ctor_set_uint8(v___x_1163_, sizeof(void*)*2, v___x_1152_);
lean_ctor_set_uint8(v___x_1163_, sizeof(void*)*2 + 1, v___x_1152_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v___x_1163_);
v___x_1165_ = v___x_1157_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
lean_dec_ref(v_arg_1113_);
lean_dec_ref(v_b_1095_);
lean_dec_ref(v_a_1094_);
lean_dec_ref(v_inst_1093_);
lean_dec_ref(v_c_1092_);
lean_dec_ref(v_00_u03b1_1091_);
v_a_1168_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1154_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1154_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec_ref(v_fallback_1097_);
lean_dec_ref(v_b_1095_);
lean_dec_ref(v_a_1094_);
lean_dec_ref(v_inst_1093_);
lean_dec_ref(v_c_1092_);
lean_dec_ref(v_00_u03b1_1091_);
v_a_1176_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1108_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1108_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___boxed(lean_object** _args){
lean_object* v_f_1184_ = _args[0];
lean_object* v_00_u03b1_1185_ = _args[1];
lean_object* v_c_1186_ = _args[2];
lean_object* v_inst_1187_ = _args[3];
lean_object* v_a_1188_ = _args[4];
lean_object* v_b_1189_ = _args[5];
lean_object* v_instToMatch_1190_ = _args[6];
lean_object* v_fallback_1191_ = _args[7];
lean_object* v_a_1192_ = _args[8];
lean_object* v_a_1193_ = _args[9];
lean_object* v_a_1194_ = _args[10];
lean_object* v_a_1195_ = _args[11];
lean_object* v_a_1196_ = _args[12];
lean_object* v_a_1197_ = _args[13];
lean_object* v_a_1198_ = _args[14];
lean_object* v_a_1199_ = _args[15];
lean_object* v_a_1200_ = _args[16];
lean_object* v_a_1201_ = _args[17];
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(v_f_1184_, v_00_u03b1_1185_, v_c_1186_, v_inst_1187_, v_a_1188_, v_b_1189_, v_instToMatch_1190_, v_fallback_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_);
lean_dec(v_a_1200_);
lean_dec_ref(v_a_1199_);
lean_dec(v_a_1198_);
lean_dec_ref(v_a_1197_);
lean_dec(v_a_1196_);
lean_dec_ref(v_a_1195_);
lean_dec(v_a_1194_);
lean_dec_ref(v_a_1193_);
lean_dec(v_a_1192_);
lean_dec_ref(v_f_1184_);
return v_res_1202_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__3(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1208_ = lean_box(0);
v___x_1209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2));
v___x_1210_ = l_Lean_mkConst(v___x_1209_, v___x_1208_);
return v___x_1210_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__8(void){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1220_ = lean_box(0);
v___x_1221_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7));
v___x_1222_ = l_Lean_mkConst(v___x_1221_, v___x_1220_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(lean_object* v_f_1228_, lean_object* v_00_u03b1_1229_, lean_object* v_c_1230_, lean_object* v_inst_1231_, lean_object* v_a_1232_, lean_object* v_b_1233_, lean_object* v_c_x27_1234_, lean_object* v_h_1235_, lean_object* v_inst_x27_1236_, lean_object* v_fallback_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_inst_x27_1236_, v_a_1244_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_a_1249_);
lean_dec_ref(v___x_1248_);
v___x_1250_ = l_Lean_Expr_cleanupAnnotations(v_a_1249_);
v___x_1251_ = l_Lean_Expr_isApp(v___x_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; 
lean_dec_ref(v___x_1250_);
lean_dec_ref(v_h_1235_);
lean_dec_ref(v_c_x27_1234_);
lean_dec_ref(v_b_1233_);
lean_dec_ref(v_a_1232_);
lean_dec_ref(v_inst_1231_);
lean_dec_ref(v_c_1230_);
lean_dec_ref(v_00_u03b1_1229_);
lean_inc(v_a_1246_);
lean_inc_ref(v_a_1245_);
lean_inc(v_a_1244_);
lean_inc_ref(v_a_1243_);
lean_inc(v_a_1242_);
lean_inc_ref(v_a_1241_);
lean_inc(v_a_1240_);
lean_inc_ref(v_a_1239_);
lean_inc(v_a_1238_);
v___x_1252_ = lean_apply_10(v_fallback_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, lean_box(0));
return v___x_1252_;
}
else
{
lean_object* v_arg_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
v_arg_1253_ = lean_ctor_get(v___x_1250_, 1);
lean_inc_ref(v_arg_1253_);
v___x_1254_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1250_);
v___x_1255_ = l_Lean_Expr_isApp(v___x_1254_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; 
lean_dec_ref(v___x_1254_);
lean_dec_ref(v_arg_1253_);
lean_dec_ref(v_h_1235_);
lean_dec_ref(v_c_x27_1234_);
lean_dec_ref(v_b_1233_);
lean_dec_ref(v_a_1232_);
lean_dec_ref(v_inst_1231_);
lean_dec_ref(v_c_1230_);
lean_dec_ref(v_00_u03b1_1229_);
lean_inc(v_a_1246_);
lean_inc_ref(v_a_1245_);
lean_inc(v_a_1244_);
lean_inc_ref(v_a_1243_);
lean_inc(v_a_1242_);
lean_inc_ref(v_a_1241_);
lean_inc(v_a_1240_);
lean_inc_ref(v_a_1239_);
lean_inc(v_a_1238_);
v___x_1256_ = lean_apply_10(v_fallback_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, lean_box(0));
return v___x_1256_;
}
else
{
lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v___x_1257_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1254_);
v___x_1258_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_1259_ = l_Lean_Expr_isConstOf(v___x_1257_, v___x_1258_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; uint8_t v___x_1261_; 
v___x_1260_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3));
v___x_1261_ = l_Lean_Expr_isConstOf(v___x_1257_, v___x_1260_);
lean_dec_ref(v___x_1257_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; 
lean_dec_ref(v_arg_1253_);
lean_dec_ref(v_h_1235_);
lean_dec_ref(v_c_x27_1234_);
lean_dec_ref(v_b_1233_);
lean_dec_ref(v_a_1232_);
lean_dec_ref(v_inst_1231_);
lean_dec_ref(v_c_1230_);
lean_dec_ref(v_00_u03b1_1229_);
lean_inc(v_a_1246_);
lean_inc_ref(v_a_1245_);
lean_inc(v_a_1244_);
lean_inc_ref(v_a_1243_);
lean_inc(v_a_1242_);
lean_inc_ref(v_a_1241_);
lean_inc(v_a_1240_);
lean_inc_ref(v_a_1239_);
lean_inc(v_a_1238_);
v___x_1262_ = lean_apply_10(v_fallback_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, lean_box(0));
return v___x_1262_;
}
else
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
lean_dec_ref(v_fallback_1237_);
v___x_1263_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__3, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__3);
lean_inc_ref(v_arg_1253_);
lean_inc_ref(v_h_1235_);
lean_inc_ref(v_c_x27_1234_);
lean_inc_ref(v_c_1230_);
v___x_1264_ = l_Lean_mkApp4(v___x_1263_, v_c_1230_, v_c_x27_1234_, v_h_1235_, v_arg_1253_);
v___x_1265_ = lean_unsigned_to_nat(1u);
v___x_1266_ = lean_mk_empty_array_with_capacity(v___x_1265_);
v___x_1267_ = lean_array_push(v___x_1266_, v___x_1264_);
lean_inc_ref(v_a_1232_);
v___x_1268_ = l_Lean_Expr_betaRev(v_a_1232_, v___x_1267_, v___x_1259_, v___x_1259_);
lean_dec_ref(v___x_1267_);
v___x_1269_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_1268_, v_a_1242_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1282_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1272_ = v___x_1269_;
v_isShared_1273_ = v_isSharedCheck_1282_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1269_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1282_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1280_; 
v___x_1274_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__5));
v___x_1275_ = l_Lean_Expr_constLevels_x21(v_f_1228_);
v___x_1276_ = l_Lean_mkConst(v___x_1274_, v___x_1275_);
v___x_1277_ = l_Lean_mkApp8(v___x_1276_, v_00_u03b1_1229_, v_c_1230_, v_inst_1231_, v_a_1232_, v_b_1233_, v_c_x27_1234_, v_h_1235_, v_arg_1253_);
v___x_1278_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1278_, 0, v_a_1270_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
lean_ctor_set_uint8(v___x_1278_, sizeof(void*)*2, v___x_1259_);
lean_ctor_set_uint8(v___x_1278_, sizeof(void*)*2 + 1, v___x_1259_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 0, v___x_1278_);
v___x_1280_ = v___x_1272_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec_ref(v_arg_1253_);
lean_dec_ref(v_h_1235_);
lean_dec_ref(v_c_x27_1234_);
lean_dec_ref(v_b_1233_);
lean_dec_ref(v_a_1232_);
lean_dec_ref(v_inst_1231_);
lean_dec_ref(v_c_1230_);
lean_dec_ref(v_00_u03b1_1229_);
v_a_1283_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1269_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1269_);
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
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
lean_dec_ref(v___x_1257_);
lean_dec_ref(v_fallback_1237_);
v___x_1291_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__8);
lean_inc_ref(v_arg_1253_);
lean_inc_ref(v_h_1235_);
lean_inc_ref(v_c_x27_1234_);
lean_inc_ref(v_c_1230_);
v___x_1292_ = l_Lean_mkApp4(v___x_1291_, v_c_1230_, v_c_x27_1234_, v_h_1235_, v_arg_1253_);
v___x_1293_ = lean_unsigned_to_nat(1u);
v___x_1294_ = lean_mk_empty_array_with_capacity(v___x_1293_);
v___x_1295_ = lean_array_push(v___x_1294_, v___x_1292_);
v___x_1296_ = 0;
lean_inc_ref(v_b_1233_);
v___x_1297_ = l_Lean_Expr_betaRev(v_b_1233_, v___x_1295_, v___x_1296_, v___x_1296_);
lean_dec_ref(v___x_1295_);
v___x_1298_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_1297_, v_a_1242_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1311_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1301_ = v___x_1298_;
v_isShared_1302_ = v_isSharedCheck_1311_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1298_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1311_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1309_; 
v___x_1303_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__10));
v___x_1304_ = l_Lean_Expr_constLevels_x21(v_f_1228_);
v___x_1305_ = l_Lean_mkConst(v___x_1303_, v___x_1304_);
v___x_1306_ = l_Lean_mkApp8(v___x_1305_, v_00_u03b1_1229_, v_c_1230_, v_inst_1231_, v_a_1232_, v_b_1233_, v_c_x27_1234_, v_h_1235_, v_arg_1253_);
v___x_1307_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1307_, 0, v_a_1299_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
lean_ctor_set_uint8(v___x_1307_, sizeof(void*)*2, v___x_1296_);
lean_ctor_set_uint8(v___x_1307_, sizeof(void*)*2 + 1, v___x_1296_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1307_);
v___x_1309_ = v___x_1301_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1307_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_dec_ref(v_arg_1253_);
lean_dec_ref(v_h_1235_);
lean_dec_ref(v_c_x27_1234_);
lean_dec_ref(v_b_1233_);
lean_dec_ref(v_a_1232_);
lean_dec_ref(v_inst_1231_);
lean_dec_ref(v_c_1230_);
lean_dec_ref(v_00_u03b1_1229_);
v_a_1312_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1298_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1298_);
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
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec_ref(v_fallback_1237_);
lean_dec_ref(v_h_1235_);
lean_dec_ref(v_c_x27_1234_);
lean_dec_ref(v_b_1233_);
lean_dec_ref(v_a_1232_);
lean_dec_ref(v_inst_1231_);
lean_dec_ref(v_c_1230_);
lean_dec_ref(v_00_u03b1_1229_);
v_a_1320_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1248_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1248_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___boxed(lean_object** _args){
lean_object* v_f_1328_ = _args[0];
lean_object* v_00_u03b1_1329_ = _args[1];
lean_object* v_c_1330_ = _args[2];
lean_object* v_inst_1331_ = _args[3];
lean_object* v_a_1332_ = _args[4];
lean_object* v_b_1333_ = _args[5];
lean_object* v_c_x27_1334_ = _args[6];
lean_object* v_h_1335_ = _args[7];
lean_object* v_inst_x27_1336_ = _args[8];
lean_object* v_fallback_1337_ = _args[9];
lean_object* v_a_1338_ = _args[10];
lean_object* v_a_1339_ = _args[11];
lean_object* v_a_1340_ = _args[12];
lean_object* v_a_1341_ = _args[13];
lean_object* v_a_1342_ = _args[14];
lean_object* v_a_1343_ = _args[15];
lean_object* v_a_1344_ = _args[16];
lean_object* v_a_1345_ = _args[17];
lean_object* v_a_1346_ = _args[18];
lean_object* v_a_1347_ = _args[19];
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(v_f_1328_, v_00_u03b1_1329_, v_c_1330_, v_inst_1331_, v_a_1332_, v_b_1333_, v_c_x27_1334_, v_h_1335_, v_inst_x27_1336_, v_fallback_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_);
lean_dec(v_a_1346_);
lean_dec_ref(v_a_1345_);
lean_dec(v_a_1344_);
lean_dec_ref(v_a_1343_);
lean_dec(v_a_1342_);
lean_dec_ref(v_a_1341_);
lean_dec(v_a_1340_);
lean_dec_ref(v_a_1339_);
lean_dec(v_a_1338_);
lean_dec_ref(v_f_1328_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(lean_object* v_f_1349_, lean_object* v_00_u03b1_1350_, lean_object* v_c_1351_, lean_object* v_inst_1352_, lean_object* v_a_1353_, lean_object* v_b_1354_, lean_object* v_fallback_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_){
_start:
{
lean_object* v___x_1366_; 
lean_inc(v_a_1364_);
lean_inc_ref(v_a_1363_);
lean_inc(v_a_1362_);
lean_inc_ref(v_a_1361_);
lean_inc(v_a_1360_);
lean_inc_ref(v_a_1359_);
lean_inc(v_a_1358_);
lean_inc_ref(v_a_1357_);
lean_inc(v_a_1356_);
lean_inc_ref(v_inst_1352_);
v___x_1366_ = lean_sym_simp(v_inst_1352_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_a_1367_);
lean_dec_ref(v___x_1366_);
if (lean_obj_tag(v_a_1367_) == 0)
{
uint8_t v_contextDependent_1368_; lean_object* v___x_1369_; 
v_contextDependent_1368_ = lean_ctor_get_uint8(v_a_1367_, 1);
lean_dec_ref(v_a_1367_);
lean_inc_ref(v_inst_1352_);
v___x_1369_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(v_f_1349_, v_00_u03b1_1350_, v_c_1351_, v_inst_1352_, v_a_1353_, v_b_1354_, v_inst_1352_, v_fallback_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; uint8_t v___y_1372_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
if (v_contextDependent_1368_ == 0)
{
lean_dec(v_a_1370_);
return v___x_1369_;
}
else
{
if (lean_obj_tag(v_a_1370_) == 0)
{
uint8_t v_contextDependent_1382_; 
v_contextDependent_1382_ = lean_ctor_get_uint8(v_a_1370_, 1);
v___y_1372_ = v_contextDependent_1382_;
goto v___jp_1371_;
}
else
{
uint8_t v_contextDependent_1383_; 
v_contextDependent_1383_ = lean_ctor_get_uint8(v_a_1370_, sizeof(void*)*2 + 1);
v___y_1372_ = v_contextDependent_1383_;
goto v___jp_1371_;
}
}
v___jp_1371_:
{
if (v___y_1372_ == 0)
{
lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1380_; 
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1380_ == 0)
{
lean_object* v_unused_1381_; 
v_unused_1381_ = lean_ctor_get(v___x_1369_, 0);
lean_dec(v_unused_1381_);
v___x_1374_ = v___x_1369_;
v_isShared_1375_ = v_isSharedCheck_1380_;
goto v_resetjp_1373_;
}
else
{
lean_dec(v___x_1369_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1380_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1378_; 
v___x_1376_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1370_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 0, v___x_1376_);
v___x_1378_ = v___x_1374_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
else
{
lean_dec(v_a_1370_);
return v___x_1369_;
}
}
}
else
{
return v___x_1369_;
}
}
else
{
lean_object* v_e_x27_1384_; uint8_t v_contextDependent_1385_; lean_object* v___x_1386_; 
v_e_x27_1384_ = lean_ctor_get(v_a_1367_, 0);
lean_inc_ref(v_e_x27_1384_);
v_contextDependent_1385_ = lean_ctor_get_uint8(v_a_1367_, sizeof(void*)*2 + 1);
lean_dec_ref(v_a_1367_);
v___x_1386_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(v_f_1349_, v_00_u03b1_1350_, v_c_1351_, v_inst_1352_, v_a_1353_, v_b_1354_, v_e_x27_1384_, v_fallback_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; uint8_t v___y_1389_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1387_);
if (v_contextDependent_1385_ == 0)
{
lean_dec(v_a_1387_);
return v___x_1386_;
}
else
{
if (lean_obj_tag(v_a_1387_) == 0)
{
uint8_t v_contextDependent_1399_; 
v_contextDependent_1399_ = lean_ctor_get_uint8(v_a_1387_, 1);
v___y_1389_ = v_contextDependent_1399_;
goto v___jp_1388_;
}
else
{
uint8_t v_contextDependent_1400_; 
v_contextDependent_1400_ = lean_ctor_get_uint8(v_a_1387_, sizeof(void*)*2 + 1);
v___y_1389_ = v_contextDependent_1400_;
goto v___jp_1388_;
}
}
v___jp_1388_:
{
if (v___y_1389_ == 0)
{
lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1397_; 
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1397_ == 0)
{
lean_object* v_unused_1398_; 
v_unused_1398_ = lean_ctor_get(v___x_1386_, 0);
lean_dec(v_unused_1398_);
v___x_1391_ = v___x_1386_;
v_isShared_1392_ = v_isSharedCheck_1397_;
goto v_resetjp_1390_;
}
else
{
lean_dec(v___x_1386_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1397_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1393_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1387_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v___x_1393_);
v___x_1395_ = v___x_1391_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
else
{
lean_dec(v_a_1387_);
return v___x_1386_;
}
}
}
else
{
return v___x_1386_;
}
}
}
else
{
lean_dec_ref(v_fallback_1355_);
lean_dec_ref(v_b_1354_);
lean_dec_ref(v_a_1353_);
lean_dec_ref(v_inst_1352_);
lean_dec_ref(v_c_1351_);
lean_dec_ref(v_00_u03b1_1350_);
return v___x_1366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___boxed(lean_object** _args){
lean_object* v_f_1401_ = _args[0];
lean_object* v_00_u03b1_1402_ = _args[1];
lean_object* v_c_1403_ = _args[2];
lean_object* v_inst_1404_ = _args[3];
lean_object* v_a_1405_ = _args[4];
lean_object* v_b_1406_ = _args[5];
lean_object* v_fallback_1407_ = _args[6];
lean_object* v_a_1408_ = _args[7];
lean_object* v_a_1409_ = _args[8];
lean_object* v_a_1410_ = _args[9];
lean_object* v_a_1411_ = _args[10];
lean_object* v_a_1412_ = _args[11];
lean_object* v_a_1413_ = _args[12];
lean_object* v_a_1414_ = _args[13];
lean_object* v_a_1415_ = _args[14];
lean_object* v_a_1416_ = _args[15];
lean_object* v_a_1417_ = _args[16];
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(v_f_1401_, v_00_u03b1_1402_, v_c_1403_, v_inst_1404_, v_a_1405_, v_b_1406_, v_fallback_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_);
lean_dec(v_a_1416_);
lean_dec_ref(v_a_1415_);
lean_dec(v_a_1414_);
lean_dec_ref(v_a_1413_);
lean_dec(v_a_1412_);
lean_dec_ref(v_a_1411_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
lean_dec(v_a_1408_);
lean_dec_ref(v_f_1401_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr(lean_object* v_f_1419_, lean_object* v_00_u03b1_1420_, lean_object* v_c_1421_, lean_object* v_inst_1422_, lean_object* v_a_1423_, lean_object* v_b_1424_, lean_object* v_c_x27_1425_, lean_object* v_h_1426_, lean_object* v_inst_x27_1427_, lean_object* v_fallback_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v___x_1439_; 
lean_inc(v_a_1437_);
lean_inc_ref(v_a_1436_);
lean_inc(v_a_1435_);
lean_inc_ref(v_a_1434_);
lean_inc(v_a_1433_);
lean_inc_ref(v_a_1432_);
lean_inc(v_a_1431_);
lean_inc_ref(v_a_1430_);
lean_inc(v_a_1429_);
lean_inc_ref(v_inst_x27_1427_);
v___x_1439_ = lean_sym_simp(v_inst_x27_1427_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1440_);
lean_dec_ref(v___x_1439_);
if (lean_obj_tag(v_a_1440_) == 0)
{
uint8_t v_contextDependent_1441_; lean_object* v___x_1442_; 
v_contextDependent_1441_ = lean_ctor_get_uint8(v_a_1440_, 1);
lean_dec_ref(v_a_1440_);
v___x_1442_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(v_f_1419_, v_00_u03b1_1420_, v_c_1421_, v_inst_1422_, v_a_1423_, v_b_1424_, v_c_x27_1425_, v_h_1426_, v_inst_x27_1427_, v_fallback_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; uint8_t v___y_1445_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_a_1443_);
if (v_contextDependent_1441_ == 0)
{
lean_dec(v_a_1443_);
return v___x_1442_;
}
else
{
if (lean_obj_tag(v_a_1443_) == 0)
{
uint8_t v_contextDependent_1455_; 
v_contextDependent_1455_ = lean_ctor_get_uint8(v_a_1443_, 1);
v___y_1445_ = v_contextDependent_1455_;
goto v___jp_1444_;
}
else
{
uint8_t v_contextDependent_1456_; 
v_contextDependent_1456_ = lean_ctor_get_uint8(v_a_1443_, sizeof(void*)*2 + 1);
v___y_1445_ = v_contextDependent_1456_;
goto v___jp_1444_;
}
}
v___jp_1444_:
{
if (v___y_1445_ == 0)
{
lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1453_; 
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1453_ == 0)
{
lean_object* v_unused_1454_; 
v_unused_1454_ = lean_ctor_get(v___x_1442_, 0);
lean_dec(v_unused_1454_);
v___x_1447_ = v___x_1442_;
v_isShared_1448_ = v_isSharedCheck_1453_;
goto v_resetjp_1446_;
}
else
{
lean_dec(v___x_1442_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1453_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1449_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1443_);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 0, v___x_1449_);
v___x_1451_ = v___x_1447_;
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
else
{
lean_dec(v_a_1443_);
return v___x_1442_;
}
}
}
else
{
return v___x_1442_;
}
}
else
{
lean_object* v_e_x27_1457_; uint8_t v_contextDependent_1458_; lean_object* v___x_1459_; 
lean_dec_ref(v_inst_x27_1427_);
v_e_x27_1457_ = lean_ctor_get(v_a_1440_, 0);
lean_inc_ref(v_e_x27_1457_);
v_contextDependent_1458_ = lean_ctor_get_uint8(v_a_1440_, sizeof(void*)*2 + 1);
lean_dec_ref(v_a_1440_);
v___x_1459_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(v_f_1419_, v_00_u03b1_1420_, v_c_1421_, v_inst_1422_, v_a_1423_, v_b_1424_, v_c_x27_1425_, v_h_1426_, v_e_x27_1457_, v_fallback_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; uint8_t v___y_1462_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1460_);
if (v_contextDependent_1458_ == 0)
{
lean_dec(v_a_1460_);
return v___x_1459_;
}
else
{
if (lean_obj_tag(v_a_1460_) == 0)
{
uint8_t v_contextDependent_1472_; 
v_contextDependent_1472_ = lean_ctor_get_uint8(v_a_1460_, 1);
v___y_1462_ = v_contextDependent_1472_;
goto v___jp_1461_;
}
else
{
uint8_t v_contextDependent_1473_; 
v_contextDependent_1473_ = lean_ctor_get_uint8(v_a_1460_, sizeof(void*)*2 + 1);
v___y_1462_ = v_contextDependent_1473_;
goto v___jp_1461_;
}
}
v___jp_1461_:
{
if (v___y_1462_ == 0)
{
lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1470_; 
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1470_ == 0)
{
lean_object* v_unused_1471_; 
v_unused_1471_ = lean_ctor_get(v___x_1459_, 0);
lean_dec(v_unused_1471_);
v___x_1464_ = v___x_1459_;
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
else
{
lean_dec(v___x_1459_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1466_; lean_object* v___x_1468_; 
v___x_1466_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1460_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 0, v___x_1466_);
v___x_1468_ = v___x_1464_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1466_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
else
{
lean_dec(v_a_1460_);
return v___x_1459_;
}
}
}
else
{
return v___x_1459_;
}
}
}
else
{
lean_dec_ref(v_fallback_1428_);
lean_dec_ref(v_inst_x27_1427_);
lean_dec_ref(v_h_1426_);
lean_dec_ref(v_c_x27_1425_);
lean_dec_ref(v_b_1424_);
lean_dec_ref(v_a_1423_);
lean_dec_ref(v_inst_1422_);
lean_dec_ref(v_c_1421_);
lean_dec_ref(v_00_u03b1_1420_);
return v___x_1439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr___boxed(lean_object** _args){
lean_object* v_f_1474_ = _args[0];
lean_object* v_00_u03b1_1475_ = _args[1];
lean_object* v_c_1476_ = _args[2];
lean_object* v_inst_1477_ = _args[3];
lean_object* v_a_1478_ = _args[4];
lean_object* v_b_1479_ = _args[5];
lean_object* v_c_x27_1480_ = _args[6];
lean_object* v_h_1481_ = _args[7];
lean_object* v_inst_x27_1482_ = _args[8];
lean_object* v_fallback_1483_ = _args[9];
lean_object* v_a_1484_ = _args[10];
lean_object* v_a_1485_ = _args[11];
lean_object* v_a_1486_ = _args[12];
lean_object* v_a_1487_ = _args[13];
lean_object* v_a_1488_ = _args[14];
lean_object* v_a_1489_ = _args[15];
lean_object* v_a_1490_ = _args[16];
lean_object* v_a_1491_ = _args[17];
lean_object* v_a_1492_ = _args[18];
lean_object* v_a_1493_ = _args[19];
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr(v_f_1474_, v_00_u03b1_1475_, v_c_1476_, v_inst_1477_, v_a_1478_, v_b_1479_, v_c_x27_1480_, v_h_1481_, v_inst_x27_1482_, v_fallback_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
lean_dec(v_a_1488_);
lean_dec_ref(v_a_1487_);
lean_dec(v_a_1486_);
lean_dec_ref(v_a_1485_);
lean_dec(v_a_1484_);
lean_dec_ref(v_f_1474_);
return v_res_1494_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = lean_unsigned_to_nat(0u);
v___x_1499_ = l_Lean_mkBVar(v___x_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1(lean_object* v_proof_1505_, lean_object* v___x_1506_, lean_object* v_arg_1507_, lean_object* v_e_x27_1508_, lean_object* v_arg_1509_, uint8_t v_a_1510_, lean_object* v_arg_1511_, lean_object* v___x_1512_, lean_object* v___x_1513_, lean_object* v_e_1514_, uint8_t v___x_1515_, uint8_t v_contextDependent_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v___x_1527_; 
v___x_1527_ = l_Lean_Meta_Sym_shareCommon___redArg(v_proof_1505_, v___y_1521_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_a_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc_n(v_a_1528_, 2);
lean_dec_ref(v___x_1527_);
v___x_1529_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__1));
v___x_1530_ = 0;
v___x_1531_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2));
lean_inc(v___x_1506_);
v___x_1532_ = l_Lean_mkConst(v___x_1531_, v___x_1506_);
v___x_1533_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__2);
lean_inc_ref_n(v_e_x27_1508_, 2);
lean_inc_ref(v_arg_1507_);
v___x_1534_ = l_Lean_mkApp4(v___x_1532_, v_arg_1507_, v_e_x27_1508_, v_a_1528_, v___x_1533_);
v___x_1535_ = lean_unsigned_to_nat(1u);
v___x_1536_ = lean_mk_empty_array_with_capacity(v___x_1535_);
lean_inc_ref(v___x_1536_);
v___x_1537_ = lean_array_push(v___x_1536_, v___x_1534_);
v___x_1538_ = l_Lean_Expr_betaRev(v_arg_1509_, v___x_1537_, v_a_1510_, v_a_1510_);
lean_dec_ref(v___x_1537_);
v___x_1539_ = l_Lean_mkLambda(v___x_1529_, v___x_1530_, v_e_x27_1508_, v___x_1538_);
v___x_1540_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_1539_, v___y_1521_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref(v___x_1540_);
lean_inc_ref_n(v_e_x27_1508_, 2);
v___x_1542_ = l_Lean_mkNot(v_e_x27_1508_);
v___x_1543_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7));
v___x_1544_ = l_Lean_mkConst(v___x_1543_, v___x_1506_);
lean_inc(v_a_1528_);
v___x_1545_ = l_Lean_mkApp4(v___x_1544_, v_arg_1507_, v_e_x27_1508_, v_a_1528_, v___x_1533_);
v___x_1546_ = lean_array_push(v___x_1536_, v___x_1545_);
v___x_1547_ = l_Lean_Expr_betaRev(v_arg_1511_, v___x_1546_, v_a_1510_, v_a_1510_);
lean_dec_ref(v___x_1546_);
v___x_1548_ = l_Lean_mkLambda(v___x_1529_, v___x_1530_, v___x_1542_, v___x_1547_);
v___x_1549_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_1548_, v___y_1521_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1551_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref(v___x_1549_);
lean_inc_ref(v___x_1513_);
lean_inc_ref(v_e_x27_1508_);
v___x_1551_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(v___x_1512_, v_e_x27_1508_, v___x_1513_, v_a_1541_, v_a_1550_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1563_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1554_ = v___x_1551_;
v_isShared_1555_ = v_isSharedCheck_1563_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1551_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1563_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1561_; 
v___x_1556_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__4));
v___x_1557_ = l_Lean_Expr_replaceFn(v_e_1514_, v___x_1556_);
v___x_1558_ = l_Lean_mkApp3(v___x_1557_, v_e_x27_1508_, v___x_1513_, v_a_1528_);
v___x_1559_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1559_, 0, v_a_1552_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
lean_ctor_set_uint8(v___x_1559_, sizeof(void*)*2, v___x_1515_);
lean_ctor_set_uint8(v___x_1559_, sizeof(void*)*2 + 1, v_contextDependent_1516_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 0, v___x_1559_);
v___x_1561_ = v___x_1554_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1559_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec(v_a_1528_);
lean_dec_ref(v_e_1514_);
lean_dec_ref(v___x_1513_);
lean_dec_ref(v_e_x27_1508_);
v_a_1564_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1551_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1551_);
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
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_dec(v_a_1541_);
lean_dec(v_a_1528_);
lean_dec_ref(v_e_1514_);
lean_dec_ref(v___x_1513_);
lean_dec_ref(v___x_1512_);
lean_dec_ref(v_e_x27_1508_);
v_a_1572_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1549_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1549_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec_ref(v___x_1536_);
lean_dec(v_a_1528_);
lean_dec_ref(v_e_1514_);
lean_dec_ref(v___x_1513_);
lean_dec_ref(v___x_1512_);
lean_dec_ref(v_arg_1511_);
lean_dec_ref(v_e_x27_1508_);
lean_dec_ref(v_arg_1507_);
lean_dec(v___x_1506_);
v_a_1580_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1540_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1540_);
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
lean_dec_ref(v_e_1514_);
lean_dec_ref(v___x_1513_);
lean_dec_ref(v___x_1512_);
lean_dec_ref(v_arg_1511_);
lean_dec_ref(v_arg_1509_);
lean_dec_ref(v_e_x27_1508_);
lean_dec_ref(v_arg_1507_);
lean_dec(v___x_1506_);
v_a_1588_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1527_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1527_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___boxed(lean_object** _args){
lean_object* v_proof_1596_ = _args[0];
lean_object* v___x_1597_ = _args[1];
lean_object* v_arg_1598_ = _args[2];
lean_object* v_e_x27_1599_ = _args[3];
lean_object* v_arg_1600_ = _args[4];
lean_object* v_a_1601_ = _args[5];
lean_object* v_arg_1602_ = _args[6];
lean_object* v___x_1603_ = _args[7];
lean_object* v___x_1604_ = _args[8];
lean_object* v_e_1605_ = _args[9];
lean_object* v___x_1606_ = _args[10];
lean_object* v_contextDependent_1607_ = _args[11];
lean_object* v___y_1608_ = _args[12];
lean_object* v___y_1609_ = _args[13];
lean_object* v___y_1610_ = _args[14];
lean_object* v___y_1611_ = _args[15];
lean_object* v___y_1612_ = _args[16];
lean_object* v___y_1613_ = _args[17];
lean_object* v___y_1614_ = _args[18];
lean_object* v___y_1615_ = _args[19];
lean_object* v___y_1616_ = _args[20];
lean_object* v___y_1617_ = _args[21];
_start:
{
uint8_t v_a_32592__boxed_1618_; uint8_t v___x_32596__boxed_1619_; uint8_t v_contextDependent_32597__boxed_1620_; lean_object* v_res_1621_; 
v_a_32592__boxed_1618_ = lean_unbox(v_a_1601_);
v___x_32596__boxed_1619_ = lean_unbox(v___x_1606_);
v_contextDependent_32597__boxed_1620_ = lean_unbox(v_contextDependent_1607_);
v_res_1621_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1(v_proof_1596_, v___x_1597_, v_arg_1598_, v_e_x27_1599_, v_arg_1600_, v_a_32592__boxed_1618_, v_arg_1602_, v___x_1603_, v___x_1604_, v_e_1605_, v___x_32596__boxed_1619_, v_contextDependent_32597__boxed_1620_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
return v_res_1621_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1628_ = lean_box(0);
v___x_1629_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
v___x_1630_ = l_Lean_mkConst(v___x_1629_, v___x_1628_);
return v___x_1630_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1631_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4);
v___x_1632_ = lean_unsigned_to_nat(1u);
v___x_1633_ = lean_mk_empty_array_with_capacity(v___x_1632_);
v___x_1634_ = lean_array_push(v___x_1633_, v___x_1631_);
return v___x_1634_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10(void){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1642_ = lean_box(0);
v___x_1643_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9));
v___x_1644_ = l_Lean_mkConst(v___x_1643_, v___x_1642_);
return v___x_1644_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11(void){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1645_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10);
v___x_1646_ = lean_unsigned_to_nat(1u);
v___x_1647_ = lean_mk_empty_array_with_capacity(v___x_1646_);
v___x_1648_ = lean_array_push(v___x_1647_, v___x_1645_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0(uint8_t v___x_1657_, lean_object* v_e_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v___x_1672_; uint8_t v___x_1673_; 
lean_inc_ref(v_e_1658_);
v___x_1672_ = l_Lean_Expr_cleanupAnnotations(v_e_1658_);
v___x_1673_ = l_Lean_Expr_isApp(v___x_1672_);
if (v___x_1673_ == 0)
{
lean_dec_ref(v___x_1672_);
lean_dec_ref(v_e_1658_);
goto v___jp_1669_;
}
else
{
lean_object* v_arg_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; 
v_arg_1674_ = lean_ctor_get(v___x_1672_, 1);
lean_inc_ref(v_arg_1674_);
v___x_1675_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1672_);
v___x_1676_ = l_Lean_Expr_isApp(v___x_1675_);
if (v___x_1676_ == 0)
{
lean_dec_ref(v___x_1675_);
lean_dec_ref(v_arg_1674_);
lean_dec_ref(v_e_1658_);
goto v___jp_1669_;
}
else
{
lean_object* v_arg_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
v_arg_1677_ = lean_ctor_get(v___x_1675_, 1);
lean_inc_ref(v_arg_1677_);
v___x_1678_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1675_);
v___x_1679_ = l_Lean_Expr_isApp(v___x_1678_);
if (v___x_1679_ == 0)
{
lean_dec_ref(v___x_1678_);
lean_dec_ref(v_arg_1677_);
lean_dec_ref(v_arg_1674_);
lean_dec_ref(v_e_1658_);
goto v___jp_1669_;
}
else
{
lean_object* v_arg_1680_; lean_object* v___x_1681_; uint8_t v___x_1682_; 
v_arg_1680_ = lean_ctor_get(v___x_1678_, 1);
lean_inc_ref(v_arg_1680_);
v___x_1681_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1678_);
v___x_1682_ = l_Lean_Expr_isApp(v___x_1681_);
if (v___x_1682_ == 0)
{
lean_dec_ref(v___x_1681_);
lean_dec_ref(v_arg_1680_);
lean_dec_ref(v_arg_1677_);
lean_dec_ref(v_arg_1674_);
lean_dec_ref(v_e_1658_);
goto v___jp_1669_;
}
else
{
lean_object* v_arg_1683_; lean_object* v___x_1684_; uint8_t v___x_1685_; 
v_arg_1683_ = lean_ctor_get(v___x_1681_, 1);
lean_inc_ref(v_arg_1683_);
v___x_1684_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1681_);
v___x_1685_ = l_Lean_Expr_isApp(v___x_1684_);
if (v___x_1685_ == 0)
{
lean_dec_ref(v___x_1684_);
lean_dec_ref(v_arg_1683_);
lean_dec_ref(v_arg_1680_);
lean_dec_ref(v_arg_1677_);
lean_dec_ref(v_arg_1674_);
lean_dec_ref(v_e_1658_);
goto v___jp_1669_;
}
else
{
lean_object* v_arg_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; uint8_t v___x_1689_; 
v_arg_1686_ = lean_ctor_get(v___x_1684_, 1);
lean_inc_ref(v_arg_1686_);
v___x_1687_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1684_);
v___x_1688_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1));
v___x_1689_ = l_Lean_Expr_isConstOf(v___x_1687_, v___x_1688_);
if (v___x_1689_ == 0)
{
lean_dec_ref(v___x_1687_);
lean_dec_ref(v_arg_1686_);
lean_dec_ref(v_arg_1683_);
lean_dec_ref(v_arg_1680_);
lean_dec_ref(v_arg_1677_);
lean_dec_ref(v_arg_1674_);
lean_dec_ref(v_e_1658_);
goto v___jp_1669_;
}
else
{
lean_object* v___x_1690_; 
lean_inc(v___y_1667_);
lean_inc_ref(v___y_1666_);
lean_inc(v___y_1665_);
lean_inc_ref(v___y_1664_);
lean_inc(v___y_1663_);
lean_inc_ref(v___y_1662_);
lean_inc(v___y_1661_);
lean_inc_ref(v___y_1660_);
lean_inc(v___y_1659_);
lean_inc_ref(v_arg_1683_);
v___x_1690_ = lean_sym_simp(v_arg_1683_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_a_1691_);
lean_dec_ref(v___x_1690_);
if (lean_obj_tag(v_a_1691_) == 0)
{
uint8_t v_contextDependent_1692_; lean_object* v___x_1693_; 
lean_dec_ref(v_e_1658_);
v_contextDependent_1692_ = lean_ctor_get_uint8(v_a_1691_, 1);
lean_dec_ref(v_a_1691_);
v___x_1693_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_1683_, v___y_1662_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; uint8_t v___x_1695_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
lean_dec_ref(v___x_1693_);
v___x_1695_ = lean_unbox(v_a_1694_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_1683_, v___y_1662_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; uint8_t v___x_1698_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1697_);
lean_dec_ref(v___x_1696_);
v___x_1698_ = lean_unbox(v_a_1697_);
lean_dec(v_a_1697_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; lean_object* v___f_1700_; lean_object* v___x_1701_; 
lean_dec(v_a_1694_);
v___x_1699_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_1689_, v_contextDependent_1692_);
v___f_1700_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1700_, 0, v___x_1699_);
v___x_1701_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(v___x_1687_, v_arg_1686_, v_arg_1683_, v_arg_1680_, v_arg_1677_, v_arg_1674_, v___f_1700_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
lean_dec_ref(v___x_1687_);
return v___x_1701_;
}
else
{
lean_object* v___x_1702_; uint8_t v___x_1703_; uint8_t v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
lean_dec_ref(v_arg_1683_);
lean_dec_ref(v_arg_1680_);
v___x_1702_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5);
v___x_1703_ = lean_unbox(v_a_1694_);
v___x_1704_ = lean_unbox(v_a_1694_);
lean_inc_ref(v_arg_1674_);
v___x_1705_ = l_Lean_Expr_betaRev(v_arg_1674_, v___x_1702_, v___x_1703_, v___x_1704_);
v___x_1706_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_1705_, v___y_1663_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1720_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1709_ = v___x_1706_;
v_isShared_1710_ = v_isSharedCheck_1720_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1706_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1720_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; lean_object* v___x_1718_; 
v___x_1711_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6));
v___x_1712_ = l_Lean_Expr_constLevels_x21(v___x_1687_);
lean_dec_ref(v___x_1687_);
v___x_1713_ = l_Lean_mkConst(v___x_1711_, v___x_1712_);
v___x_1714_ = l_Lean_mkApp3(v___x_1713_, v_arg_1686_, v_arg_1677_, v_arg_1674_);
v___x_1715_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1715_, 0, v_a_1707_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
v___x_1716_ = lean_unbox(v_a_1694_);
lean_dec(v_a_1694_);
lean_ctor_set_uint8(v___x_1715_, sizeof(void*)*2, v___x_1716_);
lean_ctor_set_uint8(v___x_1715_, sizeof(void*)*2 + 1, v_contextDependent_1692_);
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v___x_1715_);
v___x_1718_ = v___x_1709_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1715_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_dec(v_a_1694_);
lean_dec_ref(v___x_1687_);
lean_dec_ref(v_arg_1686_);
lean_dec_ref(v_arg_1677_);
lean_dec_ref(v_arg_1674_);
v_a_1721_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1706_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1706_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
lean_dec(v_a_1694_);
lean_dec_ref(v___x_1687_);
lean_dec_ref(v_arg_1686_);
lean_dec_ref(v_arg_1683_);
lean_dec_ref(v_arg_1680_);
lean_dec_ref(v_arg_1677_);
lean_dec_ref(v_arg_1674_);
v_a_1729_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1696_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1696_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
else
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_dec(v_a_1694_);
lean_dec_ref(v_arg_1683_);
lean_dec_ref(v_arg_1680_);
v___x_1737_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11);
lean_inc_ref(v_arg_1677_);
v___x_1738_ = l_Lean_Expr_betaRev(v_arg_1677_, v___x_1737_, v___x_1657_, v___x_1657_);
v___x_1739_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_1738_, v___y_1663_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1752_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1742_ = v___x_1739_;
v_isShared_1743_ = v_isSharedCheck_1752_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1739_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1752_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1750_; 
v___x_1744_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12));
v___x_1745_ = l_Lean_Expr_constLevels_x21(v___x_1687_);
lean_dec_ref(v___x_1687_);
v___x_1746_ = l_Lean_mkConst(v___x_1744_, v___x_1745_);
v___x_1747_ = l_Lean_mkApp3(v___x_1746_, v_arg_1686_, v_arg_1677_, v_arg_1674_);
v___x_1748_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1748_, 0, v_a_1740_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
lean_ctor_set_uint8(v___x_1748_, sizeof(void*)*2, v___x_1657_);
lean_ctor_set_uint8(v___x_1748_, sizeof(void*)*2 + 1, v_contextDependent_1692_);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 0, v___x_1748_);
v___x_1750_ = v___x_1742_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1748_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_dec_ref(v___x_1687_);
lean_dec_ref(v_arg_1686_);
lean_dec_ref(v_arg_1677_);
lean_dec_ref(v_arg_1674_);
v_a_1753_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1739_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1739_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_dec_ref(v___x_1687_);
lean_dec_ref(v_arg_1686_);
lean_dec_ref(v_arg_1683_);
lean_dec_ref(v_arg_1680_);
lean_dec_ref(v_arg_1677_);
lean_dec_ref(v_arg_1674_);
v_a_1761_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1693_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1693_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
else
{
lean_object* v_e_x27_1769_; lean_object* v_proof_1770_; uint8_t v_contextDependent_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1886_; 
v_e_x27_1769_ = lean_ctor_get(v_a_1691_, 0);
v_proof_1770_ = lean_ctor_get(v_a_1691_, 1);
v_contextDependent_1771_ = lean_ctor_get_uint8(v_a_1691_, sizeof(void*)*2 + 1);
v_isSharedCheck_1886_ = !lean_is_exclusive(v_a_1691_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1773_ = v_a_1691_;
v_isShared_1774_ = v_isSharedCheck_1886_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_proof_1770_);
lean_inc(v_e_x27_1769_);
lean_dec(v_a_1691_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1886_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; 
v___x_1775_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_1769_, v___y_1662_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; uint8_t v___x_1777_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1776_);
lean_dec_ref(v___x_1775_);
v___x_1777_ = lean_unbox(v_a_1776_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_1769_, v___y_1662_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; uint8_t v___x_1780_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_a_1779_);
lean_dec_ref(v___x_1778_);
v___x_1780_ = lean_unbox(v_a_1779_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___f_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_dec(v_a_1776_);
lean_del_object(v___x_1773_);
v___x_1781_ = lean_box(0);
v___x_1782_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6);
lean_inc_ref_n(v_proof_1770_, 2);
lean_inc_ref_n(v_arg_1680_, 2);
lean_inc_ref_n(v_e_x27_1769_, 2);
lean_inc_ref_n(v_arg_1683_, 3);
v___x_1783_ = l_Lean_mkApp4(v___x_1782_, v_arg_1683_, v_e_x27_1769_, v_arg_1680_, v_proof_1770_);
v___x_1784_ = lean_unsigned_to_nat(4u);
v___x_1785_ = l_Lean_Expr_getBoundedAppFn(v___x_1784_, v_e_1658_);
v___x_1786_ = lean_box(v___x_1689_);
v___x_1787_ = lean_box(v_contextDependent_1771_);
lean_inc_ref(v___x_1783_);
lean_inc_ref_n(v_arg_1674_, 2);
lean_inc_ref_n(v_arg_1677_, 2);
v___f_1788_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___boxed), 22, 12);
lean_closure_set(v___f_1788_, 0, v_proof_1770_);
lean_closure_set(v___f_1788_, 1, v___x_1781_);
lean_closure_set(v___f_1788_, 2, v_arg_1683_);
lean_closure_set(v___f_1788_, 3, v_e_x27_1769_);
lean_closure_set(v___f_1788_, 4, v_arg_1677_);
lean_closure_set(v___f_1788_, 5, v_a_1779_);
lean_closure_set(v___f_1788_, 6, v_arg_1674_);
lean_closure_set(v___f_1788_, 7, v___x_1785_);
lean_closure_set(v___f_1788_, 8, v___x_1783_);
lean_closure_set(v___f_1788_, 9, v_e_1658_);
lean_closure_set(v___f_1788_, 10, v___x_1786_);
lean_closure_set(v___f_1788_, 11, v___x_1787_);
lean_inc_ref(v_arg_1686_);
lean_inc_ref(v___x_1687_);
v___x_1789_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr___boxed), 20, 10);
lean_closure_set(v___x_1789_, 0, v___x_1687_);
lean_closure_set(v___x_1789_, 1, v_arg_1686_);
lean_closure_set(v___x_1789_, 2, v_arg_1683_);
lean_closure_set(v___x_1789_, 3, v_arg_1680_);
lean_closure_set(v___x_1789_, 4, v_arg_1677_);
lean_closure_set(v___x_1789_, 5, v_arg_1674_);
lean_closure_set(v___x_1789_, 6, v_e_x27_1769_);
lean_closure_set(v___x_1789_, 7, v_proof_1770_);
lean_closure_set(v___x_1789_, 8, v___x_1783_);
lean_closure_set(v___x_1789_, 9, v___f_1788_);
v___x_1790_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(v___x_1687_, v_arg_1686_, v_arg_1683_, v_arg_1680_, v_arg_1677_, v_arg_1674_, v___x_1789_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
lean_dec_ref(v___x_1687_);
return v___x_1790_;
}
else
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
lean_dec(v_a_1779_);
lean_dec_ref(v_e_x27_1769_);
lean_dec_ref(v___x_1687_);
lean_dec_ref(v_arg_1686_);
lean_dec_ref(v_arg_1680_);
lean_dec_ref(v_arg_1677_);
lean_inc_ref(v_proof_1770_);
v___x_1791_ = l_Lean_Meta_mkOfEqFalseCore(v_arg_1683_, v_proof_1770_);
v___x_1792_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_1791_, v___y_1663_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; uint8_t v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1793_);
lean_dec_ref(v___x_1792_);
v___x_1794_ = lean_unsigned_to_nat(1u);
v___x_1795_ = lean_mk_empty_array_with_capacity(v___x_1794_);
v___x_1796_ = lean_array_push(v___x_1795_, v_a_1793_);
v___x_1797_ = lean_unbox(v_a_1776_);
v___x_1798_ = lean_unbox(v_a_1776_);
v___x_1799_ = l_Lean_Expr_betaRev(v_arg_1674_, v___x_1796_, v___x_1797_, v___x_1798_);
lean_dec_ref(v___x_1796_);
v___x_1800_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_1799_, v___y_1663_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1815_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1803_ = v___x_1800_;
v_isShared_1804_ = v_isSharedCheck_1815_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1800_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1815_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1809_; 
v___x_1805_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14));
v___x_1806_ = l_Lean_Expr_replaceFn(v_e_1658_, v___x_1805_);
v___x_1807_ = l_Lean_Expr_app___override(v___x_1806_, v_proof_1770_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 1, v___x_1807_);
lean_ctor_set(v___x_1773_, 0, v_a_1801_);
v___x_1809_ = v___x_1773_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1801_);
lean_ctor_set(v_reuseFailAlloc_1814_, 1, v___x_1807_);
v___x_1809_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
uint8_t v___x_1810_; lean_object* v___x_1812_; 
v___x_1810_ = lean_unbox(v_a_1776_);
lean_dec(v_a_1776_);
lean_ctor_set_uint8(v___x_1809_, sizeof(void*)*2, v___x_1810_);
lean_ctor_set_uint8(v___x_1809_, sizeof(void*)*2 + 1, v_contextDependent_1771_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 0, v___x_1809_);
v___x_1812_ = v___x_1803_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1809_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
else
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
lean_dec(v_a_1776_);
lean_del_object(v___x_1773_);
lean_dec_ref(v_proof_1770_);
lean_dec_ref(v_e_1658_);
v_a_1816_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1818_ = v___x_1800_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1800_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
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
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
lean_dec(v_a_1776_);
lean_del_object(v___x_1773_);
lean_dec_ref(v_proof_1770_);
lean_dec_ref(v_arg_1674_);
lean_dec_ref(v_e_1658_);
v_a_1824_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1792_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1792_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_dec(v_a_1776_);
lean_del_object(v___x_1773_);
lean_dec_ref(v_proof_1770_);
lean_dec_ref(v_e_x27_1769_);
lean_dec_ref(v___x_1687_);
lean_dec_ref(v_arg_1686_);
lean_dec_ref(v_arg_1683_);
lean_dec_ref(v_arg_1680_);
lean_dec_ref(v_arg_1677_);
lean_dec_ref(v_arg_1674_);
lean_dec_ref(v_e_1658_);
v_a_1832_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1778_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1778_);
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
lean_object* v___x_1840_; lean_object* v___x_1841_; 
lean_dec(v_a_1776_);
lean_dec_ref(v_e_x27_1769_);
lean_dec_ref(v___x_1687_);
lean_dec_ref(v_arg_1686_);
lean_dec_ref(v_arg_1680_);
lean_dec_ref(v_arg_1674_);
lean_inc_ref(v_proof_1770_);
v___x_1840_ = l_Lean_Meta_mkOfEqTrueCore(v_arg_1683_, v_proof_1770_);
v___x_1841_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_1840_, v___y_1663_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref(v___x_1841_);
v___x_1843_ = lean_unsigned_to_nat(1u);
v___x_1844_ = lean_mk_empty_array_with_capacity(v___x_1843_);
v___x_1845_ = lean_array_push(v___x_1844_, v_a_1842_);
v___x_1846_ = l_Lean_Expr_betaRev(v_arg_1677_, v___x_1845_, v___x_1657_, v___x_1657_);
lean_dec_ref(v___x_1845_);
v___x_1847_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_1846_, v___y_1663_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1861_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1850_ = v___x_1847_;
v_isShared_1851_ = v_isSharedCheck_1861_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1847_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1861_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1852_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16));
v___x_1853_ = l_Lean_Expr_replaceFn(v_e_1658_, v___x_1852_);
v___x_1854_ = l_Lean_Expr_app___override(v___x_1853_, v_proof_1770_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 1, v___x_1854_);
lean_ctor_set(v___x_1773_, 0, v_a_1848_);
v___x_1856_ = v___x_1773_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1848_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v___x_1854_);
lean_ctor_set_uint8(v_reuseFailAlloc_1860_, sizeof(void*)*2 + 1, v_contextDependent_1771_);
v___x_1856_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1858_; 
lean_ctor_set_uint8(v___x_1856_, sizeof(void*)*2, v___x_1657_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1856_);
v___x_1858_ = v___x_1850_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1856_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_del_object(v___x_1773_);
lean_dec_ref(v_proof_1770_);
lean_dec_ref(v_e_1658_);
v_a_1862_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1847_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1847_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_del_object(v___x_1773_);
lean_dec_ref(v_proof_1770_);
lean_dec_ref(v_arg_1677_);
lean_dec_ref(v_e_1658_);
v_a_1870_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1841_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1841_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
lean_del_object(v___x_1773_);
lean_dec_ref(v_proof_1770_);
lean_dec_ref(v_e_x27_1769_);
lean_dec_ref(v___x_1687_);
lean_dec_ref(v_arg_1686_);
lean_dec_ref(v_arg_1683_);
lean_dec_ref(v_arg_1680_);
lean_dec_ref(v_arg_1677_);
lean_dec_ref(v_arg_1674_);
lean_dec_ref(v_e_1658_);
v_a_1878_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1880_ = v___x_1775_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1775_);
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
}
}
else
{
lean_dec_ref(v___x_1687_);
lean_dec_ref(v_arg_1686_);
lean_dec_ref(v_arg_1683_);
lean_dec_ref(v_arg_1680_);
lean_dec_ref(v_arg_1677_);
lean_dec_ref(v_arg_1674_);
lean_dec_ref(v_e_1658_);
return v___x_1690_;
}
}
}
}
}
}
}
v___jp_1669_:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1670_, 0, v___x_1657_);
lean_ctor_set_uint8(v___x_1670_, 1, v___x_1657_);
v___x_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
return v___x_1671_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___boxed(lean_object* v___x_1887_, lean_object* v_e_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
uint8_t v___x_32876__boxed_1899_; lean_object* v_res_1900_; 
v___x_32876__boxed_1899_ = lean_unbox(v___x_1887_);
v_res_1900_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0(v___x_32876__boxed_1899_, v_e_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv(lean_object* v_e_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_){
_start:
{
lean_object* v_numArgs_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; 
v_numArgs_1912_ = l_Lean_Expr_getAppNumArgs(v_e_1901_);
v___x_1913_ = lean_unsigned_to_nat(5u);
v___x_1914_ = lean_nat_dec_lt(v_numArgs_1912_, v___x_1913_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1915_; lean_object* v___f_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1915_ = lean_box(v___x_1914_);
v___f_1916_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___boxed), 12, 1);
lean_closure_set(v___f_1916_, 0, v___x_1915_);
v___x_1917_ = lean_nat_sub(v_numArgs_1912_, v___x_1913_);
lean_dec(v_numArgs_1912_);
v___x_1918_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_1901_, v___x_1917_, v___f_1916_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_);
lean_dec(v___x_1917_);
return v___x_1918_;
}
else
{
uint8_t v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
lean_dec(v_numArgs_1912_);
lean_dec_ref(v_e_1901_);
v___x_1919_ = 0;
v___x_1920_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1920_, 0, v___x_1914_);
lean_ctor_set_uint8(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
return v___x_1921_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___boxed(lean_object* v_e_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv(v_e_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_);
lean_dec(v_a_1931_);
lean_dec_ref(v_a_1930_);
lean_dec(v_a_1929_);
lean_dec_ref(v_a_1928_);
lean_dec(v_a_1927_);
lean_dec_ref(v_a_1926_);
lean_dec(v_a_1925_);
lean_dec_ref(v_a_1924_);
lean_dec(v_a_1923_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1952_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16_));
v___x_1953_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16_));
v___x_1954_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___boxed), 11, 0);
v___x_1955_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_1952_, v___x_1953_, v___x_1954_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16____boxed(lean_object* v_a_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16_();
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_18_(){
_start:
{
lean_object* v___x_1959_; uint8_t v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1959_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16_));
v___x_1960_ = 0;
v___x_1961_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___boxed), 11, 0);
v___x_1962_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_1959_, v___x_1960_, v___x_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_18____boxed(lean_object* v_a_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_18_();
return v_res_1964_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2(void){
_start:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1970_ = lean_box(0);
v___x_1971_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1));
v___x_1972_ = l_Lean_mkConst(v___x_1971_, v___x_1970_);
return v___x_1972_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5(void){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1978_ = lean_box(0);
v___x_1979_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4));
v___x_1980_ = l_Lean_mkConst(v___x_1979_, v___x_1978_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(lean_object* v_p_1981_, lean_object* v_inst_1982_, lean_object* v_instToMatch_1983_, lean_object* v_fallback_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_){
_start:
{
lean_object* v___x_1995_; 
v___x_1995_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_instToMatch_1983_, v_a_1991_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_a_1996_);
lean_dec_ref(v___x_1995_);
v___x_1997_ = l_Lean_Expr_cleanupAnnotations(v_a_1996_);
v___x_1998_ = l_Lean_Expr_isApp(v___x_1997_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; 
lean_dec_ref(v___x_1997_);
lean_dec_ref(v_inst_1982_);
lean_dec_ref(v_p_1981_);
lean_inc(v_a_1993_);
lean_inc_ref(v_a_1992_);
lean_inc(v_a_1991_);
lean_inc_ref(v_a_1990_);
lean_inc(v_a_1989_);
lean_inc_ref(v_a_1988_);
lean_inc(v_a_1987_);
lean_inc_ref(v_a_1986_);
lean_inc(v_a_1985_);
v___x_1999_ = lean_apply_10(v_fallback_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, lean_box(0));
return v___x_1999_;
}
else
{
lean_object* v_arg_2000_; lean_object* v___x_2001_; uint8_t v___x_2002_; 
v_arg_2000_ = lean_ctor_get(v___x_1997_, 1);
lean_inc_ref(v_arg_2000_);
v___x_2001_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1997_);
v___x_2002_ = l_Lean_Expr_isApp(v___x_2001_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; 
lean_dec_ref(v___x_2001_);
lean_dec_ref(v_arg_2000_);
lean_dec_ref(v_inst_1982_);
lean_dec_ref(v_p_1981_);
lean_inc(v_a_1993_);
lean_inc_ref(v_a_1992_);
lean_inc(v_a_1991_);
lean_inc_ref(v_a_1990_);
lean_inc(v_a_1989_);
lean_inc_ref(v_a_1988_);
lean_inc(v_a_1987_);
lean_inc_ref(v_a_1986_);
lean_inc(v_a_1985_);
v___x_2003_ = lean_apply_10(v_fallback_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, lean_box(0));
return v___x_2003_;
}
else
{
lean_object* v___x_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; 
v___x_2004_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2001_);
v___x_2005_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_2006_ = l_Lean_Expr_isConstOf(v___x_2004_, v___x_2005_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; uint8_t v___x_2008_; 
v___x_2007_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3));
v___x_2008_ = l_Lean_Expr_isConstOf(v___x_2004_, v___x_2007_);
lean_dec_ref(v___x_2004_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; 
lean_dec_ref(v_arg_2000_);
lean_dec_ref(v_inst_1982_);
lean_dec_ref(v_p_1981_);
lean_inc(v_a_1993_);
lean_inc_ref(v_a_1992_);
lean_inc(v_a_1991_);
lean_inc_ref(v_a_1990_);
lean_inc(v_a_1989_);
lean_inc_ref(v_a_1988_);
lean_inc(v_a_1987_);
lean_inc_ref(v_a_1986_);
lean_inc(v_a_1985_);
v___x_2009_ = lean_apply_10(v_fallback_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, lean_box(0));
return v___x_2009_;
}
else
{
lean_object* v___x_2010_; 
lean_dec_ref(v_fallback_1984_);
v___x_2010_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_1988_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2021_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2013_ = v___x_2010_;
v_isShared_2014_ = v_isSharedCheck_2021_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2010_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2021_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2019_; 
v___x_2015_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2);
v___x_2016_ = l_Lean_mkApp3(v___x_2015_, v_p_1981_, v_inst_1982_, v_arg_2000_);
v___x_2017_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2017_, 0, v_a_2011_);
lean_ctor_set(v___x_2017_, 1, v___x_2016_);
lean_ctor_set_uint8(v___x_2017_, sizeof(void*)*2, v___x_2006_);
lean_ctor_set_uint8(v___x_2017_, sizeof(void*)*2 + 1, v___x_2006_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 0, v___x_2017_);
v___x_2019_ = v___x_2013_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2017_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_dec_ref(v_arg_2000_);
lean_dec_ref(v_inst_1982_);
lean_dec_ref(v_p_1981_);
v_a_2022_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_2010_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2010_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
}
else
{
lean_object* v___x_2030_; 
lean_dec_ref(v___x_2004_);
lean_dec_ref(v_fallback_1984_);
v___x_2030_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_1988_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2042_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2033_ = v___x_2030_;
v_isShared_2034_ = v_isSharedCheck_2042_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2030_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2042_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2040_; 
v___x_2035_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5);
v___x_2036_ = l_Lean_mkApp3(v___x_2035_, v_p_1981_, v_inst_1982_, v_arg_2000_);
v___x_2037_ = 0;
v___x_2038_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2038_, 0, v_a_2031_);
lean_ctor_set(v___x_2038_, 1, v___x_2036_);
lean_ctor_set_uint8(v___x_2038_, sizeof(void*)*2, v___x_2037_);
lean_ctor_set_uint8(v___x_2038_, sizeof(void*)*2 + 1, v___x_2037_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 0, v___x_2038_);
v___x_2040_ = v___x_2033_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_dec_ref(v_arg_2000_);
lean_dec_ref(v_inst_1982_);
lean_dec_ref(v_p_1981_);
v_a_2043_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_2030_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2030_);
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
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec_ref(v_fallback_1984_);
lean_dec_ref(v_inst_1982_);
lean_dec_ref(v_p_1981_);
v_a_2051_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_1995_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_1995_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___boxed(lean_object* v_p_2059_, lean_object* v_inst_2060_, lean_object* v_instToMatch_2061_, lean_object* v_fallback_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(v_p_2059_, v_inst_2060_, v_instToMatch_2061_, v_fallback_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
lean_dec(v_a_2071_);
lean_dec_ref(v_a_2070_);
lean_dec(v_a_2069_);
lean_dec_ref(v_a_2068_);
lean_dec(v_a_2067_);
lean_dec_ref(v_a_2066_);
lean_dec(v_a_2065_);
lean_dec_ref(v_a_2064_);
lean_dec(v_a_2063_);
return v_res_2073_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = lean_box(0);
v___x_2080_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1));
v___x_2081_ = l_Lean_mkConst(v___x_2080_, v___x_2079_);
return v___x_2081_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5(void){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2087_ = lean_box(0);
v___x_2088_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4));
v___x_2089_ = l_Lean_mkConst(v___x_2088_, v___x_2087_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(lean_object* v_p_2090_, lean_object* v_p_x27_2091_, lean_object* v_h_2092_, lean_object* v_inst_2093_, lean_object* v_inst_x27_2094_, lean_object* v_fallback_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_){
_start:
{
lean_object* v___x_2106_; 
v___x_2106_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_inst_x27_2094_, v_a_2102_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2108_; uint8_t v___x_2109_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2107_);
lean_dec_ref(v___x_2106_);
v___x_2108_ = l_Lean_Expr_cleanupAnnotations(v_a_2107_);
v___x_2109_ = l_Lean_Expr_isApp(v___x_2108_);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; 
lean_dec_ref(v___x_2108_);
lean_dec_ref(v_inst_2093_);
lean_dec_ref(v_h_2092_);
lean_dec_ref(v_p_x27_2091_);
lean_dec_ref(v_p_2090_);
lean_inc(v_a_2104_);
lean_inc_ref(v_a_2103_);
lean_inc(v_a_2102_);
lean_inc_ref(v_a_2101_);
lean_inc(v_a_2100_);
lean_inc_ref(v_a_2099_);
lean_inc(v_a_2098_);
lean_inc_ref(v_a_2097_);
lean_inc(v_a_2096_);
v___x_2110_ = lean_apply_10(v_fallback_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, lean_box(0));
return v___x_2110_;
}
else
{
lean_object* v_arg_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v_arg_2111_ = lean_ctor_get(v___x_2108_, 1);
lean_inc_ref(v_arg_2111_);
v___x_2112_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2108_);
v___x_2113_ = l_Lean_Expr_isApp(v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; 
lean_dec_ref(v___x_2112_);
lean_dec_ref(v_arg_2111_);
lean_dec_ref(v_inst_2093_);
lean_dec_ref(v_h_2092_);
lean_dec_ref(v_p_x27_2091_);
lean_dec_ref(v_p_2090_);
lean_inc(v_a_2104_);
lean_inc_ref(v_a_2103_);
lean_inc(v_a_2102_);
lean_inc_ref(v_a_2101_);
lean_inc(v_a_2100_);
lean_inc_ref(v_a_2099_);
lean_inc(v_a_2098_);
lean_inc_ref(v_a_2097_);
lean_inc(v_a_2096_);
v___x_2114_ = lean_apply_10(v_fallback_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, lean_box(0));
return v___x_2114_;
}
else
{
lean_object* v___x_2115_; lean_object* v___x_2116_; uint8_t v___x_2117_; 
v___x_2115_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2112_);
v___x_2116_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_2117_ = l_Lean_Expr_isConstOf(v___x_2115_, v___x_2116_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; uint8_t v___x_2119_; 
v___x_2118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3));
v___x_2119_ = l_Lean_Expr_isConstOf(v___x_2115_, v___x_2118_);
lean_dec_ref(v___x_2115_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; 
lean_dec_ref(v_arg_2111_);
lean_dec_ref(v_inst_2093_);
lean_dec_ref(v_h_2092_);
lean_dec_ref(v_p_x27_2091_);
lean_dec_ref(v_p_2090_);
lean_inc(v_a_2104_);
lean_inc_ref(v_a_2103_);
lean_inc(v_a_2102_);
lean_inc_ref(v_a_2101_);
lean_inc(v_a_2100_);
lean_inc_ref(v_a_2099_);
lean_inc(v_a_2098_);
lean_inc_ref(v_a_2097_);
lean_inc(v_a_2096_);
v___x_2120_ = lean_apply_10(v_fallback_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, lean_box(0));
return v___x_2120_;
}
else
{
lean_object* v___x_2121_; 
lean_dec_ref(v_fallback_2095_);
v___x_2121_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_2099_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2132_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2124_ = v___x_2121_;
v_isShared_2125_ = v_isSharedCheck_2132_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2121_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2132_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2130_; 
v___x_2126_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2);
v___x_2127_ = l_Lean_mkApp5(v___x_2126_, v_p_2090_, v_p_x27_2091_, v_h_2092_, v_inst_2093_, v_arg_2111_);
v___x_2128_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2128_, 0, v_a_2122_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
lean_ctor_set_uint8(v___x_2128_, sizeof(void*)*2, v___x_2117_);
lean_ctor_set_uint8(v___x_2128_, sizeof(void*)*2 + 1, v___x_2117_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v___x_2128_);
v___x_2130_ = v___x_2124_;
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
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec_ref(v_arg_2111_);
lean_dec_ref(v_inst_2093_);
lean_dec_ref(v_h_2092_);
lean_dec_ref(v_p_x27_2091_);
lean_dec_ref(v_p_2090_);
v_a_2133_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2121_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2121_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
else
{
lean_object* v___x_2141_; 
lean_dec_ref(v___x_2115_);
lean_dec_ref(v_fallback_2095_);
v___x_2141_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_2099_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2153_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2144_ = v___x_2141_;
v_isShared_2145_ = v_isSharedCheck_2153_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2141_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2153_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; uint8_t v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2151_; 
v___x_2146_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5);
v___x_2147_ = l_Lean_mkApp5(v___x_2146_, v_p_2090_, v_p_x27_2091_, v_h_2092_, v_inst_2093_, v_arg_2111_);
v___x_2148_ = 0;
v___x_2149_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2149_, 0, v_a_2142_);
lean_ctor_set(v___x_2149_, 1, v___x_2147_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*2, v___x_2148_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*2 + 1, v___x_2148_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 0, v___x_2149_);
v___x_2151_ = v___x_2144_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2149_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec_ref(v_arg_2111_);
lean_dec_ref(v_inst_2093_);
lean_dec_ref(v_h_2092_);
lean_dec_ref(v_p_x27_2091_);
lean_dec_ref(v_p_2090_);
v_a_2154_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2141_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2141_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec_ref(v_fallback_2095_);
lean_dec_ref(v_inst_2093_);
lean_dec_ref(v_h_2092_);
lean_dec_ref(v_p_x27_2091_);
lean_dec_ref(v_p_2090_);
v_a_2162_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2106_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2106_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___boxed(lean_object* v_p_2170_, lean_object* v_p_x27_2171_, lean_object* v_h_2172_, lean_object* v_inst_2173_, lean_object* v_inst_x27_2174_, lean_object* v_fallback_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(v_p_2170_, v_p_x27_2171_, v_h_2172_, v_inst_2173_, v_inst_x27_2174_, v_fallback_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_);
lean_dec(v_a_2184_);
lean_dec_ref(v_a_2183_);
lean_dec(v_a_2182_);
lean_dec_ref(v_a_2181_);
lean_dec(v_a_2180_);
lean_dec_ref(v_a_2179_);
lean_dec(v_a_2178_);
lean_dec_ref(v_a_2177_);
lean_dec(v_a_2176_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(lean_object* v_p_2187_, lean_object* v_inst_2188_, lean_object* v_fallback_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_){
_start:
{
lean_object* v___x_2200_; 
lean_inc(v_a_2198_);
lean_inc_ref(v_a_2197_);
lean_inc(v_a_2196_);
lean_inc_ref(v_a_2195_);
lean_inc(v_a_2194_);
lean_inc_ref(v_a_2193_);
lean_inc(v_a_2192_);
lean_inc_ref(v_a_2191_);
lean_inc(v_a_2190_);
lean_inc_ref(v_inst_2188_);
v___x_2200_ = lean_sym_simp(v_inst_2188_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_a_2201_);
lean_dec_ref(v___x_2200_);
if (lean_obj_tag(v_a_2201_) == 0)
{
uint8_t v_contextDependent_2202_; lean_object* v___x_2203_; 
v_contextDependent_2202_ = lean_ctor_get_uint8(v_a_2201_, 1);
lean_dec_ref(v_a_2201_);
lean_inc_ref(v_inst_2188_);
v___x_2203_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(v_p_2187_, v_inst_2188_, v_inst_2188_, v_fallback_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; uint8_t v___y_2206_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_a_2204_);
if (v_contextDependent_2202_ == 0)
{
lean_dec(v_a_2204_);
return v___x_2203_;
}
else
{
if (lean_obj_tag(v_a_2204_) == 0)
{
uint8_t v_contextDependent_2216_; 
v_contextDependent_2216_ = lean_ctor_get_uint8(v_a_2204_, 1);
v___y_2206_ = v_contextDependent_2216_;
goto v___jp_2205_;
}
else
{
uint8_t v_contextDependent_2217_; 
v_contextDependent_2217_ = lean_ctor_get_uint8(v_a_2204_, sizeof(void*)*2 + 1);
v___y_2206_ = v_contextDependent_2217_;
goto v___jp_2205_;
}
}
v___jp_2205_:
{
if (v___y_2206_ == 0)
{
lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2214_; 
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2214_ == 0)
{
lean_object* v_unused_2215_; 
v_unused_2215_ = lean_ctor_get(v___x_2203_, 0);
lean_dec(v_unused_2215_);
v___x_2208_ = v___x_2203_;
v_isShared_2209_ = v_isSharedCheck_2214_;
goto v_resetjp_2207_;
}
else
{
lean_dec(v___x_2203_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2214_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2210_; lean_object* v___x_2212_; 
v___x_2210_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2204_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v___x_2210_);
v___x_2212_ = v___x_2208_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
else
{
lean_dec(v_a_2204_);
return v___x_2203_;
}
}
}
else
{
return v___x_2203_;
}
}
else
{
lean_object* v_e_x27_2218_; uint8_t v_contextDependent_2219_; lean_object* v___x_2220_; 
v_e_x27_2218_ = lean_ctor_get(v_a_2201_, 0);
lean_inc_ref(v_e_x27_2218_);
v_contextDependent_2219_ = lean_ctor_get_uint8(v_a_2201_, sizeof(void*)*2 + 1);
lean_dec_ref(v_a_2201_);
v___x_2220_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(v_p_2187_, v_inst_2188_, v_e_x27_2218_, v_fallback_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; uint8_t v___y_2223_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_a_2221_);
if (v_contextDependent_2219_ == 0)
{
lean_dec(v_a_2221_);
return v___x_2220_;
}
else
{
if (lean_obj_tag(v_a_2221_) == 0)
{
uint8_t v_contextDependent_2233_; 
v_contextDependent_2233_ = lean_ctor_get_uint8(v_a_2221_, 1);
v___y_2223_ = v_contextDependent_2233_;
goto v___jp_2222_;
}
else
{
uint8_t v_contextDependent_2234_; 
v_contextDependent_2234_ = lean_ctor_get_uint8(v_a_2221_, sizeof(void*)*2 + 1);
v___y_2223_ = v_contextDependent_2234_;
goto v___jp_2222_;
}
}
v___jp_2222_:
{
if (v___y_2223_ == 0)
{
lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2231_; 
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2231_ == 0)
{
lean_object* v_unused_2232_; 
v_unused_2232_ = lean_ctor_get(v___x_2220_, 0);
lean_dec(v_unused_2232_);
v___x_2225_ = v___x_2220_;
v_isShared_2226_ = v_isSharedCheck_2231_;
goto v_resetjp_2224_;
}
else
{
lean_dec(v___x_2220_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2231_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2227_; lean_object* v___x_2229_; 
v___x_2227_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2221_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v___x_2227_);
v___x_2229_ = v___x_2225_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2227_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
else
{
lean_dec(v_a_2221_);
return v___x_2220_;
}
}
}
else
{
return v___x_2220_;
}
}
}
else
{
lean_dec_ref(v_fallback_2189_);
lean_dec_ref(v_inst_2188_);
lean_dec_ref(v_p_2187_);
return v___x_2200_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable___boxed(lean_object* v_p_2235_, lean_object* v_inst_2236_, lean_object* v_fallback_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(v_p_2235_, v_inst_2236_, v_fallback_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_);
lean_dec(v_a_2246_);
lean_dec_ref(v_a_2245_);
lean_dec(v_a_2244_);
lean_dec_ref(v_a_2243_);
lean_dec(v_a_2242_);
lean_dec_ref(v_a_2241_);
lean_dec(v_a_2240_);
lean_dec_ref(v_a_2239_);
lean_dec(v_a_2238_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr(lean_object* v_p_2249_, lean_object* v_p_x27_2250_, lean_object* v_h_2251_, lean_object* v_inst_2252_, lean_object* v_inst_x27_2253_, lean_object* v_fallback_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_){
_start:
{
lean_object* v___x_2265_; 
lean_inc(v_a_2263_);
lean_inc_ref(v_a_2262_);
lean_inc(v_a_2261_);
lean_inc_ref(v_a_2260_);
lean_inc(v_a_2259_);
lean_inc_ref(v_a_2258_);
lean_inc(v_a_2257_);
lean_inc_ref(v_a_2256_);
lean_inc(v_a_2255_);
lean_inc_ref(v_inst_x27_2253_);
v___x_2265_ = lean_sym_simp(v_inst_x27_2253_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2266_);
lean_dec_ref(v___x_2265_);
if (lean_obj_tag(v_a_2266_) == 0)
{
uint8_t v_contextDependent_2267_; lean_object* v___x_2268_; 
v_contextDependent_2267_ = lean_ctor_get_uint8(v_a_2266_, 1);
lean_dec_ref(v_a_2266_);
v___x_2268_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(v_p_2249_, v_p_x27_2250_, v_h_2251_, v_inst_2252_, v_inst_x27_2253_, v_fallback_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; uint8_t v___y_2271_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_a_2269_);
if (v_contextDependent_2267_ == 0)
{
lean_dec(v_a_2269_);
return v___x_2268_;
}
else
{
if (lean_obj_tag(v_a_2269_) == 0)
{
uint8_t v_contextDependent_2281_; 
v_contextDependent_2281_ = lean_ctor_get_uint8(v_a_2269_, 1);
v___y_2271_ = v_contextDependent_2281_;
goto v___jp_2270_;
}
else
{
uint8_t v_contextDependent_2282_; 
v_contextDependent_2282_ = lean_ctor_get_uint8(v_a_2269_, sizeof(void*)*2 + 1);
v___y_2271_ = v_contextDependent_2282_;
goto v___jp_2270_;
}
}
v___jp_2270_:
{
if (v___y_2271_ == 0)
{
lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2279_; 
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2279_ == 0)
{
lean_object* v_unused_2280_; 
v_unused_2280_ = lean_ctor_get(v___x_2268_, 0);
lean_dec(v_unused_2280_);
v___x_2273_ = v___x_2268_;
v_isShared_2274_ = v_isSharedCheck_2279_;
goto v_resetjp_2272_;
}
else
{
lean_dec(v___x_2268_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2279_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2275_; lean_object* v___x_2277_; 
v___x_2275_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2269_);
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 0, v___x_2275_);
v___x_2277_ = v___x_2273_;
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
}
else
{
lean_dec(v_a_2269_);
return v___x_2268_;
}
}
}
else
{
return v___x_2268_;
}
}
else
{
lean_object* v_e_x27_2283_; uint8_t v_contextDependent_2284_; lean_object* v___x_2285_; 
lean_dec_ref(v_inst_x27_2253_);
v_e_x27_2283_ = lean_ctor_get(v_a_2266_, 0);
lean_inc_ref(v_e_x27_2283_);
v_contextDependent_2284_ = lean_ctor_get_uint8(v_a_2266_, sizeof(void*)*2 + 1);
lean_dec_ref(v_a_2266_);
v___x_2285_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(v_p_2249_, v_p_x27_2250_, v_h_2251_, v_inst_2252_, v_e_x27_2283_, v_fallback_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; uint8_t v___y_2288_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
if (v_contextDependent_2284_ == 0)
{
lean_dec(v_a_2286_);
return v___x_2285_;
}
else
{
if (lean_obj_tag(v_a_2286_) == 0)
{
uint8_t v_contextDependent_2298_; 
v_contextDependent_2298_ = lean_ctor_get_uint8(v_a_2286_, 1);
v___y_2288_ = v_contextDependent_2298_;
goto v___jp_2287_;
}
else
{
uint8_t v_contextDependent_2299_; 
v_contextDependent_2299_ = lean_ctor_get_uint8(v_a_2286_, sizeof(void*)*2 + 1);
v___y_2288_ = v_contextDependent_2299_;
goto v___jp_2287_;
}
}
v___jp_2287_:
{
if (v___y_2288_ == 0)
{
lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2296_; 
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2296_ == 0)
{
lean_object* v_unused_2297_; 
v_unused_2297_ = lean_ctor_get(v___x_2285_, 0);
lean_dec(v_unused_2297_);
v___x_2290_ = v___x_2285_;
v_isShared_2291_ = v_isSharedCheck_2296_;
goto v_resetjp_2289_;
}
else
{
lean_dec(v___x_2285_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2296_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2292_; lean_object* v___x_2294_; 
v___x_2292_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2286_);
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 0, v___x_2292_);
v___x_2294_ = v___x_2290_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v___x_2292_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
else
{
lean_dec(v_a_2286_);
return v___x_2285_;
}
}
}
else
{
return v___x_2285_;
}
}
}
else
{
lean_dec_ref(v_fallback_2254_);
lean_dec_ref(v_inst_x27_2253_);
lean_dec_ref(v_inst_2252_);
lean_dec_ref(v_h_2251_);
lean_dec_ref(v_p_x27_2250_);
lean_dec_ref(v_p_2249_);
return v___x_2265_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___boxed(lean_object* v_p_2300_, lean_object* v_p_x27_2301_, lean_object* v_h_2302_, lean_object* v_inst_2303_, lean_object* v_inst_x27_2304_, lean_object* v_fallback_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr(v_p_2300_, v_p_x27_2301_, v_h_2302_, v_inst_2303_, v_inst_x27_2304_, v_fallback_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
lean_dec(v_a_2310_);
lean_dec_ref(v_a_2309_);
lean_dec(v_a_2308_);
lean_dec_ref(v_a_2307_);
lean_dec(v_a_2306_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1(lean_object* v___x_2318_, lean_object* v_e_x27_2319_, lean_object* v___y_2320_, lean_object* v___x_2321_, lean_object* v___x_2322_, lean_object* v___x_2323_, lean_object* v_arg_2324_, lean_object* v_proof_2325_, lean_object* v_arg_2326_, uint8_t v___x_2327_, uint8_t v_contextDependent_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_2318_, v___y_2333_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2341_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref(v___x_2339_);
lean_inc_ref(v___y_2320_);
lean_inc_ref(v_e_x27_2319_);
v___x_2341_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1(v_a_2340_, v_e_x27_2319_, v___y_2320_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2354_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2344_ = v___x_2341_;
v_isShared_2345_ = v_isSharedCheck_2354_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2341_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2354_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2352_; 
v___x_2346_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1___closed__0));
v___x_2347_ = l_Lean_Name_mkStr3(v___x_2321_, v___x_2322_, v___x_2346_);
v___x_2348_ = l_Lean_mkConst(v___x_2347_, v___x_2323_);
v___x_2349_ = l_Lean_mkApp5(v___x_2348_, v_arg_2324_, v_e_x27_2319_, v_proof_2325_, v_arg_2326_, v___y_2320_);
v___x_2350_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2350_, 0, v_a_2342_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
lean_ctor_set_uint8(v___x_2350_, sizeof(void*)*2, v___x_2327_);
lean_ctor_set_uint8(v___x_2350_, sizeof(void*)*2 + 1, v_contextDependent_2328_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 0, v___x_2350_);
v___x_2352_ = v___x_2344_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2350_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec_ref(v_arg_2326_);
lean_dec_ref(v_proof_2325_);
lean_dec_ref(v_arg_2324_);
lean_dec(v___x_2323_);
lean_dec_ref(v___x_2322_);
lean_dec_ref(v___x_2321_);
lean_dec_ref(v___y_2320_);
lean_dec_ref(v_e_x27_2319_);
v_a_2355_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2341_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2341_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
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
lean_dec_ref(v_arg_2326_);
lean_dec_ref(v_proof_2325_);
lean_dec_ref(v_arg_2324_);
lean_dec(v___x_2323_);
lean_dec_ref(v___x_2322_);
lean_dec_ref(v___x_2321_);
lean_dec_ref(v___y_2320_);
lean_dec_ref(v_e_x27_2319_);
v_a_2363_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2339_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2339_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1___boxed(lean_object** _args){
lean_object* v___x_2371_ = _args[0];
lean_object* v_e_x27_2372_ = _args[1];
lean_object* v___y_2373_ = _args[2];
lean_object* v___x_2374_ = _args[3];
lean_object* v___x_2375_ = _args[4];
lean_object* v___x_2376_ = _args[5];
lean_object* v_arg_2377_ = _args[6];
lean_object* v_proof_2378_ = _args[7];
lean_object* v_arg_2379_ = _args[8];
lean_object* v___x_2380_ = _args[9];
lean_object* v_contextDependent_2381_ = _args[10];
lean_object* v___y_2382_ = _args[11];
lean_object* v___y_2383_ = _args[12];
lean_object* v___y_2384_ = _args[13];
lean_object* v___y_2385_ = _args[14];
lean_object* v___y_2386_ = _args[15];
lean_object* v___y_2387_ = _args[16];
lean_object* v___y_2388_ = _args[17];
lean_object* v___y_2389_ = _args[18];
lean_object* v___y_2390_ = _args[19];
lean_object* v___y_2391_ = _args[20];
_start:
{
uint8_t v___x_23749__boxed_2392_; uint8_t v_contextDependent_23750__boxed_2393_; lean_object* v_res_2394_; 
v___x_23749__boxed_2392_ = lean_unbox(v___x_2380_);
v_contextDependent_23750__boxed_2393_ = lean_unbox(v_contextDependent_2381_);
v_res_2394_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1(v___x_2371_, v_e_x27_2372_, v___y_2373_, v___x_2374_, v___x_2375_, v___x_2376_, v_arg_2377_, v_proof_2378_, v_arg_2379_, v___x_23749__boxed_2392_, v_contextDependent_23750__boxed_2393_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
return v_res_2394_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2402_ = lean_box(0);
v___x_2403_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__3));
v___x_2404_ = l_Lean_mkConst(v___x_2403_, v___x_2402_);
return v___x_2404_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2408_ = lean_box(0);
v___x_2409_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__6));
v___x_2410_ = l_Lean_mkConst(v___x_2409_, v___x_2408_);
return v___x_2410_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2411_ = lean_box(0);
v___x_2412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1));
v___x_2413_ = l_Lean_mkConst(v___x_2412_, v___x_2411_);
return v___x_2413_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11(void){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2419_ = lean_box(0);
v___x_2420_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10));
v___x_2421_ = l_Lean_mkConst(v___x_2420_, v___x_2419_);
return v___x_2421_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__14(void){
_start:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2427_ = lean_box(0);
v___x_2428_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__13));
v___x_2429_ = l_Lean_mkConst(v___x_2428_, v___x_2427_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0(uint8_t v___x_2430_, lean_object* v_e_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v___x_2445_; uint8_t v___x_2446_; 
v___x_2445_ = l_Lean_Expr_cleanupAnnotations(v_e_2431_);
v___x_2446_ = l_Lean_Expr_isApp(v___x_2445_);
if (v___x_2446_ == 0)
{
lean_dec_ref(v___x_2445_);
goto v___jp_2442_;
}
else
{
lean_object* v_arg_2447_; lean_object* v___x_2448_; uint8_t v___x_2449_; 
v_arg_2447_ = lean_ctor_get(v___x_2445_, 1);
lean_inc_ref(v_arg_2447_);
v___x_2448_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2445_);
v___x_2449_ = l_Lean_Expr_isApp(v___x_2448_);
if (v___x_2449_ == 0)
{
lean_dec_ref(v___x_2448_);
lean_dec_ref(v_arg_2447_);
goto v___jp_2442_;
}
else
{
lean_object* v_arg_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; uint8_t v___x_2455_; 
v_arg_2450_ = lean_ctor_get(v___x_2448_, 1);
lean_inc_ref(v_arg_2450_);
v___x_2451_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2448_);
v___x_2452_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__0));
v___x_2453_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__0));
v___x_2454_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1));
v___x_2455_ = l_Lean_Expr_isConstOf(v___x_2451_, v___x_2454_);
lean_dec_ref(v___x_2451_);
if (v___x_2455_ == 0)
{
lean_dec_ref(v_arg_2450_);
lean_dec_ref(v_arg_2447_);
goto v___jp_2442_;
}
else
{
lean_object* v___x_2456_; 
lean_inc(v___y_2440_);
lean_inc_ref(v___y_2439_);
lean_inc(v___y_2438_);
lean_inc_ref(v___y_2437_);
lean_inc(v___y_2436_);
lean_inc_ref(v___y_2435_);
lean_inc(v___y_2434_);
lean_inc_ref(v___y_2433_);
lean_inc(v___y_2432_);
lean_inc_ref(v_arg_2450_);
v___x_2456_ = lean_sym_simp(v_arg_2450_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_a_2457_);
lean_dec_ref(v___x_2456_);
if (lean_obj_tag(v_a_2457_) == 0)
{
uint8_t v_contextDependent_2458_; lean_object* v___x_2459_; 
v_contextDependent_2458_ = lean_ctor_get_uint8(v_a_2457_, 1);
lean_dec_ref(v_a_2457_);
v___x_2459_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_2450_, v___y_2435_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; uint8_t v___x_2461_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_a_2460_);
lean_dec_ref(v___x_2459_);
v___x_2461_ = lean_unbox(v_a_2460_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; 
v___x_2462_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_2450_, v___y_2435_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; uint8_t v___x_2464_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc(v_a_2463_);
lean_dec_ref(v___x_2462_);
v___x_2464_ = lean_unbox(v_a_2463_);
lean_dec(v_a_2463_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2465_; lean_object* v___f_2466_; lean_object* v___x_2467_; 
lean_dec(v_a_2460_);
v___x_2465_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_2455_, v_contextDependent_2458_);
v___f_2466_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2466_, 0, v___x_2465_);
v___x_2467_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(v_arg_2450_, v_arg_2447_, v___f_2466_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
return v___x_2467_;
}
else
{
lean_object* v___x_2468_; 
lean_dec_ref(v_arg_2450_);
v___x_2468_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v___y_2435_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2480_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2471_ = v___x_2468_;
v_isShared_2472_ = v_isSharedCheck_2480_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2468_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2480_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; uint8_t v___x_2476_; lean_object* v___x_2478_; 
v___x_2473_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__4, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__4);
v___x_2474_ = l_Lean_Expr_app___override(v___x_2473_, v_arg_2447_);
v___x_2475_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2475_, 0, v_a_2469_);
lean_ctor_set(v___x_2475_, 1, v___x_2474_);
v___x_2476_ = lean_unbox(v_a_2460_);
lean_dec(v_a_2460_);
lean_ctor_set_uint8(v___x_2475_, sizeof(void*)*2, v___x_2476_);
lean_ctor_set_uint8(v___x_2475_, sizeof(void*)*2 + 1, v_contextDependent_2458_);
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 0, v___x_2475_);
v___x_2478_ = v___x_2471_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2475_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_dec(v_a_2460_);
lean_dec_ref(v_arg_2447_);
v_a_2481_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2468_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2468_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
}
else
{
lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2496_; 
lean_dec(v_a_2460_);
lean_dec_ref(v_arg_2450_);
lean_dec_ref(v_arg_2447_);
v_a_2489_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2491_ = v___x_2462_;
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2462_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2489_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
}
else
{
lean_object* v___x_2497_; 
lean_dec(v_a_2460_);
lean_dec_ref(v_arg_2450_);
v___x_2497_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v___y_2435_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2508_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2500_ = v___x_2497_;
v_isShared_2501_ = v_isSharedCheck_2508_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2497_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2508_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2506_; 
v___x_2502_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7);
v___x_2503_ = l_Lean_Expr_app___override(v___x_2502_, v_arg_2447_);
v___x_2504_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2504_, 0, v_a_2498_);
lean_ctor_set(v___x_2504_, 1, v___x_2503_);
lean_ctor_set_uint8(v___x_2504_, sizeof(void*)*2, v___x_2430_);
lean_ctor_set_uint8(v___x_2504_, sizeof(void*)*2 + 1, v_contextDependent_2458_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 0, v___x_2504_);
v___x_2506_ = v___x_2500_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v___x_2504_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
lean_dec_ref(v_arg_2447_);
v_a_2509_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___x_2497_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2497_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2524_; 
lean_dec_ref(v_arg_2450_);
lean_dec_ref(v_arg_2447_);
v_a_2517_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2519_ = v___x_2459_;
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2459_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2522_; 
if (v_isShared_2520_ == 0)
{
v___x_2522_ = v___x_2519_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_a_2517_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
}
else
{
lean_object* v_e_x27_2525_; lean_object* v_proof_2526_; uint8_t v_contextDependent_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2619_; 
v_e_x27_2525_ = lean_ctor_get(v_a_2457_, 0);
v_proof_2526_ = lean_ctor_get(v_a_2457_, 1);
v_contextDependent_2527_ = lean_ctor_get_uint8(v_a_2457_, sizeof(void*)*2 + 1);
v_isSharedCheck_2619_ = !lean_is_exclusive(v_a_2457_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2529_ = v_a_2457_;
v_isShared_2530_ = v_isSharedCheck_2619_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_proof_2526_);
lean_inc(v_e_x27_2525_);
lean_dec(v_a_2457_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2619_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2531_; 
v___x_2531_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_2525_, v___y_2435_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; uint8_t v___x_2533_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_a_2532_);
lean_dec_ref(v___x_2531_);
v___x_2533_ = lean_unbox(v_a_2532_);
if (v___x_2533_ == 0)
{
lean_object* v___x_2534_; 
v___x_2534_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_2525_, v___y_2435_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v_a_2535_; uint8_t v___x_2536_; 
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc(v_a_2535_);
lean_dec_ref(v___x_2534_);
v___x_2536_ = lean_unbox(v_a_2535_);
lean_dec(v_a_2535_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2537_; 
lean_dec(v_a_2532_);
lean_del_object(v___x_2529_);
lean_inc_ref(v_e_x27_2525_);
v___x_2537_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance(v_e_x27_2525_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v_a_2538_; lean_object* v___y_2540_; 
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc(v_a_2538_);
lean_dec_ref(v___x_2537_);
if (lean_obj_tag(v_a_2538_) == 0)
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2547_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6);
lean_inc_ref(v_proof_2526_);
lean_inc_ref(v_arg_2447_);
lean_inc_ref(v_e_x27_2525_);
lean_inc_ref(v_arg_2450_);
v___x_2548_ = l_Lean_mkApp4(v___x_2547_, v_arg_2450_, v_e_x27_2525_, v_arg_2447_, v_proof_2526_);
v___y_2540_ = v___x_2548_;
goto v___jp_2539_;
}
else
{
lean_object* v_val_2549_; 
v_val_2549_ = lean_ctor_get(v_a_2538_, 0);
lean_inc(v_val_2549_);
lean_dec_ref(v_a_2538_);
v___y_2540_ = v_val_2549_;
goto v___jp_2539_;
}
v___jp_2539_:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___f_2545_; lean_object* v___x_2546_; 
v___x_2541_ = lean_box(0);
v___x_2542_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8);
v___x_2543_ = lean_box(v___x_2455_);
v___x_2544_ = lean_box(v_contextDependent_2527_);
lean_inc_ref(v_arg_2447_);
lean_inc_ref(v_proof_2526_);
lean_inc_ref(v_arg_2450_);
lean_inc_ref(v___y_2540_);
lean_inc_ref(v_e_x27_2525_);
v___f_2545_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1___boxed), 21, 11);
lean_closure_set(v___f_2545_, 0, v___x_2542_);
lean_closure_set(v___f_2545_, 1, v_e_x27_2525_);
lean_closure_set(v___f_2545_, 2, v___y_2540_);
lean_closure_set(v___f_2545_, 3, v___x_2452_);
lean_closure_set(v___f_2545_, 4, v___x_2453_);
lean_closure_set(v___f_2545_, 5, v___x_2541_);
lean_closure_set(v___f_2545_, 6, v_arg_2450_);
lean_closure_set(v___f_2545_, 7, v_proof_2526_);
lean_closure_set(v___f_2545_, 8, v_arg_2447_);
lean_closure_set(v___f_2545_, 9, v___x_2543_);
lean_closure_set(v___f_2545_, 10, v___x_2544_);
v___x_2546_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr(v_arg_2450_, v_e_x27_2525_, v_proof_2526_, v_arg_2447_, v___y_2540_, v___f_2545_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
return v___x_2546_;
}
}
else
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2557_; 
lean_dec_ref(v_proof_2526_);
lean_dec_ref(v_e_x27_2525_);
lean_dec_ref(v_arg_2450_);
lean_dec_ref(v_arg_2447_);
v_a_2550_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2552_ = v___x_2537_;
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2537_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
if (v_isShared_2553_ == 0)
{
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2550_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
else
{
lean_object* v___x_2558_; 
lean_dec_ref(v_e_x27_2525_);
v___x_2558_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v___y_2435_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2572_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2561_ = v___x_2558_;
v_isShared_2562_ = v_isSharedCheck_2572_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2558_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2572_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2566_; 
v___x_2563_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11);
v___x_2564_ = l_Lean_mkApp3(v___x_2563_, v_arg_2450_, v_arg_2447_, v_proof_2526_);
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 1, v___x_2564_);
lean_ctor_set(v___x_2529_, 0, v_a_2559_);
v___x_2566_ = v___x_2529_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2559_);
lean_ctor_set(v_reuseFailAlloc_2571_, 1, v___x_2564_);
v___x_2566_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
uint8_t v___x_2567_; lean_object* v___x_2569_; 
v___x_2567_ = lean_unbox(v_a_2532_);
lean_dec(v_a_2532_);
lean_ctor_set_uint8(v___x_2566_, sizeof(void*)*2, v___x_2567_);
lean_ctor_set_uint8(v___x_2566_, sizeof(void*)*2 + 1, v_contextDependent_2527_);
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v___x_2566_);
v___x_2569_ = v___x_2561_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v___x_2566_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
lean_dec(v_a_2532_);
lean_del_object(v___x_2529_);
lean_dec_ref(v_proof_2526_);
lean_dec_ref(v_arg_2450_);
lean_dec_ref(v_arg_2447_);
v_a_2573_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2575_ = v___x_2558_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2558_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2573_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
}
else
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
lean_dec(v_a_2532_);
lean_del_object(v___x_2529_);
lean_dec_ref(v_proof_2526_);
lean_dec_ref(v_e_x27_2525_);
lean_dec_ref(v_arg_2450_);
lean_dec_ref(v_arg_2447_);
v_a_2581_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2583_ = v___x_2534_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2534_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2581_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
else
{
lean_object* v___x_2589_; 
lean_dec(v_a_2532_);
lean_dec_ref(v_e_x27_2525_);
v___x_2589_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v___y_2435_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2602_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2592_ = v___x_2589_;
v_isShared_2593_ = v_isSharedCheck_2602_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2589_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2602_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2597_; 
v___x_2594_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__14, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__14_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__14);
v___x_2595_ = l_Lean_mkApp3(v___x_2594_, v_arg_2450_, v_arg_2447_, v_proof_2526_);
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 1, v___x_2595_);
lean_ctor_set(v___x_2529_, 0, v_a_2590_);
v___x_2597_ = v___x_2529_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2590_);
lean_ctor_set(v_reuseFailAlloc_2601_, 1, v___x_2595_);
lean_ctor_set_uint8(v_reuseFailAlloc_2601_, sizeof(void*)*2 + 1, v_contextDependent_2527_);
v___x_2597_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
lean_object* v___x_2599_; 
lean_ctor_set_uint8(v___x_2597_, sizeof(void*)*2, v___x_2430_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 0, v___x_2597_);
v___x_2599_ = v___x_2592_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2597_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
else
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
lean_del_object(v___x_2529_);
lean_dec_ref(v_proof_2526_);
lean_dec_ref(v_arg_2450_);
lean_dec_ref(v_arg_2447_);
v_a_2603_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v___x_2589_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2589_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
lean_del_object(v___x_2529_);
lean_dec_ref(v_proof_2526_);
lean_dec_ref(v_e_x27_2525_);
lean_dec_ref(v_arg_2450_);
lean_dec_ref(v_arg_2447_);
v_a_2611_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2531_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2531_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_arg_2450_);
lean_dec_ref(v_arg_2447_);
return v___x_2456_;
}
}
}
}
v___jp_2442_:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2443_, 0, v___x_2430_);
lean_ctor_set_uint8(v___x_2443_, 1, v___x_2430_);
v___x_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
return v___x_2444_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___boxed(lean_object* v___x_2620_, lean_object* v_e_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
uint8_t v___x_23949__boxed_2632_; lean_object* v_res_2633_; 
v___x_23949__boxed_2632_ = lean_unbox(v___x_2620_);
v_res_2633_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0(v___x_23949__boxed_2632_, v_e_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv(lean_object* v_e_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_){
_start:
{
lean_object* v_numArgs_2645_; lean_object* v___x_2646_; uint8_t v___x_2647_; 
v_numArgs_2645_ = l_Lean_Expr_getAppNumArgs(v_e_2634_);
v___x_2646_ = lean_unsigned_to_nat(2u);
v___x_2647_ = lean_nat_dec_lt(v_numArgs_2645_, v___x_2646_);
if (v___x_2647_ == 0)
{
lean_object* v___x_2648_; lean_object* v___f_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2648_ = lean_box(v___x_2647_);
v___f_2649_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___boxed), 12, 1);
lean_closure_set(v___f_2649_, 0, v___x_2648_);
v___x_2650_ = lean_nat_sub(v_numArgs_2645_, v___x_2646_);
lean_dec(v_numArgs_2645_);
v___x_2651_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_2634_, v___x_2650_, v___f_2649_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_);
lean_dec(v___x_2650_);
return v___x_2651_;
}
else
{
uint8_t v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
lean_dec(v_numArgs_2645_);
lean_dec_ref(v_e_2634_);
v___x_2652_ = 0;
v___x_2653_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2653_, 0, v___x_2647_);
lean_ctor_set_uint8(v___x_2653_, 1, v___x_2652_);
v___x_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2653_);
return v___x_2654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___boxed(lean_object* v_e_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv(v_e_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_);
lean_dec(v_a_2664_);
lean_dec_ref(v_a_2663_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
lean_dec(v_a_2658_);
lean_dec_ref(v_a_2657_);
lean_dec(v_a_2656_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13_(){
_start:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2682_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13_));
v___x_2683_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13_));
v___x_2684_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___boxed), 11, 0);
v___x_2685_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_2682_, v___x_2683_, v___x_2684_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13____boxed(lean_object* v_a_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13_();
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_15_(){
_start:
{
lean_object* v___x_2689_; uint8_t v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2689_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13_));
v___x_2690_ = 0;
v___x_2691_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___boxed), 11, 0);
v___x_2692_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_2689_, v___x_2690_, v___x_2691_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_15____boxed(lean_object* v_a_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_15_();
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(lean_object* v_declName_2695_, lean_object* v___y_2696_){
_start:
{
lean_object* v___x_2698_; lean_object* v_env_2699_; uint8_t v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2698_ = lean_st_ref_get(v___y_2696_);
v_env_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc_ref(v_env_2699_);
lean_dec(v___x_2698_);
v___x_2700_ = lean_get_reducibility_status(v_env_2699_, v_declName_2695_);
v___x_2701_ = lean_box(v___x_2700_);
v___x_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg___boxed(lean_object* v_declName_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v_res_2706_; 
v_res_2706_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(v_declName_2703_, v___y_2704_);
lean_dec(v___y_2704_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1(lean_object* v_declName_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(v_declName_2707_, v___y_2709_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___boxed(lean_object* v_declName_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1(v_declName_2712_, v___y_2713_, v___y_2714_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0(lean_object* v_declName_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v___x_2721_; lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2737_; 
v___x_2721_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(v_declName_2717_, v___y_2719_);
v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2724_ = v___x_2721_;
v_isShared_2725_ = v_isSharedCheck_2737_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2721_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2737_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
uint8_t v___x_2726_; 
v___x_2726_ = lean_unbox(v_a_2722_);
lean_dec(v_a_2722_);
if (v___x_2726_ == 2)
{
uint8_t v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2730_; 
v___x_2727_ = 1;
v___x_2728_ = lean_box(v___x_2727_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 0, v___x_2728_);
v___x_2730_ = v___x_2724_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v___x_2728_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
else
{
uint8_t v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2735_; 
v___x_2732_ = 0;
v___x_2733_ = lean_box(v___x_2732_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 0, v___x_2733_);
v___x_2735_ = v___x_2724_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2733_);
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
}
LEAN_EXPORT lean_object* l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0___boxed(lean_object* v_declName_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0(v_declName_2738_, v___y_2739_, v___y_2740_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0(lean_object* v_canUnfold_x3f_2743_, lean_object* v_cfg_2744_, lean_object* v_info_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2749_ = l_Lean_ConstantInfo_name(v_info_2745_);
v___x_2750_ = l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(v___x_2749_, v___y_2747_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; uint8_t v___x_2752_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_a_2751_);
v___x_2752_ = lean_unbox(v_a_2751_);
if (v___x_2752_ == 0)
{
if (lean_obj_tag(v_canUnfold_x3f_2743_) == 0)
{
uint8_t v_transparency_2753_; uint8_t v___x_2754_; 
lean_dec_ref(v_info_2745_);
v_transparency_2753_ = lean_ctor_get_uint8(v_cfg_2744_, 9);
lean_dec_ref(v_cfg_2744_);
v___x_2754_ = 1;
switch(v_transparency_2753_)
{
case 4:
{
lean_dec(v_a_2751_);
lean_dec(v___x_2749_);
return v___x_2750_;
}
case 0:
{
lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2762_; 
lean_dec(v_a_2751_);
lean_dec(v___x_2749_);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2762_ == 0)
{
lean_object* v_unused_2763_; 
v_unused_2763_ = lean_ctor_get(v___x_2750_, 0);
lean_dec(v_unused_2763_);
v___x_2756_ = v___x_2750_;
v_isShared_2757_ = v_isSharedCheck_2762_;
goto v_resetjp_2755_;
}
else
{
lean_dec(v___x_2750_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2762_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2758_; lean_object* v___x_2760_; 
v___x_2758_ = lean_box(v___x_2754_);
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 0, v___x_2758_);
v___x_2760_ = v___x_2756_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v___x_2758_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
case 1:
{
lean_object* v___x_2764_; 
lean_dec_ref(v___x_2750_);
v___x_2764_ = l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0(v___x_2749_, v___y_2746_, v___y_2747_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2777_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2767_ = v___x_2764_;
v_isShared_2768_ = v_isSharedCheck_2777_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2764_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2777_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
uint8_t v___x_2769_; 
v___x_2769_ = lean_unbox(v_a_2765_);
lean_dec(v_a_2765_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; lean_object* v___x_2772_; 
lean_dec(v_a_2751_);
v___x_2770_ = lean_box(v___x_2754_);
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 0, v___x_2770_);
v___x_2772_ = v___x_2767_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2770_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
else
{
lean_object* v___x_2775_; 
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 0, v_a_2751_);
v___x_2775_ = v___x_2767_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2751_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
else
{
lean_dec(v_a_2751_);
return v___x_2764_;
}
}
default: 
{
lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2809_; 
lean_dec(v_a_2751_);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2809_ == 0)
{
lean_object* v_unused_2810_; 
v_unused_2810_ = lean_ctor_get(v___x_2750_, 0);
lean_dec(v_unused_2810_);
v___x_2779_ = v___x_2750_;
v_isShared_2780_ = v_isSharedCheck_2809_;
goto v_resetjp_2778_;
}
else
{
lean_dec(v___x_2750_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2809_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2781_; lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2808_; 
v___x_2781_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(v___x_2749_, v___y_2747_);
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2784_ = v___x_2781_;
v_isShared_2785_ = v_isSharedCheck_2808_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2781_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2808_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
uint8_t v___y_2787_; uint8_t v___x_2796_; uint8_t v___x_2797_; uint8_t v___x_2798_; 
v___x_2796_ = 0;
v___x_2797_ = lean_unbox(v_a_2782_);
v___x_2798_ = l_Lean_instBEqReducibilityStatus_beq(v___x_2797_, v___x_2796_);
if (v___x_2798_ == 0)
{
uint8_t v___x_2799_; uint8_t v___x_2800_; 
lean_del_object(v___x_2779_);
v___x_2799_ = 3;
v___x_2800_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2753_, v___x_2799_);
if (v___x_2800_ == 0)
{
lean_dec(v_a_2782_);
v___y_2787_ = v___x_2800_;
goto v___jp_2786_;
}
else
{
uint8_t v___x_2801_; uint8_t v___x_2802_; uint8_t v___x_2803_; 
v___x_2801_ = 3;
v___x_2802_ = lean_unbox(v_a_2782_);
lean_dec(v_a_2782_);
v___x_2803_ = l_Lean_instBEqReducibilityStatus_beq(v___x_2802_, v___x_2801_);
v___y_2787_ = v___x_2803_;
goto v___jp_2786_;
}
}
else
{
lean_object* v___x_2804_; lean_object* v___x_2806_; 
lean_del_object(v___x_2784_);
lean_dec(v_a_2782_);
v___x_2804_ = lean_box(v___x_2754_);
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 0, v___x_2804_);
v___x_2806_ = v___x_2779_;
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
v___jp_2786_:
{
if (v___y_2787_ == 0)
{
lean_object* v___x_2788_; lean_object* v___x_2790_; 
v___x_2788_ = lean_box(v___y_2787_);
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 0, v___x_2788_);
v___x_2790_ = v___x_2784_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v___x_2788_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
else
{
lean_object* v___x_2792_; lean_object* v___x_2794_; 
v___x_2792_ = lean_box(v___x_2754_);
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 0, v___x_2792_);
v___x_2794_ = v___x_2784_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___x_2792_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
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
lean_object* v_val_2811_; lean_object* v___x_2812_; 
lean_dec_ref(v___x_2750_);
lean_dec(v_a_2751_);
lean_dec(v___x_2749_);
v_val_2811_ = lean_ctor_get(v_canUnfold_x3f_2743_, 0);
lean_inc(v_val_2811_);
lean_dec_ref(v_canUnfold_x3f_2743_);
lean_inc(v___y_2747_);
lean_inc_ref(v___y_2746_);
v___x_2812_ = lean_apply_5(v_val_2811_, v_cfg_2744_, v_info_2745_, v___y_2746_, v___y_2747_, lean_box(0));
return v___x_2812_;
}
}
else
{
lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2821_; 
lean_dec(v_a_2751_);
lean_dec(v___x_2749_);
lean_dec_ref(v_info_2745_);
lean_dec_ref(v_cfg_2744_);
lean_dec(v_canUnfold_x3f_2743_);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2821_ == 0)
{
lean_object* v_unused_2822_; 
v_unused_2822_ = lean_ctor_get(v___x_2750_, 0);
lean_dec(v_unused_2822_);
v___x_2814_ = v___x_2750_;
v_isShared_2815_ = v_isSharedCheck_2821_;
goto v_resetjp_2813_;
}
else
{
lean_dec(v___x_2750_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2821_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
uint8_t v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2819_; 
v___x_2816_ = 0;
v___x_2817_ = lean_box(v___x_2816_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 0, v___x_2817_);
v___x_2819_ = v___x_2814_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v___x_2817_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
else
{
lean_dec(v___x_2749_);
lean_dec_ref(v_info_2745_);
lean_dec_ref(v_cfg_2744_);
lean_dec(v_canUnfold_x3f_2743_);
return v___x_2750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0___boxed(lean_object* v_canUnfold_x3f_2823_, lean_object* v_cfg_2824_, lean_object* v_info_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0(v_canUnfold_x3f_2823_, v_cfg_2824_, v_info_2825_, v___y_2826_, v___y_2827_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(lean_object* v_x_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_){
_start:
{
lean_object* v_keyedConfig_2836_; uint8_t v_trackZetaDelta_2837_; lean_object* v_zetaDeltaSet_2838_; lean_object* v_lctx_2839_; lean_object* v_localInstances_2840_; lean_object* v_defEqCtx_x3f_2841_; lean_object* v_synthPendingDepth_2842_; lean_object* v_canUnfold_x3f_2843_; uint8_t v_univApprox_2844_; uint8_t v_inTypeClassResolution_2845_; uint8_t v_cacheInferType_2846_; lean_object* v___f_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v_keyedConfig_2836_ = lean_ctor_get(v_a_2831_, 0);
v_trackZetaDelta_2837_ = lean_ctor_get_uint8(v_a_2831_, sizeof(void*)*7);
v_zetaDeltaSet_2838_ = lean_ctor_get(v_a_2831_, 1);
v_lctx_2839_ = lean_ctor_get(v_a_2831_, 2);
v_localInstances_2840_ = lean_ctor_get(v_a_2831_, 3);
v_defEqCtx_x3f_2841_ = lean_ctor_get(v_a_2831_, 4);
v_synthPendingDepth_2842_ = lean_ctor_get(v_a_2831_, 5);
v_canUnfold_x3f_2843_ = lean_ctor_get(v_a_2831_, 6);
v_univApprox_2844_ = lean_ctor_get_uint8(v_a_2831_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2845_ = lean_ctor_get_uint8(v_a_2831_, sizeof(void*)*7 + 2);
v_cacheInferType_2846_ = lean_ctor_get_uint8(v_a_2831_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_2843_);
v___f_2847_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_2847_, 0, v_canUnfold_x3f_2843_);
v___x_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2848_, 0, v___f_2847_);
lean_inc(v_synthPendingDepth_2842_);
lean_inc(v_defEqCtx_x3f_2841_);
lean_inc_ref(v_localInstances_2840_);
lean_inc_ref(v_lctx_2839_);
lean_inc(v_zetaDeltaSet_2838_);
lean_inc_ref(v_keyedConfig_2836_);
v___x_2849_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2849_, 0, v_keyedConfig_2836_);
lean_ctor_set(v___x_2849_, 1, v_zetaDeltaSet_2838_);
lean_ctor_set(v___x_2849_, 2, v_lctx_2839_);
lean_ctor_set(v___x_2849_, 3, v_localInstances_2840_);
lean_ctor_set(v___x_2849_, 4, v_defEqCtx_x3f_2841_);
lean_ctor_set(v___x_2849_, 5, v_synthPendingDepth_2842_);
lean_ctor_set(v___x_2849_, 6, v___x_2848_);
lean_ctor_set_uint8(v___x_2849_, sizeof(void*)*7, v_trackZetaDelta_2837_);
lean_ctor_set_uint8(v___x_2849_, sizeof(void*)*7 + 1, v_univApprox_2844_);
lean_ctor_set_uint8(v___x_2849_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2845_);
lean_ctor_set_uint8(v___x_2849_, sizeof(void*)*7 + 3, v_cacheInferType_2846_);
lean_inc(v_a_2834_);
lean_inc_ref(v_a_2833_);
lean_inc(v_a_2832_);
v___x_2850_ = lean_apply_5(v_x_2830_, v___x_2849_, v_a_2832_, v_a_2833_, v_a_2834_, lean_box(0));
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___boxed(lean_object* v_x_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v_x_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_);
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2854_);
lean_dec(v_a_2853_);
lean_dec_ref(v_a_2852_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard(lean_object* v_00_u03b1_2858_, lean_object* v_x_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_){
_start:
{
lean_object* v___x_2865_; 
v___x_2865_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v_x_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___boxed(lean_object* v_00_u03b1_2866_, lean_object* v_x_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard(v_00_u03b1_2866_, v_x_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_);
lean_dec(v_a_2871_);
lean_dec_ref(v_a_2870_);
lean_dec(v_a_2869_);
lean_dec_ref(v_a_2868_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond(lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_){
_start:
{
lean_object* v___x_2885_; 
v___x_2885_ = l_Lean_Meta_Sym_Simp_simpCond(v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___boxed(lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond(v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_);
lean_dec(v_a_2895_);
lean_dec_ref(v_a_2894_);
lean_dec(v_a_2893_);
lean_dec_ref(v_a_2892_);
lean_dec(v_a_2891_);
lean_dec_ref(v_a_2890_);
lean_dec(v_a_2889_);
lean_dec_ref(v_a_2888_);
lean_dec(v_a_2887_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_(){
_start:
{
lean_object* v___f_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___f_2924_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_));
v___x_2925_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_));
v___x_2926_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_));
v___x_2927_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_2925_, v___x_2926_, v___f_2924_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15____boxed(lean_object* v_a_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_();
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_17_(){
_start:
{
lean_object* v___f_2931_; lean_object* v___x_2932_; uint8_t v___x_2933_; lean_object* v___x_2934_; 
v___f_2931_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_));
v___x_2932_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_));
v___x_2933_ = 0;
v___x_2934_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_2932_, v___x_2933_, v___f_2931_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_17____boxed(lean_object* v_a_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_17_();
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0(lean_object* v_msgData_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v___x_2943_; lean_object* v_env_2944_; lean_object* v___x_2945_; lean_object* v_mctx_2946_; lean_object* v_lctx_2947_; lean_object* v_options_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2943_ = lean_st_ref_get(v___y_2941_);
v_env_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc_ref(v_env_2944_);
lean_dec(v___x_2943_);
v___x_2945_ = lean_st_ref_get(v___y_2939_);
v_mctx_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc_ref(v_mctx_2946_);
lean_dec(v___x_2945_);
v_lctx_2947_ = lean_ctor_get(v___y_2938_, 2);
v_options_2948_ = lean_ctor_get(v___y_2940_, 2);
lean_inc_ref(v_options_2948_);
lean_inc_ref(v_lctx_2947_);
v___x_2949_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2949_, 0, v_env_2944_);
lean_ctor_set(v___x_2949_, 1, v_mctx_2946_);
lean_ctor_set(v___x_2949_, 2, v_lctx_2947_);
lean_ctor_set(v___x_2949_, 3, v_options_2948_);
v___x_2950_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
lean_ctor_set(v___x_2950_, 1, v_msgData_2937_);
v___x_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0___boxed(lean_object* v_msgData_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
lean_object* v_res_2958_; 
v_res_2958_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0(v_msgData_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
lean_dec(v___y_2956_);
lean_dec_ref(v___y_2955_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
return v_res_2958_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2959_; double v___x_2960_; 
v___x_2959_ = lean_unsigned_to_nat(0u);
v___x_2960_ = lean_float_of_nat(v___x_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(lean_object* v_cls_2964_, lean_object* v_msg_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_){
_start:
{
lean_object* v_ref_2971_; lean_object* v___x_2972_; lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_3017_; 
v_ref_2971_ = lean_ctor_get(v___y_2968_, 5);
v___x_2972_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0(v_msg_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_2975_ = v___x_2972_;
v_isShared_2976_ = v_isSharedCheck_3017_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2972_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_3017_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2977_; lean_object* v_traceState_2978_; lean_object* v_env_2979_; lean_object* v_nextMacroScope_2980_; lean_object* v_ngen_2981_; lean_object* v_auxDeclNGen_2982_; lean_object* v_cache_2983_; lean_object* v_messages_2984_; lean_object* v_infoState_2985_; lean_object* v_snapshotTasks_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_3016_; 
v___x_2977_ = lean_st_ref_take(v___y_2969_);
v_traceState_2978_ = lean_ctor_get(v___x_2977_, 4);
v_env_2979_ = lean_ctor_get(v___x_2977_, 0);
v_nextMacroScope_2980_ = lean_ctor_get(v___x_2977_, 1);
v_ngen_2981_ = lean_ctor_get(v___x_2977_, 2);
v_auxDeclNGen_2982_ = lean_ctor_get(v___x_2977_, 3);
v_cache_2983_ = lean_ctor_get(v___x_2977_, 5);
v_messages_2984_ = lean_ctor_get(v___x_2977_, 6);
v_infoState_2985_ = lean_ctor_get(v___x_2977_, 7);
v_snapshotTasks_2986_ = lean_ctor_get(v___x_2977_, 8);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_2988_ = v___x_2977_;
v_isShared_2989_ = v_isSharedCheck_3016_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_snapshotTasks_2986_);
lean_inc(v_infoState_2985_);
lean_inc(v_messages_2984_);
lean_inc(v_cache_2983_);
lean_inc(v_traceState_2978_);
lean_inc(v_auxDeclNGen_2982_);
lean_inc(v_ngen_2981_);
lean_inc(v_nextMacroScope_2980_);
lean_inc(v_env_2979_);
lean_dec(v___x_2977_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_3016_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
uint64_t v_tid_2990_; lean_object* v_traces_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3015_; 
v_tid_2990_ = lean_ctor_get_uint64(v_traceState_2978_, sizeof(void*)*1);
v_traces_2991_ = lean_ctor_get(v_traceState_2978_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v_traceState_2978_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_2993_ = v_traceState_2978_;
v_isShared_2994_ = v_isSharedCheck_3015_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_traces_2991_);
lean_dec(v_traceState_2978_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3015_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2995_; double v___x_2996_; uint8_t v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3005_; 
v___x_2995_ = lean_box(0);
v___x_2996_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0);
v___x_2997_ = 0;
v___x_2998_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__1));
v___x_2999_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2999_, 0, v_cls_2964_);
lean_ctor_set(v___x_2999_, 1, v___x_2995_);
lean_ctor_set(v___x_2999_, 2, v___x_2998_);
lean_ctor_set_float(v___x_2999_, sizeof(void*)*3, v___x_2996_);
lean_ctor_set_float(v___x_2999_, sizeof(void*)*3 + 8, v___x_2996_);
lean_ctor_set_uint8(v___x_2999_, sizeof(void*)*3 + 16, v___x_2997_);
v___x_3000_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__2));
v___x_3001_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3001_, 0, v___x_2999_);
lean_ctor_set(v___x_3001_, 1, v_a_2973_);
lean_ctor_set(v___x_3001_, 2, v___x_3000_);
lean_inc(v_ref_2971_);
v___x_3002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3002_, 0, v_ref_2971_);
lean_ctor_set(v___x_3002_, 1, v___x_3001_);
v___x_3003_ = l_Lean_PersistentArray_push___redArg(v_traces_2991_, v___x_3002_);
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 0, v___x_3003_);
v___x_3005_ = v___x_2993_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_3003_);
lean_ctor_set_uint64(v_reuseFailAlloc_3014_, sizeof(void*)*1, v_tid_2990_);
v___x_3005_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
lean_object* v___x_3007_; 
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 4, v___x_3005_);
v___x_3007_ = v___x_2988_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_env_2979_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v_nextMacroScope_2980_);
lean_ctor_set(v_reuseFailAlloc_3013_, 2, v_ngen_2981_);
lean_ctor_set(v_reuseFailAlloc_3013_, 3, v_auxDeclNGen_2982_);
lean_ctor_set(v_reuseFailAlloc_3013_, 4, v___x_3005_);
lean_ctor_set(v_reuseFailAlloc_3013_, 5, v_cache_2983_);
lean_ctor_set(v_reuseFailAlloc_3013_, 6, v_messages_2984_);
lean_ctor_set(v_reuseFailAlloc_3013_, 7, v_infoState_2985_);
lean_ctor_set(v_reuseFailAlloc_3013_, 8, v_snapshotTasks_2986_);
v___x_3007_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3011_; 
v___x_3008_ = lean_st_ref_set(v___y_2969_, v___x_3007_);
v___x_3009_ = lean_box(0);
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 0, v___x_3009_);
v___x_3011_ = v___x_2975_;
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___boxed(lean_object* v_cls_3018_, lean_object* v_msg_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v_cls_3018_, v_msg_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
return v_res_3025_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5(void){
_start:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3036_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2));
v___x_3037_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__4));
v___x_3038_ = l_Lean_Name_append(v___x_3037_, v___x_3036_);
return v___x_3038_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7(void){
_start:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3040_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__6));
v___x_3041_ = l_Lean_stringToMessageData(v___x_3040_);
return v___x_3041_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9(void){
_start:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__8));
v___x_3044_ = l_Lean_stringToMessageData(v___x_3043_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(lean_object* v_e_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
lean_inc_ref(v_e_3047_);
v___x_3058_ = lean_alloc_closure((void*)(l_Lean_Meta_reduceRecMatcher_x3f___boxed), 6, 1);
lean_closure_set(v___x_3058_, 0, v_e_3047_);
v___x_3059_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___x_3058_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3116_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3062_ = v___x_3059_;
v_isShared_3063_ = v_isSharedCheck_3116_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3059_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3116_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
if (lean_obj_tag(v_a_3060_) == 1)
{
lean_object* v_val_3064_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v_options_3090_; uint8_t v_hasTrace_3091_; 
lean_del_object(v___x_3062_);
v_val_3064_ = lean_ctor_get(v_a_3060_, 0);
lean_inc(v_val_3064_);
lean_dec_ref(v_a_3060_);
v_options_3090_ = lean_ctor_get(v_a_3055_, 2);
v_hasTrace_3091_ = lean_ctor_get_uint8(v_options_3090_, sizeof(void*)*1);
if (v_hasTrace_3091_ == 0)
{
lean_dec_ref(v_e_3047_);
v___y_3066_ = v_a_3052_;
v___y_3067_ = v_a_3053_;
v___y_3068_ = v_a_3054_;
v___y_3069_ = v_a_3055_;
v___y_3070_ = v_a_3056_;
goto v___jp_3065_;
}
else
{
lean_object* v_inheritedTraceOptions_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; uint8_t v___x_3095_; 
v_inheritedTraceOptions_3092_ = lean_ctor_get(v_a_3055_, 13);
v___x_3093_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2));
v___x_3094_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5, &l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5);
v___x_3095_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3092_, v_options_3090_, v___x_3094_);
if (v___x_3095_ == 0)
{
lean_dec_ref(v_e_3047_);
v___y_3066_ = v_a_3052_;
v___y_3067_ = v_a_3053_;
v___y_3068_ = v_a_3054_;
v___y_3069_ = v_a_3055_;
v___y_3070_ = v_a_3056_;
goto v___jp_3065_;
}
else
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3096_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7, &l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7);
v___x_3097_ = l_Lean_indentExpr(v_e_3047_);
v___x_3098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3096_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
v___x_3099_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9, &l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9_once, _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9);
v___x_3100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3098_);
lean_ctor_set(v___x_3100_, 1, v___x_3099_);
lean_inc(v_val_3064_);
v___x_3101_ = l_Lean_indentExpr(v_val_3064_);
v___x_3102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3100_);
lean_ctor_set(v___x_3102_, 1, v___x_3101_);
v___x_3103_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v___x_3093_, v___x_3102_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_dec_ref(v___x_3103_);
v___y_3066_ = v_a_3052_;
v___y_3067_ = v_a_3053_;
v___y_3068_ = v_a_3054_;
v___y_3069_ = v_a_3055_;
v___y_3070_ = v_a_3056_;
goto v___jp_3065_;
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_dec(v_val_3064_);
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3103_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3103_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
}
v___jp_3065_:
{
lean_object* v___x_3071_; 
lean_inc(v_val_3064_);
v___x_3071_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_val_3064_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3081_; 
v_a_3072_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3074_ = v___x_3071_;
v_isShared_3075_ = v_isSharedCheck_3081_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_3071_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3081_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
uint8_t v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3079_; 
v___x_3076_ = 0;
v___x_3077_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3077_, 0, v_val_3064_);
lean_ctor_set(v___x_3077_, 1, v_a_3072_);
lean_ctor_set_uint8(v___x_3077_, sizeof(void*)*2, v___x_3076_);
lean_ctor_set_uint8(v___x_3077_, sizeof(void*)*2 + 1, v___x_3076_);
if (v_isShared_3075_ == 0)
{
lean_ctor_set(v___x_3074_, 0, v___x_3077_);
v___x_3079_ = v___x_3074_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v___x_3077_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
else
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3089_; 
lean_dec(v_val_3064_);
v_a_3082_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3084_ = v___x_3071_;
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3071_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3087_; 
if (v_isShared_3085_ == 0)
{
v___x_3087_ = v___x_3084_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_a_3082_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
}
}
else
{
lean_object* v___x_3112_; lean_object* v___x_3114_; 
lean_dec(v_a_3060_);
lean_dec_ref(v_e_3047_);
v___x_3112_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__10));
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 0, v___x_3112_);
v___x_3114_ = v___x_3062_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3112_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
else
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
lean_dec_ref(v_e_3047_);
v_a_3117_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3059_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3059_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___boxed(lean_object* v_e_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_e_3125_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
lean_dec(v_a_3134_);
lean_dec_ref(v_a_3133_);
lean_dec(v_a_3132_);
lean_dec_ref(v_a_3131_);
lean_dec(v_a_3130_);
lean_dec_ref(v_a_3129_);
lean_dec(v_a_3128_);
lean_dec_ref(v_a_3127_);
lean_dec(v_a_3126_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0(lean_object* v_cls_3137_, lean_object* v_msg_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v___x_3149_; 
v___x_3149_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v_cls_3137_, v_msg_3138_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
return v___x_3149_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___boxed(lean_object* v_cls_3150_, lean_object* v_msg_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
lean_object* v_res_3162_; 
v_res_3162_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0(v_cls_3150_, v_msg_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec(lean_object* v_x_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_){
_start:
{
uint8_t v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3188_ = 0;
v___x_3189_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___closed__0));
lean_inc_ref(v_x_3177_);
v___x_3190_ = l_Lean_Meta_Sym_Simp_simpInterlaced(v_x_3177_, v___x_3189_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v_a_3191_; 
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
lean_inc(v_a_3191_);
if (lean_obj_tag(v_a_3191_) == 0)
{
uint8_t v_done_3192_; 
v_done_3192_ = lean_ctor_get_uint8(v_a_3191_, 0);
if (v_done_3192_ == 0)
{
lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3205_; 
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3205_ == 0)
{
lean_object* v_unused_3206_; 
v_unused_3206_ = lean_ctor_get(v___x_3190_, 0);
lean_dec(v_unused_3206_);
v___x_3194_ = v___x_3190_;
v_isShared_3195_ = v_isSharedCheck_3205_;
goto v_resetjp_3193_;
}
else
{
lean_dec(v___x_3190_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3205_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
uint8_t v_contextDependent_3196_; lean_object* v___x_3197_; 
v_contextDependent_3196_ = lean_ctor_get_uint8(v_a_3191_, 1);
lean_dec_ref(v_a_3191_);
v___x_3197_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_x_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v_a_3198_; uint8_t v___y_3200_; 
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
lean_inc(v_a_3198_);
if (v_contextDependent_3196_ == 0)
{
lean_dec(v_a_3198_);
lean_del_object(v___x_3194_);
return v___x_3197_;
}
else
{
lean_dec_ref(v___x_3197_);
v___y_3200_ = v___x_3188_;
goto v___jp_3199_;
}
v___jp_3199_:
{
lean_object* v___x_3201_; lean_object* v___x_3203_; 
v___x_3201_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3198_);
if (v_isShared_3195_ == 0)
{
lean_ctor_set(v___x_3194_, 0, v___x_3201_);
v___x_3203_ = v___x_3194_;
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
else
{
lean_del_object(v___x_3194_);
return v___x_3197_;
}
}
}
else
{
lean_dec_ref(v_a_3191_);
lean_dec_ref(v_x_3177_);
return v___x_3190_;
}
}
else
{
uint8_t v_done_3207_; 
v_done_3207_ = lean_ctor_get_uint8(v_a_3191_, sizeof(void*)*2);
if (v_done_3207_ == 0)
{
lean_object* v_e_x27_3208_; lean_object* v_proof_3209_; uint8_t v_contextDependent_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3256_; 
lean_dec_ref(v___x_3190_);
v_e_x27_3208_ = lean_ctor_get(v_a_3191_, 0);
v_proof_3209_ = lean_ctor_get(v_a_3191_, 1);
v_contextDependent_3210_ = lean_ctor_get_uint8(v_a_3191_, sizeof(void*)*2 + 1);
v_isSharedCheck_3256_ = !lean_is_exclusive(v_a_3191_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3212_ = v_a_3191_;
v_isShared_3213_ = v_isSharedCheck_3256_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_proof_3209_);
lean_inc(v_e_x27_3208_);
lean_dec(v_a_3191_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3256_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3214_; 
lean_inc_ref(v_e_x27_3208_);
v___x_3214_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_e_x27_3208_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3255_; 
v_a_3215_ = lean_ctor_get(v___x_3214_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3217_ = v___x_3214_;
v_isShared_3218_ = v_isSharedCheck_3255_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_3214_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3255_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
if (lean_obj_tag(v_a_3215_) == 0)
{
uint8_t v___y_3220_; 
lean_dec_ref(v_a_3215_);
lean_dec_ref(v_x_3177_);
if (v_contextDependent_3210_ == 0)
{
v___y_3220_ = v___x_3188_;
goto v___jp_3219_;
}
else
{
v___y_3220_ = v_contextDependent_3210_;
goto v___jp_3219_;
}
v___jp_3219_:
{
lean_object* v___x_3222_; 
if (v_isShared_3213_ == 0)
{
v___x_3222_ = v___x_3212_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_e_x27_3208_);
lean_ctor_set(v_reuseFailAlloc_3226_, 1, v_proof_3209_);
v___x_3222_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
lean_object* v___x_3224_; 
lean_ctor_set_uint8(v___x_3222_, sizeof(void*)*2, v___x_3188_);
lean_ctor_set_uint8(v___x_3222_, sizeof(void*)*2 + 1, v___y_3220_);
if (v_isShared_3218_ == 0)
{
lean_ctor_set(v___x_3217_, 0, v___x_3222_);
v___x_3224_ = v___x_3217_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3222_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
else
{
lean_object* v_e_x27_3227_; lean_object* v_proof_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3254_; 
lean_del_object(v___x_3217_);
lean_del_object(v___x_3212_);
v_e_x27_3227_ = lean_ctor_get(v_a_3215_, 0);
v_proof_3228_ = lean_ctor_get(v_a_3215_, 1);
v_isSharedCheck_3254_ = !lean_is_exclusive(v_a_3215_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3230_ = v_a_3215_;
v_isShared_3231_ = v_isSharedCheck_3254_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_proof_3228_);
lean_inc(v_e_x27_3227_);
lean_dec(v_a_3215_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3254_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3232_; 
lean_inc_ref(v_e_x27_3227_);
v___x_3232_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v_x_3177_, v_e_x27_3208_, v_proof_3209_, v_e_x27_3227_, v_proof_3228_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_a_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3245_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3235_ = v___x_3232_;
v_isShared_3236_ = v_isSharedCheck_3245_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_a_3233_);
lean_dec(v___x_3232_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3245_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
uint8_t v___y_3238_; 
if (v_contextDependent_3210_ == 0)
{
v___y_3238_ = v___x_3188_;
goto v___jp_3237_;
}
else
{
v___y_3238_ = v_contextDependent_3210_;
goto v___jp_3237_;
}
v___jp_3237_:
{
lean_object* v___x_3240_; 
if (v_isShared_3231_ == 0)
{
lean_ctor_set(v___x_3230_, 1, v_a_3233_);
v___x_3240_ = v___x_3230_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_e_x27_3227_);
lean_ctor_set(v_reuseFailAlloc_3244_, 1, v_a_3233_);
v___x_3240_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
lean_object* v___x_3242_; 
lean_ctor_set_uint8(v___x_3240_, sizeof(void*)*2, v___x_3188_);
lean_ctor_set_uint8(v___x_3240_, sizeof(void*)*2 + 1, v___y_3238_);
if (v_isShared_3236_ == 0)
{
lean_ctor_set(v___x_3235_, 0, v___x_3240_);
v___x_3242_ = v___x_3235_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v___x_3240_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
}
}
else
{
lean_object* v_a_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3253_; 
lean_del_object(v___x_3230_);
lean_dec_ref(v_e_x27_3227_);
v_a_3246_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3248_ = v___x_3232_;
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_a_3246_);
lean_dec(v___x_3232_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3251_; 
if (v_isShared_3249_ == 0)
{
v___x_3251_ = v___x_3248_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_a_3246_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_3212_);
lean_dec_ref(v_proof_3209_);
lean_dec_ref(v_e_x27_3208_);
lean_dec_ref(v_x_3177_);
return v___x_3214_;
}
}
}
else
{
lean_dec_ref(v_a_3191_);
lean_dec_ref(v_x_3177_);
return v___x_3190_;
}
}
}
else
{
lean_dec_ref(v_x_3177_);
return v___x_3190_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___boxed(lean_object* v_x_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_){
_start:
{
lean_object* v_res_3268_; 
v_res_3268_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec(v_x_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_);
lean_dec(v_a_3266_);
lean_dec_ref(v_a_3265_);
lean_dec(v_a_3264_);
lean_dec_ref(v_a_3263_);
lean_dec(v_a_3262_);
lean_dec_ref(v_a_3261_);
lean_dec(v_a_3260_);
lean_dec_ref(v_a_3259_);
lean_dec(v_a_3258_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3291_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_));
v___x_3292_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_));
v___x_3293_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___boxed), 11, 0);
v___x_3294_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_3291_, v___x_3292_, v___x_3293_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17____boxed(lean_object* v_a_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_();
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_3298_; uint8_t v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3298_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_));
v___x_3299_ = 0;
v___x_3300_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___boxed), 11, 0);
v___x_3301_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_3298_, v___x_3299_, v___x_3300_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_19____boxed(lean_object* v_a_3302_){
_start:
{
lean_object* v_res_3303_; 
v_res_3303_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_19_();
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(lean_object* v_appFn_3305_, lean_object* v_e_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_){
_start:
{
lean_object* v___x_3317_; 
v___x_3317_ = l_Lean_Meta_Tactic_Cbv_getMatchTheorems(v_appFn_3305_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_);
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_object* v_a_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
lean_inc(v_a_3318_);
lean_dec_ref(v___x_3317_);
v___x_3319_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0));
v___x_3320_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_3318_, v___x_3319_, v_e_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_);
return v___x_3320_;
}
else
{
lean_object* v_a_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3328_; 
lean_dec_ref(v_e_3306_);
v_a_3321_ = lean_ctor_get(v___x_3317_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3323_ = v___x_3317_;
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_a_3321_);
lean_dec(v___x_3317_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3326_; 
if (v_isShared_3324_ == 0)
{
v___x_3326_ = v___x_3323_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_a_3321_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___boxed(lean_object* v_appFn_3329_, lean_object* v_e_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_){
_start:
{
lean_object* v_res_3341_; 
v_res_3341_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(v_appFn_3329_, v_e_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_);
lean_dec(v_a_3339_);
lean_dec_ref(v_a_3338_);
lean_dec(v_a_3337_);
lean_dec_ref(v_a_3336_);
lean_dec(v_a_3335_);
lean_dec_ref(v_a_3334_);
lean_dec(v_a_3333_);
lean_dec_ref(v_a_3332_);
lean_dec(v_a_3331_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(lean_object* v_declName_3342_, lean_object* v___y_3343_){
_start:
{
lean_object* v___x_3345_; lean_object* v_env_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3345_ = lean_st_ref_get(v___y_3343_);
v_env_3346_ = lean_ctor_get(v___x_3345_, 0);
lean_inc_ref(v_env_3346_);
lean_dec(v___x_3345_);
v___x_3347_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_3346_, v_declName_3342_);
v___x_3348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3347_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg___boxed(lean_object* v_declName_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(v_declName_3349_, v___y_3350_);
lean_dec(v___y_3350_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0(lean_object* v_declName_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_){
_start:
{
lean_object* v___x_3364_; 
v___x_3364_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(v_declName_3353_, v___y_3362_);
return v___x_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___boxed(lean_object* v_declName_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0(v_declName_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v___y_3368_);
lean_dec_ref(v___y_3367_);
lean_dec(v___y_3366_);
return v_res_3376_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2(void){
_start:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3383_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1));
v___x_3384_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__4));
v___x_3385_ = l_Lean_Name_append(v___x_3384_, v___x_3383_);
return v___x_3385_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4(void){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3387_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__3));
v___x_3388_ = l_Lean_stringToMessageData(v___x_3387_);
return v___x_3388_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6(void){
_start:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3390_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__5));
v___x_3391_ = l_Lean_stringToMessageData(v___x_3390_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher(lean_object* v_e_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_){
_start:
{
uint8_t v___x_3403_; 
v___x_3403_ = l_Lean_Expr_isApp(v_e_3392_);
if (v___x_3403_ == 0)
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
lean_dec_ref(v_e_3392_);
v___x_3404_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3404_, 0, v___x_3403_);
lean_ctor_set_uint8(v___x_3404_, 1, v___x_3403_);
v___x_3405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3404_);
return v___x_3405_;
}
else
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3406_ = l_Lean_Expr_getAppFn(v_e_3392_);
v___x_3407_ = l_Lean_Expr_constName_x3f(v___x_3406_);
lean_dec_ref(v___x_3406_);
if (lean_obj_tag(v___x_3407_) == 1)
{
lean_object* v_val_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3555_; 
v_val_3408_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3410_ = v___x_3407_;
v_isShared_3411_ = v_isSharedCheck_3555_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_val_3408_);
lean_dec(v___x_3407_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3555_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v_a_3413_; lean_object* v_e_x27_3414_; lean_object* v___y_3456_; lean_object* v_a_3457_; lean_object* v___y_3460_; lean_object* v___y_3463_; lean_object* v___y_3464_; uint8_t v___y_3465_; lean_object* v___y_3469_; lean_object* v_a_3470_; lean_object* v___y_3478_; lean_object* v___x_3480_; lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3554_; 
lean_inc(v_val_3408_);
v___x_3480_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(v_val_3408_, v_a_3401_);
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3483_ = v___x_3480_;
v_isShared_3484_ = v_isSharedCheck_3554_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3480_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3554_;
goto v_resetjp_3482_;
}
v___jp_3412_:
{
lean_object* v_options_3415_; uint8_t v_hasTrace_3416_; 
v_options_3415_ = lean_ctor_get(v_a_3400_, 2);
v_hasTrace_3416_ = lean_ctor_get_uint8(v_options_3415_, sizeof(void*)*1);
if (v_hasTrace_3416_ == 0)
{
lean_object* v___x_3418_; 
lean_dec_ref(v_e_x27_3414_);
lean_dec(v_val_3408_);
lean_dec_ref(v_e_3392_);
if (v_isShared_3411_ == 0)
{
lean_ctor_set_tag(v___x_3410_, 0);
lean_ctor_set(v___x_3410_, 0, v_a_3413_);
v___x_3418_ = v___x_3410_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3413_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; uint8_t v___x_3423_; 
v_inheritedTraceOptions_3420_ = lean_ctor_get(v_a_3400_, 13);
v___x_3421_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1));
v___x_3422_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2, &l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2);
v___x_3423_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3420_, v_options_3415_, v___x_3422_);
if (v___x_3423_ == 0)
{
lean_object* v___x_3425_; 
lean_dec_ref(v_e_x27_3414_);
lean_dec(v_val_3408_);
lean_dec_ref(v_e_3392_);
if (v_isShared_3411_ == 0)
{
lean_ctor_set_tag(v___x_3410_, 0);
lean_ctor_set(v___x_3410_, 0, v_a_3413_);
v___x_3425_ = v___x_3410_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_a_3413_);
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
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
lean_del_object(v___x_3410_);
v___x_3427_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4, &l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4_once, _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4);
v___x_3428_ = l_Lean_MessageData_ofName(v_val_3408_);
v___x_3429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3427_);
lean_ctor_set(v___x_3429_, 1, v___x_3428_);
v___x_3430_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6, &l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6);
v___x_3431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3429_);
lean_ctor_set(v___x_3431_, 1, v___x_3430_);
v___x_3432_ = l_Lean_indentExpr(v_e_3392_);
v___x_3433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3431_);
lean_ctor_set(v___x_3433_, 1, v___x_3432_);
v___x_3434_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9, &l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9_once, _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9);
v___x_3435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3433_);
lean_ctor_set(v___x_3435_, 1, v___x_3434_);
v___x_3436_ = l_Lean_indentExpr(v_e_x27_3414_);
v___x_3437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3435_);
lean_ctor_set(v___x_3437_, 1, v___x_3436_);
v___x_3438_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v___x_3421_, v___x_3437_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3445_ == 0)
{
lean_object* v_unused_3446_; 
v_unused_3446_ = lean_ctor_get(v___x_3438_, 0);
lean_dec(v_unused_3446_);
v___x_3440_ = v___x_3438_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_dec(v___x_3438_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 0, v_a_3413_);
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3413_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
else
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
lean_dec_ref(v_a_3413_);
v_a_3447_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3438_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3438_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3447_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
}
}
v___jp_3455_:
{
if (lean_obj_tag(v_a_3457_) == 1)
{
lean_object* v_e_x27_3458_; 
lean_dec_ref(v___y_3456_);
v_e_x27_3458_ = lean_ctor_get(v_a_3457_, 0);
lean_inc_ref(v_e_x27_3458_);
v_a_3413_ = v_a_3457_;
v_e_x27_3414_ = v_e_x27_3458_;
goto v___jp_3412_;
}
else
{
lean_dec_ref(v_a_3457_);
lean_del_object(v___x_3410_);
lean_dec(v_val_3408_);
lean_dec_ref(v_e_3392_);
return v___y_3456_;
}
}
v___jp_3459_:
{
if (lean_obj_tag(v___y_3460_) == 0)
{
lean_object* v_a_3461_; 
v_a_3461_ = lean_ctor_get(v___y_3460_, 0);
lean_inc(v_a_3461_);
v___y_3456_ = v___y_3460_;
v_a_3457_ = v_a_3461_;
goto v___jp_3455_;
}
else
{
lean_del_object(v___x_3410_);
lean_dec(v_val_3408_);
lean_dec_ref(v_e_3392_);
return v___y_3460_;
}
}
v___jp_3462_:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; 
lean_dec_ref(v___y_3464_);
v___x_3466_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3463_);
lean_inc_ref(v___x_3466_);
v___x_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3466_);
v___y_3456_ = v___x_3467_;
v_a_3457_ = v___x_3466_;
goto v___jp_3455_;
}
v___jp_3468_:
{
if (lean_obj_tag(v_a_3470_) == 0)
{
uint8_t v_done_3471_; 
v_done_3471_ = lean_ctor_get_uint8(v_a_3470_, 0);
if (v_done_3471_ == 0)
{
uint8_t v_contextDependent_3472_; lean_object* v___x_3473_; 
lean_dec_ref(v___y_3469_);
v_contextDependent_3472_ = lean_ctor_get_uint8(v_a_3470_, 1);
lean_dec_ref(v_a_3470_);
lean_inc_ref(v_e_3392_);
v___x_3473_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_e_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_);
if (lean_obj_tag(v___x_3473_) == 0)
{
if (v_contextDependent_3472_ == 0)
{
v___y_3460_ = v___x_3473_;
goto v___jp_3459_;
}
else
{
lean_object* v_a_3474_; uint8_t v___x_3475_; 
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
lean_inc(v_a_3474_);
v___x_3475_ = 0;
v___y_3463_ = v_a_3474_;
v___y_3464_ = v___x_3473_;
v___y_3465_ = v___x_3475_;
goto v___jp_3462_;
}
}
else
{
v___y_3460_ = v___x_3473_;
goto v___jp_3459_;
}
}
else
{
lean_dec_ref(v_a_3470_);
lean_del_object(v___x_3410_);
lean_dec(v_val_3408_);
lean_dec_ref(v_e_3392_);
return v___y_3469_;
}
}
else
{
lean_object* v_e_x27_3476_; 
lean_dec_ref(v___y_3469_);
v_e_x27_3476_ = lean_ctor_get(v_a_3470_, 0);
lean_inc_ref(v_e_x27_3476_);
v_a_3413_ = v_a_3470_;
v_e_x27_3414_ = v_e_x27_3476_;
goto v___jp_3412_;
}
}
v___jp_3477_:
{
if (lean_obj_tag(v___y_3478_) == 0)
{
lean_object* v_a_3479_; 
v_a_3479_ = lean_ctor_get(v___y_3478_, 0);
lean_inc(v_a_3479_);
v___y_3469_ = v___y_3478_;
v_a_3470_ = v_a_3479_;
goto v___jp_3468_;
}
else
{
lean_del_object(v___x_3410_);
lean_dec(v_val_3408_);
lean_dec_ref(v_e_3392_);
return v___y_3478_;
}
}
v_resetjp_3482_:
{
if (lean_obj_tag(v_a_3481_) == 1)
{
lean_object* v_val_3485_; lean_object* v_numParams_3486_; lean_object* v_numDiscrs_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
lean_del_object(v___x_3483_);
v_val_3485_ = lean_ctor_get(v_a_3481_, 0);
lean_inc(v_val_3485_);
lean_dec_ref(v_a_3481_);
v_numParams_3486_ = lean_ctor_get(v_val_3485_, 0);
lean_inc(v_numParams_3486_);
v_numDiscrs_3487_ = lean_ctor_get(v_val_3485_, 1);
lean_inc(v_numDiscrs_3487_);
lean_dec(v_val_3485_);
v___x_3488_ = lean_unsigned_to_nat(1u);
v___x_3489_ = lean_nat_add(v_numParams_3486_, v___x_3488_);
lean_dec(v_numParams_3486_);
v___x_3490_ = lean_nat_add(v___x_3489_, v_numDiscrs_3487_);
lean_dec(v_numDiscrs_3487_);
lean_inc_ref(v_e_3392_);
v___x_3491_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_e_3392_, v___x_3489_, v___x_3490_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_);
lean_dec(v___x_3490_);
lean_dec(v___x_3489_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_a_3492_);
if (lean_obj_tag(v_a_3492_) == 0)
{
uint8_t v_done_3493_; 
v_done_3493_ = lean_ctor_get_uint8(v_a_3492_, 0);
if (v_done_3493_ == 0)
{
uint8_t v_contextDependent_3494_; lean_object* v___x_3495_; 
lean_dec_ref(v___x_3491_);
v_contextDependent_3494_ = lean_ctor_get_uint8(v_a_3492_, 1);
lean_dec_ref(v_a_3492_);
lean_inc_ref(v_e_3392_);
lean_inc(v_val_3408_);
v___x_3495_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(v_val_3408_, v_e_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; uint8_t v___y_3498_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
if (v_contextDependent_3494_ == 0)
{
lean_dec(v_a_3496_);
v___y_3478_ = v___x_3495_;
goto v___jp_3477_;
}
else
{
if (lean_obj_tag(v_a_3496_) == 0)
{
uint8_t v_contextDependent_3508_; 
v_contextDependent_3508_ = lean_ctor_get_uint8(v_a_3496_, 1);
v___y_3498_ = v_contextDependent_3508_;
goto v___jp_3497_;
}
else
{
uint8_t v_contextDependent_3509_; 
v_contextDependent_3509_ = lean_ctor_get_uint8(v_a_3496_, sizeof(void*)*2 + 1);
v___y_3498_ = v_contextDependent_3509_;
goto v___jp_3497_;
}
}
v___jp_3497_:
{
if (v___y_3498_ == 0)
{
lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3506_; 
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3506_ == 0)
{
lean_object* v_unused_3507_; 
v_unused_3507_ = lean_ctor_get(v___x_3495_, 0);
lean_dec(v_unused_3507_);
v___x_3500_ = v___x_3495_;
v_isShared_3501_ = v_isSharedCheck_3506_;
goto v_resetjp_3499_;
}
else
{
lean_dec(v___x_3495_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3506_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3502_; lean_object* v___x_3504_; 
v___x_3502_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3496_);
lean_inc_ref(v___x_3502_);
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 0, v___x_3502_);
v___x_3504_ = v___x_3500_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3502_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
v___y_3469_ = v___x_3504_;
v_a_3470_ = v___x_3502_;
goto v___jp_3468_;
}
}
}
else
{
lean_dec(v_a_3496_);
v___y_3478_ = v___x_3495_;
goto v___jp_3477_;
}
}
}
else
{
v___y_3478_ = v___x_3495_;
goto v___jp_3477_;
}
}
else
{
lean_dec_ref(v_a_3492_);
v___y_3478_ = v___x_3491_;
goto v___jp_3477_;
}
}
else
{
uint8_t v_done_3510_; 
v_done_3510_ = lean_ctor_get_uint8(v_a_3492_, sizeof(void*)*2);
if (v_done_3510_ == 0)
{
lean_object* v_e_x27_3511_; lean_object* v_proof_3512_; uint8_t v_contextDependent_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3549_; 
lean_dec_ref(v___x_3491_);
v_e_x27_3511_ = lean_ctor_get(v_a_3492_, 0);
v_proof_3512_ = lean_ctor_get(v_a_3492_, 1);
v_contextDependent_3513_ = lean_ctor_get_uint8(v_a_3492_, sizeof(void*)*2 + 1);
v_isSharedCheck_3549_ = !lean_is_exclusive(v_a_3492_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3515_ = v_a_3492_;
v_isShared_3516_ = v_isSharedCheck_3549_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_proof_3512_);
lean_inc(v_e_x27_3511_);
lean_dec(v_a_3492_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3549_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3517_; 
lean_inc_ref(v_e_x27_3511_);
lean_inc(v_val_3408_);
v___x_3517_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(v_val_3408_, v_e_x27_3511_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v_a_3518_; 
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc(v_a_3518_);
lean_dec_ref(v___x_3517_);
if (lean_obj_tag(v_a_3518_) == 0)
{
uint8_t v_done_3519_; uint8_t v_contextDependent_3520_; uint8_t v___y_3522_; 
v_done_3519_ = lean_ctor_get_uint8(v_a_3518_, 0);
v_contextDependent_3520_ = lean_ctor_get_uint8(v_a_3518_, 1);
lean_dec_ref(v_a_3518_);
if (v_contextDependent_3513_ == 0)
{
v___y_3522_ = v_contextDependent_3520_;
goto v___jp_3521_;
}
else
{
v___y_3522_ = v_contextDependent_3513_;
goto v___jp_3521_;
}
v___jp_3521_:
{
lean_object* v___x_3524_; 
lean_inc_ref(v_e_x27_3511_);
if (v_isShared_3516_ == 0)
{
v___x_3524_ = v___x_3515_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_e_x27_3511_);
lean_ctor_set(v_reuseFailAlloc_3525_, 1, v_proof_3512_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
lean_ctor_set_uint8(v___x_3524_, sizeof(void*)*2, v_done_3519_);
lean_ctor_set_uint8(v___x_3524_, sizeof(void*)*2 + 1, v___y_3522_);
v_a_3413_ = v___x_3524_;
v_e_x27_3414_ = v_e_x27_3511_;
goto v___jp_3412_;
}
}
}
else
{
lean_object* v_e_x27_3526_; lean_object* v_proof_3527_; uint8_t v_done_3528_; uint8_t v_contextDependent_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3548_; 
lean_del_object(v___x_3515_);
v_e_x27_3526_ = lean_ctor_get(v_a_3518_, 0);
v_proof_3527_ = lean_ctor_get(v_a_3518_, 1);
v_done_3528_ = lean_ctor_get_uint8(v_a_3518_, sizeof(void*)*2);
v_contextDependent_3529_ = lean_ctor_get_uint8(v_a_3518_, sizeof(void*)*2 + 1);
v_isSharedCheck_3548_ = !lean_is_exclusive(v_a_3518_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3531_ = v_a_3518_;
v_isShared_3532_ = v_isSharedCheck_3548_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_proof_3527_);
lean_inc(v_e_x27_3526_);
lean_dec(v_a_3518_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3548_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3533_; 
lean_inc_ref(v_e_x27_3526_);
lean_inc_ref(v_e_3392_);
v___x_3533_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v_e_3392_, v_e_x27_3511_, v_proof_3512_, v_e_x27_3526_, v_proof_3527_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v_a_3534_; uint8_t v___y_3536_; 
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
lean_inc(v_a_3534_);
lean_dec_ref(v___x_3533_);
if (v_contextDependent_3513_ == 0)
{
v___y_3536_ = v_contextDependent_3529_;
goto v___jp_3535_;
}
else
{
v___y_3536_ = v_contextDependent_3513_;
goto v___jp_3535_;
}
v___jp_3535_:
{
lean_object* v___x_3538_; 
lean_inc_ref(v_e_x27_3526_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 1, v_a_3534_);
v___x_3538_ = v___x_3531_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_e_x27_3526_);
lean_ctor_set(v_reuseFailAlloc_3539_, 1, v_a_3534_);
lean_ctor_set_uint8(v_reuseFailAlloc_3539_, sizeof(void*)*2, v_done_3528_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
lean_ctor_set_uint8(v___x_3538_, sizeof(void*)*2 + 1, v___y_3536_);
v_a_3413_ = v___x_3538_;
v_e_x27_3414_ = v_e_x27_3526_;
goto v___jp_3412_;
}
}
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
lean_del_object(v___x_3531_);
lean_dec_ref(v_e_x27_3526_);
lean_del_object(v___x_3410_);
lean_dec(v_val_3408_);
lean_dec_ref(v_e_3392_);
v_a_3540_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3533_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3533_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_3515_);
lean_dec_ref(v_proof_3512_);
lean_dec_ref(v_e_x27_3511_);
v___y_3478_ = v___x_3517_;
goto v___jp_3477_;
}
}
}
else
{
lean_dec_ref(v_a_3492_);
v___y_3478_ = v___x_3491_;
goto v___jp_3477_;
}
}
}
else
{
v___y_3478_ = v___x_3491_;
goto v___jp_3477_;
}
}
else
{
lean_object* v___x_3550_; lean_object* v___x_3552_; 
lean_dec(v_a_3481_);
lean_del_object(v___x_3410_);
lean_dec(v_val_3408_);
lean_dec_ref(v_e_3392_);
v___x_3550_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__10));
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 0, v___x_3550_);
v___x_3552_ = v___x_3483_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v___x_3550_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
}
}
}
else
{
lean_object* v___x_3556_; lean_object* v___x_3557_; 
lean_dec(v___x_3407_);
lean_dec_ref(v_e_3392_);
v___x_3556_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__10));
v___x_3557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3556_);
return v___x_3557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher___boxed(lean_object* v_e_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l_Lean_Meta_Tactic_Cbv_tryMatcher(v_e_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
lean_dec_ref(v_a_3560_);
lean_dec(v_a_3559_);
return v_res_3569_;
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
