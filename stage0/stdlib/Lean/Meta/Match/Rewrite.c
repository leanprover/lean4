// Lean compiler output
// Module: Lean.Meta.Match.Rewrite
// Imports: public import Lean.Meta.Tactic.Simp.Types import Lean.Meta.Tactic.Assumption import Lean.Meta.Tactic.Refl import Lean.Meta.Tactic.Simp.Rewrite
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
static const lean_string_object l_Lean_Meta_rwIfWith___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l_Lean_Meta_rwIfWith___closed__0 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Meta_rwIfWith___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwIfWith___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l_Lean_Meta_rwIfWith___closed__1 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__1_value;
static const lean_string_object l_Lean_Meta_rwIfWith___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l_Lean_Meta_rwIfWith___closed__2 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__2_value;
static const lean_ctor_object l_Lean_Meta_rwIfWith___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwIfWith___closed__2_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l_Lean_Meta_rwIfWith___closed__3 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__3_value;
static const lean_string_object l_Lean_Meta_rwIfWith___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_Meta_rwIfWith___closed__4 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__4_value;
static const lean_ctor_object l_Lean_Meta_rwIfWith___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwIfWith___closed__4_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l_Lean_Meta_rwIfWith___closed__5 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__5_value;
static const lean_string_object l_Lean_Meta_rwIfWith___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "if_neg"};
static const lean_object* l_Lean_Meta_rwIfWith___closed__6 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__6_value;
static const lean_ctor_object l_Lean_Meta_rwIfWith___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwIfWith___closed__6_value),LEAN_SCALAR_PTR_LITERAL(94, 43, 105, 241, 236, 232, 111, 225)}};
static const lean_object* l_Lean_Meta_rwIfWith___closed__7 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__7_value;
static const lean_string_object l_Lean_Meta_rwIfWith___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "if_pos"};
static const lean_object* l_Lean_Meta_rwIfWith___closed__8 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__8_value;
static const lean_ctor_object l_Lean_Meta_rwIfWith___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwIfWith___closed__8_value),LEAN_SCALAR_PTR_LITERAL(242, 79, 136, 209, 251, 93, 254, 106)}};
static const lean_object* l_Lean_Meta_rwIfWith___closed__9 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__9_value;
static const lean_string_object l_Lean_Meta_rwIfWith___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "dif_neg"};
static const lean_object* l_Lean_Meta_rwIfWith___closed__10 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__10_value;
static const lean_ctor_object l_Lean_Meta_rwIfWith___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwIfWith___closed__10_value),LEAN_SCALAR_PTR_LITERAL(184, 114, 55, 245, 8, 138, 156, 111)}};
static const lean_object* l_Lean_Meta_rwIfWith___closed__11 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__11_value;
static const lean_string_object l_Lean_Meta_rwIfWith___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "dif_pos"};
static const lean_object* l_Lean_Meta_rwIfWith___closed__12 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__12_value;
static const lean_ctor_object l_Lean_Meta_rwIfWith___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwIfWith___closed__12_value),LEAN_SCALAR_PTR_LITERAL(38, 147, 143, 206, 51, 9, 8, 80)}};
static const lean_object* l_Lean_Meta_rwIfWith___closed__13 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__13_value;
static const lean_string_object l_Lean_Meta_rwIfWith___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Meta_rwIfWith___closed__14 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__14_value;
static const lean_string_object l_Lean_Meta_rwIfWith___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Meta_rwIfWith___closed__15 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__15_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_rwIfWith___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwIfWith___closed__14_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_rwIfWith___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_rwIfWith___closed__16_value_aux_0),((lean_object*)&l_Lean_Meta_rwIfWith___closed__15_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Meta_rwIfWith___closed__16 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__16_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_rwIfWith___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwIfWith___closed__17;
static const lean_string_object l_Lean_Meta_rwIfWith___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Meta_rwIfWith___closed__18 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__18_value;
static const lean_ctor_object l_Lean_Meta_rwIfWith___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwIfWith___closed__14_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_rwIfWith___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_rwIfWith___closed__19_value_aux_0),((lean_object*)&l_Lean_Meta_rwIfWith___closed__18_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Meta_rwIfWith___closed__19 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__19_value;
static lean_once_cell_t l_Lean_Meta_rwIfWith___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwIfWith___closed__20;
static const lean_string_object l_Lean_Meta_rwIfWith___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "cond_neg"};
static const lean_object* l_Lean_Meta_rwIfWith___closed__21 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__21_value;
static const lean_ctor_object l_Lean_Meta_rwIfWith___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwIfWith___closed__14_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_rwIfWith___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_rwIfWith___closed__22_value_aux_0),((lean_object*)&l_Lean_Meta_rwIfWith___closed__21_value),LEAN_SCALAR_PTR_LITERAL(49, 12, 112, 38, 148, 75, 173, 29)}};
static const lean_object* l_Lean_Meta_rwIfWith___closed__22 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__22_value;
static const lean_string_object l_Lean_Meta_rwIfWith___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "cond_pos"};
static const lean_object* l_Lean_Meta_rwIfWith___closed__23 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__23_value;
static const lean_ctor_object l_Lean_Meta_rwIfWith___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwIfWith___closed__14_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_rwIfWith___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_rwIfWith___closed__24_value_aux_0),((lean_object*)&l_Lean_Meta_rwIfWith___closed__23_value),LEAN_SCALAR_PTR_LITERAL(92, 34, 41, 42, 220, 235, 208, 212)}};
static const lean_object* l_Lean_Meta_rwIfWith___closed__24 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__24_value;
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwIfWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwIfWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Meta_isMatcherAppCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg___closed__1_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__2_value;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6_spec__20___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___closed__0;
size_t lean_usize_sub(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___closed__1;
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Failed to resolve `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Failed to discharge `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__5;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis(lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_hrefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__7(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_rwMatcher___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Could not un-HEq `"};
static const lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__1;
static const lean_string_object l_Lean_Meta_rwMatcher___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`:"};
static const lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__3;
static const lean_string_object l_Lean_Meta_rwMatcher___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__4 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__1___closed__4_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__5;
static const lean_string_object l_Lean_Meta_rwMatcher___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Not all hypotheses of `"};
static const lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__6 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__1___closed__6_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__7;
static const lean_string_object l_Lean_Meta_rwMatcher___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "` could be discharged: "};
static const lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__8 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__1___closed__8_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__9;
static const lean_array_object l_Lean_Meta_rwMatcher___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__10 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__1___closed__10_value;
static const lean_string_object l_Lean_Meta_rwMatcher___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Left-hand side `"};
static const lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__11 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__1___closed__11_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__12;
static const lean_string_object l_Lean_Meta_rwMatcher___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "` of `"};
static const lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__13 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__1___closed__13_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__14;
static const lean_string_object l_Lean_Meta_rwMatcher___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` does not apply to `"};
static const lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__15 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__1___closed__15_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__16;
static const lean_string_object l_Lean_Meta_rwMatcher___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__17 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__1___closed__17_value;
static const lean_ctor_object l_Lean_Meta_rwMatcher___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwMatcher___lam__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__18 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__1___closed__18_value;
static const lean_string_object l_Lean_Meta_rwMatcher___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__19 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__1___closed__19_value;
static const lean_ctor_object l_Lean_Meta_rwMatcher___lam__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwMatcher___lam__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__20 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__1___closed__20_value;
static const lean_string_object l_Lean_Meta_rwMatcher___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Type of `"};
static const lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__21 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__1___closed__21_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__22;
static const lean_string_object l_Lean_Meta_rwMatcher___lam__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "` is not an equality"};
static const lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__23 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__1___closed__23_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__24;
static const lean_string_object l_Lean_Meta_rwMatcher___lam__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "eqProof has type"};
static const lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__25 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__1___closed__25_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__26;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_rwMatcher___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = " rewriting with "};
static const lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__1;
static const lean_string_object l_Lean_Meta_rwMatcher___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " in"};
static const lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__2 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__2___closed__2_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__3;
lean_object* l_Lean_exceptEmoji___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__14(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_rwMatcher_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_rwMatcher_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14_spec__16(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14_spec__16___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___redArg___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___redArg___closed__2;
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_rwMatcher___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Failed to apply "};
static const lean_object* l_Lean_Meta_rwMatcher___closed__0 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__0_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__1;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__2 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__2_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__3;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_rwMatcher___closed__4;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__5 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__5_value;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Match"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__6 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__6_value;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__7 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__7_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwMatcher___closed__5_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_rwMatcher___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_rwMatcher___closed__6_value),LEAN_SCALAR_PTR_LITERAL(250, 1, 225, 180, 135, 246, 184, 244)}};
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_rwMatcher___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_rwMatcher___closed__7_value),LEAN_SCALAR_PTR_LITERAL(253, 56, 25, 25, 156, 146, 62, 130)}};
static const lean_object* l_Lean_Meta_rwMatcher___closed__8 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__8_value;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Not a matcher application:"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__9 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__9_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__10;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "When trying to reduce arm "};
static const lean_object* l_Lean_Meta_rwMatcher___closed__11 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__11_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__12;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ", only "};
static const lean_object* l_Lean_Meta_rwMatcher___closed__13 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__13_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__14;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " equations for "};
static const lean_object* l_Lean_Meta_rwMatcher___closed__15 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__15_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__16;
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__17;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "PSum"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__18 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__18_value;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "casesOn"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__19 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__19_value;
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwMatcher___closed__18_value),LEAN_SCALAR_PTR_LITERAL(147, 224, 206, 173, 168, 27, 198, 53)}};
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_rwMatcher___closed__20_value_aux_0),((lean_object*)&l_Lean_Meta_rwMatcher___closed__19_value),LEAN_SCALAR_PTR_LITERAL(166, 115, 173, 38, 27, 113, 160, 8)}};
static const lean_object* l_Lean_Meta_rwMatcher___closed__20 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__20_value;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "PSigma"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__21 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__21_value;
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwMatcher___closed__21_value),LEAN_SCALAR_PTR_LITERAL(0, 171, 149, 177, 120, 131, 37, 223)}};
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_rwMatcher___closed__22_value_aux_0),((lean_object*)&l_Lean_Meta_rwMatcher___closed__19_value),LEAN_SCALAR_PTR_LITERAL(225, 129, 3, 119, 45, 252, 168, 83)}};
static const lean_object* l_Lean_Meta_rwMatcher___closed__22 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__22_value;
lean_object* lean_io_mono_nanos_now();
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* lean_get_congr_match_equations_for(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_rwIfWith___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_rwIfWith___closed__16));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_rwIfWith___closed__20(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_rwIfWith___closed__19));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwIfWith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_13; 
lean_inc_ref(x_2);
x_13 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_2, x_4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_Expr_cleanupAnnotations(x_14);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec_ref(x_15);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
goto block_12;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_17);
x_18 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
goto block_12;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_20);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
goto block_12;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_23);
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
goto block_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_26);
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_28 = ((lean_object*)(l_Lean_Meta_rwIfWith___closed__1));
x_29 = l_Lean_Expr_isConstOf(x_27, x_28);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Expr_isApp(x_27);
if (x_30 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
goto block_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_31);
x_32 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_33 = ((lean_object*)(l_Lean_Meta_rwIfWith___closed__3));
x_34 = l_Lean_Expr_isConstOf(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = ((lean_object*)(l_Lean_Meta_rwIfWith___closed__5));
x_36 = l_Lean_Expr_isConstOf(x_32, x_35);
if (x_36 == 0)
{
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
goto block_12;
}
else
{
lean_object* x_37; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_37 = lean_infer_type(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_26);
x_39 = l_Lean_Meta_isExprDefEq(x_26, x_38, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_104; 
x_40 = lean_ctor_get(x_39, 0);
x_104 = !lean_is_exclusive(x_39);
if (x_104 == 0)
{
x_41 = x_39;
x_42 = x_104;
goto block_103;
}
else
{
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_box(0);
x_42 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Lean_Expr_constLevels_x21(x_32);
lean_dec_ref(x_32);
x_44 = lean_unbox(x_40);
lean_dec(x_40);
if (x_44 == 0)
{
lean_object* x_45; 
lean_del_object(x_41);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_45 = lean_infer_type(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
lean_inc_ref(x_26);
x_47 = l_Lean_mkNot(x_26);
x_48 = l_Lean_Meta_isExprDefEq(x_47, x_46, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_70; 
x_49 = lean_ctor_get(x_48, 0);
x_70 = !lean_is_exclusive(x_48);
if (x_70 == 0)
{
x_50 = x_48;
x_51 = x_70;
goto block_69;
}
else
{
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_box(0);
x_51 = x_70;
goto block_69;
}
block_69:
{
uint8_t x_52; 
x_52 = lean_unbox(x_49);
lean_dec(x_49);
if (x_52 == 0)
{
lean_del_object(x_50);
lean_dec(x_43);
lean_dec_ref(x_31);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec_ref(x_1);
goto block_12;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec_ref(x_2);
x_53 = ((lean_object*)(l_Lean_Meta_rwIfWith___closed__7));
x_54 = l_Lean_mkConst(x_53, x_43);
x_55 = lean_unsigned_to_nat(6u);
x_56 = lean_mk_empty_array_with_capacity(x_55);
x_57 = lean_array_push(x_56, x_26);
x_58 = lean_array_push(x_57, x_23);
x_59 = lean_array_push(x_58, x_1);
x_60 = lean_array_push(x_59, x_31);
x_61 = lean_array_push(x_60, x_20);
lean_inc_ref(x_17);
x_62 = lean_array_push(x_61, x_17);
x_63 = l_Lean_mkAppN(x_54, x_62);
lean_dec_ref(x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_65, 0, x_17);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*2, x_36);
if (x_51 == 0)
{
lean_ctor_set(x_50, 0, x_65);
x_66 = x_50;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_65);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_78; 
lean_dec(x_43);
lean_dec_ref(x_31);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_71 = lean_ctor_get(x_48, 0);
x_78 = !lean_is_exclusive(x_48);
if (x_78 == 0)
{
x_72 = x_48;
x_73 = x_78;
goto block_77;
}
else
{
lean_inc(x_71);
lean_dec(x_48);
x_72 = lean_box(0);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
if (x_73 == 0)
{
x_74 = x_72;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_71);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_86; 
lean_dec(x_43);
lean_dec_ref(x_31);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_79 = lean_ctor_get(x_45, 0);
x_86 = !lean_is_exclusive(x_45);
if (x_86 == 0)
{
x_80 = x_45;
x_81 = x_86;
goto block_85;
}
else
{
lean_inc(x_79);
lean_dec(x_45);
x_80 = lean_box(0);
x_81 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_82; 
if (x_81 == 0)
{
x_82 = x_80;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_79);
x_82 = x_84;
goto block_83;
}
block_83:
{
return x_82;
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_87 = ((lean_object*)(l_Lean_Meta_rwIfWith___closed__9));
x_88 = l_Lean_mkConst(x_87, x_43);
x_89 = lean_unsigned_to_nat(6u);
x_90 = lean_mk_empty_array_with_capacity(x_89);
x_91 = lean_array_push(x_90, x_26);
x_92 = lean_array_push(x_91, x_23);
x_93 = lean_array_push(x_92, x_1);
x_94 = lean_array_push(x_93, x_31);
lean_inc_ref(x_20);
x_95 = lean_array_push(x_94, x_20);
x_96 = lean_array_push(x_95, x_17);
x_97 = l_Lean_mkAppN(x_88, x_96);
lean_dec_ref(x_96);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_99, 0, x_20);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*2, x_36);
if (x_42 == 0)
{
lean_ctor_set(x_41, 0, x_99);
x_100 = x_41;
goto block_101;
}
else
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_99);
x_100 = x_102;
goto block_101;
}
block_101:
{
return x_100;
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_112; 
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_105 = lean_ctor_get(x_39, 0);
x_112 = !lean_is_exclusive(x_39);
if (x_112 == 0)
{
x_106 = x_39;
x_107 = x_112;
goto block_111;
}
else
{
lean_inc(x_105);
lean_dec(x_39);
x_106 = lean_box(0);
x_107 = x_112;
goto block_111;
}
block_111:
{
lean_object* x_108; 
if (x_107 == 0)
{
x_108 = x_106;
goto block_109;
}
else
{
lean_object* x_110; 
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_105);
x_108 = x_110;
goto block_109;
}
block_109:
{
return x_108;
}
}
}
}
else
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; uint8_t x_120; 
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_113 = lean_ctor_get(x_37, 0);
x_120 = !lean_is_exclusive(x_37);
if (x_120 == 0)
{
x_114 = x_37;
x_115 = x_120;
goto block_119;
}
else
{
lean_inc(x_113);
lean_dec(x_37);
x_114 = lean_box(0);
x_115 = x_120;
goto block_119;
}
block_119:
{
lean_object* x_116; 
if (x_115 == 0)
{
x_116 = x_114;
goto block_117;
}
else
{
lean_object* x_118; 
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_113);
x_116 = x_118;
goto block_117;
}
block_117:
{
return x_116;
}
}
}
}
}
else
{
lean_object* x_121; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_121 = lean_infer_type(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec_ref(x_121);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_26);
x_123 = l_Lean_Meta_isExprDefEq(x_26, x_122, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_196; 
x_124 = lean_ctor_get(x_123, 0);
x_196 = !lean_is_exclusive(x_123);
if (x_196 == 0)
{
x_125 = x_123;
x_126 = x_196;
goto block_195;
}
else
{
lean_inc(x_124);
lean_dec(x_123);
x_125 = lean_box(0);
x_126 = x_196;
goto block_195;
}
block_195:
{
lean_object* x_127; uint8_t x_128; 
x_127 = l_Lean_Expr_constLevels_x21(x_32);
lean_dec_ref(x_32);
x_128 = lean_unbox(x_124);
lean_dec(x_124);
if (x_128 == 0)
{
lean_object* x_129; 
lean_del_object(x_125);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_129 = lean_infer_type(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec_ref(x_129);
lean_inc_ref(x_26);
x_131 = l_Lean_mkNot(x_26);
x_132 = l_Lean_Meta_isExprDefEq(x_131, x_130, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; uint8_t x_158; 
x_133 = lean_ctor_get(x_132, 0);
x_158 = !lean_is_exclusive(x_132);
if (x_158 == 0)
{
x_134 = x_132;
x_135 = x_158;
goto block_157;
}
else
{
lean_inc(x_133);
lean_dec(x_132);
x_134 = lean_box(0);
x_135 = x_158;
goto block_157;
}
block_157:
{
uint8_t x_136; 
x_136 = lean_unbox(x_133);
lean_dec(x_133);
if (x_136 == 0)
{
lean_del_object(x_134);
lean_dec(x_127);
lean_dec_ref(x_31);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec_ref(x_1);
goto block_12;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec_ref(x_2);
x_137 = lean_unsigned_to_nat(1u);
x_138 = lean_mk_empty_array_with_capacity(x_137);
lean_inc_ref(x_1);
x_139 = lean_array_push(x_138, x_1);
lean_inc_ref(x_17);
x_140 = l_Lean_Expr_beta(x_17, x_139);
x_141 = ((lean_object*)(l_Lean_Meta_rwIfWith___closed__11));
x_142 = l_Lean_mkConst(x_141, x_127);
x_143 = lean_unsigned_to_nat(6u);
x_144 = lean_mk_empty_array_with_capacity(x_143);
x_145 = lean_array_push(x_144, x_26);
x_146 = lean_array_push(x_145, x_23);
x_147 = lean_array_push(x_146, x_1);
x_148 = lean_array_push(x_147, x_31);
x_149 = lean_array_push(x_148, x_20);
x_150 = lean_array_push(x_149, x_17);
x_151 = l_Lean_mkAppN(x_142, x_150);
lean_dec_ref(x_150);
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_151);
x_153 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_153, 0, x_140);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set_uint8(x_153, sizeof(void*)*2, x_34);
if (x_135 == 0)
{
lean_ctor_set(x_134, 0, x_153);
x_154 = x_134;
goto block_155;
}
else
{
lean_object* x_156; 
x_156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_156, 0, x_153);
x_154 = x_156;
goto block_155;
}
block_155:
{
return x_154;
}
}
}
}
else
{
lean_object* x_159; lean_object* x_160; uint8_t x_161; uint8_t x_166; 
lean_dec(x_127);
lean_dec_ref(x_31);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_159 = lean_ctor_get(x_132, 0);
x_166 = !lean_is_exclusive(x_132);
if (x_166 == 0)
{
x_160 = x_132;
x_161 = x_166;
goto block_165;
}
else
{
lean_inc(x_159);
lean_dec(x_132);
x_160 = lean_box(0);
x_161 = x_166;
goto block_165;
}
block_165:
{
lean_object* x_162; 
if (x_161 == 0)
{
x_162 = x_160;
goto block_163;
}
else
{
lean_object* x_164; 
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_159);
x_162 = x_164;
goto block_163;
}
block_163:
{
return x_162;
}
}
}
}
else
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; uint8_t x_174; 
lean_dec(x_127);
lean_dec_ref(x_31);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_167 = lean_ctor_get(x_129, 0);
x_174 = !lean_is_exclusive(x_129);
if (x_174 == 0)
{
x_168 = x_129;
x_169 = x_174;
goto block_173;
}
else
{
lean_inc(x_167);
lean_dec(x_129);
x_168 = lean_box(0);
x_169 = x_174;
goto block_173;
}
block_173:
{
lean_object* x_170; 
if (x_169 == 0)
{
x_170 = x_168;
goto block_171;
}
else
{
lean_object* x_172; 
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_167);
x_170 = x_172;
goto block_171;
}
block_171:
{
return x_170;
}
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_175 = lean_unsigned_to_nat(1u);
x_176 = lean_mk_empty_array_with_capacity(x_175);
lean_inc_ref(x_1);
x_177 = lean_array_push(x_176, x_1);
lean_inc_ref(x_20);
x_178 = l_Lean_Expr_beta(x_20, x_177);
x_179 = ((lean_object*)(l_Lean_Meta_rwIfWith___closed__13));
x_180 = l_Lean_mkConst(x_179, x_127);
x_181 = lean_unsigned_to_nat(6u);
x_182 = lean_mk_empty_array_with_capacity(x_181);
x_183 = lean_array_push(x_182, x_26);
x_184 = lean_array_push(x_183, x_23);
x_185 = lean_array_push(x_184, x_1);
x_186 = lean_array_push(x_185, x_31);
x_187 = lean_array_push(x_186, x_20);
x_188 = lean_array_push(x_187, x_17);
x_189 = l_Lean_mkAppN(x_180, x_188);
lean_dec_ref(x_188);
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_189);
x_191 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_191, 0, x_178);
lean_ctor_set(x_191, 1, x_190);
lean_ctor_set_uint8(x_191, sizeof(void*)*2, x_34);
if (x_126 == 0)
{
lean_ctor_set(x_125, 0, x_191);
x_192 = x_125;
goto block_193;
}
else
{
lean_object* x_194; 
x_194 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_194, 0, x_191);
x_192 = x_194;
goto block_193;
}
block_193:
{
return x_192;
}
}
}
}
else
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; uint8_t x_204; 
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_197 = lean_ctor_get(x_123, 0);
x_204 = !lean_is_exclusive(x_123);
if (x_204 == 0)
{
x_198 = x_123;
x_199 = x_204;
goto block_203;
}
else
{
lean_inc(x_197);
lean_dec(x_123);
x_198 = lean_box(0);
x_199 = x_204;
goto block_203;
}
block_203:
{
lean_object* x_200; 
if (x_199 == 0)
{
x_200 = x_198;
goto block_201;
}
else
{
lean_object* x_202; 
x_202 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_202, 0, x_197);
x_200 = x_202;
goto block_201;
}
block_201:
{
return x_200;
}
}
}
}
else
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; uint8_t x_212; 
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_205 = lean_ctor_get(x_121, 0);
x_212 = !lean_is_exclusive(x_121);
if (x_212 == 0)
{
x_206 = x_121;
x_207 = x_212;
goto block_211;
}
else
{
lean_inc(x_205);
lean_dec(x_121);
x_206 = lean_box(0);
x_207 = x_212;
goto block_211;
}
block_211:
{
lean_object* x_208; 
if (x_207 == 0)
{
x_208 = x_206;
goto block_209;
}
else
{
lean_object* x_210; 
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_205);
x_208 = x_210;
goto block_209;
}
block_209:
{
return x_208;
}
}
}
}
}
}
else
{
lean_object* x_213; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_213 = lean_infer_type(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
lean_dec_ref(x_213);
x_215 = lean_obj_once(&l_Lean_Meta_rwIfWith___closed__17, &l_Lean_Meta_rwIfWith___closed__17_once, _init_l_Lean_Meta_rwIfWith___closed__17);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_23);
x_216 = l_Lean_Meta_mkEq(x_23, x_215, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
lean_dec_ref(x_216);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_218 = l_Lean_Meta_isExprDefEq(x_214, x_217, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; uint8_t x_221; uint8_t x_291; 
x_219 = lean_ctor_get(x_218, 0);
x_291 = !lean_is_exclusive(x_218);
if (x_291 == 0)
{
x_220 = x_218;
x_221 = x_291;
goto block_290;
}
else
{
lean_inc(x_219);
lean_dec(x_218);
x_220 = lean_box(0);
x_221 = x_291;
goto block_290;
}
block_290:
{
lean_object* x_222; uint8_t x_223; 
x_222 = l_Lean_Expr_constLevels_x21(x_27);
lean_dec_ref(x_27);
x_223 = lean_unbox(x_219);
lean_dec(x_219);
if (x_223 == 0)
{
lean_object* x_224; 
lean_del_object(x_220);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_224 = lean_infer_type(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
lean_dec_ref(x_224);
x_226 = lean_obj_once(&l_Lean_Meta_rwIfWith___closed__20, &l_Lean_Meta_rwIfWith___closed__20_once, _init_l_Lean_Meta_rwIfWith___closed__20);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_23);
x_227 = l_Lean_Meta_mkEq(x_23, x_226, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
lean_dec_ref(x_227);
x_229 = l_Lean_Meta_isExprDefEq(x_225, x_228, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; uint8_t x_232; uint8_t x_250; 
x_230 = lean_ctor_get(x_229, 0);
x_250 = !lean_is_exclusive(x_229);
if (x_250 == 0)
{
x_231 = x_229;
x_232 = x_250;
goto block_249;
}
else
{
lean_inc(x_230);
lean_dec(x_229);
x_231 = lean_box(0);
x_232 = x_250;
goto block_249;
}
block_249:
{
uint8_t x_233; 
x_233 = lean_unbox(x_230);
lean_dec(x_230);
if (x_233 == 0)
{
lean_del_object(x_231);
lean_dec(x_222);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec_ref(x_1);
goto block_12;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec_ref(x_2);
x_234 = ((lean_object*)(l_Lean_Meta_rwIfWith___closed__22));
x_235 = l_Lean_mkConst(x_234, x_222);
x_236 = lean_unsigned_to_nat(5u);
x_237 = lean_mk_empty_array_with_capacity(x_236);
x_238 = lean_array_push(x_237, x_26);
x_239 = lean_array_push(x_238, x_23);
x_240 = lean_array_push(x_239, x_20);
lean_inc_ref(x_17);
x_241 = lean_array_push(x_240, x_17);
x_242 = lean_array_push(x_241, x_1);
x_243 = l_Lean_mkAppN(x_235, x_242);
lean_dec_ref(x_242);
x_244 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_244, 0, x_243);
x_245 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_245, 0, x_17);
lean_ctor_set(x_245, 1, x_244);
lean_ctor_set_uint8(x_245, sizeof(void*)*2, x_29);
if (x_232 == 0)
{
lean_ctor_set(x_231, 0, x_245);
x_246 = x_231;
goto block_247;
}
else
{
lean_object* x_248; 
x_248 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_248, 0, x_245);
x_246 = x_248;
goto block_247;
}
block_247:
{
return x_246;
}
}
}
}
else
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; uint8_t x_258; 
lean_dec(x_222);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_251 = lean_ctor_get(x_229, 0);
x_258 = !lean_is_exclusive(x_229);
if (x_258 == 0)
{
x_252 = x_229;
x_253 = x_258;
goto block_257;
}
else
{
lean_inc(x_251);
lean_dec(x_229);
x_252 = lean_box(0);
x_253 = x_258;
goto block_257;
}
block_257:
{
lean_object* x_254; 
if (x_253 == 0)
{
x_254 = x_252;
goto block_255;
}
else
{
lean_object* x_256; 
x_256 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_256, 0, x_251);
x_254 = x_256;
goto block_255;
}
block_255:
{
return x_254;
}
}
}
}
else
{
lean_object* x_259; lean_object* x_260; uint8_t x_261; uint8_t x_266; 
lean_dec(x_225);
lean_dec(x_222);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_259 = lean_ctor_get(x_227, 0);
x_266 = !lean_is_exclusive(x_227);
if (x_266 == 0)
{
x_260 = x_227;
x_261 = x_266;
goto block_265;
}
else
{
lean_inc(x_259);
lean_dec(x_227);
x_260 = lean_box(0);
x_261 = x_266;
goto block_265;
}
block_265:
{
lean_object* x_262; 
if (x_261 == 0)
{
x_262 = x_260;
goto block_263;
}
else
{
lean_object* x_264; 
x_264 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_264, 0, x_259);
x_262 = x_264;
goto block_263;
}
block_263:
{
return x_262;
}
}
}
}
else
{
lean_object* x_267; lean_object* x_268; uint8_t x_269; uint8_t x_274; 
lean_dec(x_222);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_267 = lean_ctor_get(x_224, 0);
x_274 = !lean_is_exclusive(x_224);
if (x_274 == 0)
{
x_268 = x_224;
x_269 = x_274;
goto block_273;
}
else
{
lean_inc(x_267);
lean_dec(x_224);
x_268 = lean_box(0);
x_269 = x_274;
goto block_273;
}
block_273:
{
lean_object* x_270; 
if (x_269 == 0)
{
x_270 = x_268;
goto block_271;
}
else
{
lean_object* x_272; 
x_272 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_272, 0, x_267);
x_270 = x_272;
goto block_271;
}
block_271:
{
return x_270;
}
}
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_275 = ((lean_object*)(l_Lean_Meta_rwIfWith___closed__24));
x_276 = l_Lean_mkConst(x_275, x_222);
x_277 = lean_unsigned_to_nat(5u);
x_278 = lean_mk_empty_array_with_capacity(x_277);
x_279 = lean_array_push(x_278, x_26);
x_280 = lean_array_push(x_279, x_23);
lean_inc_ref(x_20);
x_281 = lean_array_push(x_280, x_20);
x_282 = lean_array_push(x_281, x_17);
x_283 = lean_array_push(x_282, x_1);
x_284 = l_Lean_mkAppN(x_276, x_283);
lean_dec_ref(x_283);
x_285 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_285, 0, x_284);
x_286 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_286, 0, x_20);
lean_ctor_set(x_286, 1, x_285);
lean_ctor_set_uint8(x_286, sizeof(void*)*2, x_29);
if (x_221 == 0)
{
lean_ctor_set(x_220, 0, x_286);
x_287 = x_220;
goto block_288;
}
else
{
lean_object* x_289; 
x_289 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_289, 0, x_286);
x_287 = x_289;
goto block_288;
}
block_288:
{
return x_287;
}
}
}
}
else
{
lean_object* x_292; lean_object* x_293; uint8_t x_294; uint8_t x_299; 
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_292 = lean_ctor_get(x_218, 0);
x_299 = !lean_is_exclusive(x_218);
if (x_299 == 0)
{
x_293 = x_218;
x_294 = x_299;
goto block_298;
}
else
{
lean_inc(x_292);
lean_dec(x_218);
x_293 = lean_box(0);
x_294 = x_299;
goto block_298;
}
block_298:
{
lean_object* x_295; 
if (x_294 == 0)
{
x_295 = x_293;
goto block_296;
}
else
{
lean_object* x_297; 
x_297 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_297, 0, x_292);
x_295 = x_297;
goto block_296;
}
block_296:
{
return x_295;
}
}
}
}
else
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; uint8_t x_307; 
lean_dec(x_214);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_300 = lean_ctor_get(x_216, 0);
x_307 = !lean_is_exclusive(x_216);
if (x_307 == 0)
{
x_301 = x_216;
x_302 = x_307;
goto block_306;
}
else
{
lean_inc(x_300);
lean_dec(x_216);
x_301 = lean_box(0);
x_302 = x_307;
goto block_306;
}
block_306:
{
lean_object* x_303; 
if (x_302 == 0)
{
x_303 = x_301;
goto block_304;
}
else
{
lean_object* x_305; 
x_305 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_305, 0, x_300);
x_303 = x_305;
goto block_304;
}
block_304:
{
return x_303;
}
}
}
}
else
{
lean_object* x_308; lean_object* x_309; uint8_t x_310; uint8_t x_315; 
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_308 = lean_ctor_get(x_213, 0);
x_315 = !lean_is_exclusive(x_213);
if (x_315 == 0)
{
x_309 = x_213;
x_310 = x_315;
goto block_314;
}
else
{
lean_inc(x_308);
lean_dec(x_213);
x_309 = lean_box(0);
x_310 = x_315;
goto block_314;
}
block_314:
{
lean_object* x_311; 
if (x_310 == 0)
{
x_311 = x_309;
goto block_312;
}
else
{
lean_object* x_313; 
x_313 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_313, 0, x_308);
x_311 = x_313;
goto block_312;
}
block_312:
{
return x_311;
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
lean_object* x_316; lean_object* x_317; uint8_t x_318; uint8_t x_323; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_316 = lean_ctor_get(x_13, 0);
x_323 = !lean_is_exclusive(x_13);
if (x_323 == 0)
{
x_317 = x_13;
x_318 = x_323;
goto block_322;
}
else
{
lean_inc(x_316);
lean_dec(x_13);
x_317 = lean_box(0);
x_318 = x_323;
goto block_322;
}
block_322:
{
lean_object* x_319; 
if (x_318 == 0)
{
x_319 = x_317;
goto block_320;
}
else
{
lean_object* x_321; 
x_321 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_321, 0, x_316);
x_319 = x_321;
goto block_320;
}
block_320:
{
return x_319;
}
}
}
block_12:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_box(0);
x_9 = 1;
x_10 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwIfWith___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_rwIfWith(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = l_Lean_Meta_isMatcherAppCore(x_5, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(x_1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg(x_1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_24; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = lean_ctor_get(x_11, 1);
x_13 = lean_ctor_get(x_11, 2);
x_14 = lean_ctor_get(x_11, 3);
x_15 = lean_ctor_get(x_11, 4);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_11, 0);
lean_dec(x_25);
x_16 = x_11;
x_17 = x_24;
goto block_23;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_18; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_10);
x_18 = x_16;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_12);
lean_ctor_set(x_22, 2, x_13);
lean_ctor_set(x_22, 3, x_14);
lean_ctor_set(x_22, 4, x_15);
x_18 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_st_ref_set(x_2, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_9);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__1(void) {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(32u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__0);
x_6 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_usize(x_6, 4, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_34; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_st_ref_take(x_1);
x_7 = lean_ctor_get(x_6, 4);
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_6, 2);
x_11 = lean_ctor_get(x_6, 3);
x_12 = lean_ctor_get(x_6, 5);
x_13 = lean_ctor_get(x_6, 6);
x_14 = lean_ctor_get(x_6, 7);
x_15 = lean_ctor_get(x_6, 8);
x_34 = !lean_is_exclusive(x_6);
if (x_34 == 0)
{
x_16 = x_6;
x_17 = x_34;
goto block_33;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_16 = lean_box(0);
x_17 = x_34;
goto block_33;
}
block_33:
{
uint64_t x_18; lean_object* x_19; uint8_t x_20; uint8_t x_31; 
x_18 = lean_ctor_get_uint64(x_7, sizeof(void*)*1);
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_7, 0);
lean_dec(x_32);
x_19 = x_7;
x_20 = x_31;
goto block_30;
}
else
{
lean_dec(x_7);
x_19 = lean_box(0);
x_20 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__1);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_21);
x_22 = x_19;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set_uint64(x_29, sizeof(void*)*1, x_18);
x_22 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_23; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 4, x_22);
x_23 = x_16;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_9);
lean_ctor_set(x_27, 2, x_10);
lean_ctor_set(x_27, 3, x_11);
lean_ctor_set(x_27, 4, x_22);
lean_ctor_set(x_27, 5, x_12);
lean_ctor_set(x_27, 6, x_13);
lean_ctor_set(x_27, 7, x_14);
lean_ctor_set(x_27, 8, x_15);
x_23 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_st_ref_set(x_1, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_5);
return x_25;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Meta_rwMatcher___lam__0(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3_spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_53; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3_spec__4(x_2, x_3, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
x_11 = x_9;
x_12 = x_53;
goto block_52;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_51; 
x_13 = lean_st_ref_take(x_6);
x_14 = lean_ctor_get(x_13, 4);
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 5);
x_20 = lean_ctor_get(x_13, 6);
x_21 = lean_ctor_get(x_13, 7);
x_22 = lean_ctor_get(x_13, 8);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
x_23 = x_13;
x_24 = x_51;
goto block_50;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_14);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = x_51;
goto block_50;
}
block_50:
{
uint64_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_49; 
x_25 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_26 = lean_ctor_get(x_14, 0);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
x_27 = x_14;
x_28 = x_49;
goto block_48;
}
else
{
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_box(0);
x_28 = x_49;
goto block_48;
}
block_48:
{
double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0);
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__1));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__2));
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_10);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_26, x_35);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_36);
x_37 = x_27;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set_uint64(x_47, sizeof(void*)*1, x_25);
x_37 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_38; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 4, x_37);
x_38 = x_23;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_16);
lean_ctor_set(x_45, 2, x_17);
lean_ctor_set(x_45, 3, x_18);
lean_ctor_set(x_45, 4, x_37);
lean_ctor_set(x_45, 5, x_19);
lean_ctor_set(x_45, 6, x_20);
lean_ctor_set(x_45, 7, x_21);
lean_ctor_set(x_45, 8, x_22);
x_38 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_st_ref_set(x_6, x_38);
x_40 = lean_box(0);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_40);
x_41 = x_11;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3_spec__4(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
if (x_11 == 0)
{
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6_spec__20___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
x_7 = l_Lean_instBEqMVarId_beq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6_spec__20___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6_spec__20___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___closed__0(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___closed__1(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___closed__0);
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___closed__1);
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_instBEqMVarId_beq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_usize_shift_right(x_2, x_6);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6_spec__20___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_instHashableMVarId_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 7);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(x_6, x_1);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_3, x_2);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_uget_borrowed(x_1, x_3);
x_18 = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(x_17, x_6);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_41; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_61; uint8_t x_63; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_box(0);
x_63 = lean_unbox(x_19);
lean_dec(x_19);
if (x_63 == 0)
{
lean_object* x_64; 
lean_inc(x_17);
x_64 = l_Lean_MVarId_getType(x_17, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
lean_inc(x_65);
x_66 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_65);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = l_Lean_Expr_isEq(x_65);
if (x_67 == 0)
{
uint8_t x_68; 
x_68 = l_Lean_Expr_isHEq(x_65);
lean_dec(x_65);
if (x_68 == 0)
{
x_10 = x_20;
goto block_14;
}
else
{
lean_object* x_69; 
x_69 = l_Lean_Meta_saveState___redArg(x_6, x_8);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_17);
x_71 = l_Lean_MVarId_assumption(x_17, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_71) == 0)
{
lean_dec(x_70);
x_41 = x_71;
goto block_42;
}
else
{
lean_object* x_72; uint8_t x_73; uint8_t x_90; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_90 = l_Lean_Exception_isInterrupt(x_72);
if (x_90 == 0)
{
uint8_t x_91; 
x_91 = l_Lean_Exception_isRuntime(x_72);
x_73 = x_91;
goto block_89;
}
else
{
lean_dec(x_72);
x_73 = x_90;
goto block_89;
}
block_89:
{
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec_ref(x_71);
x_74 = l_Lean_Meta_SavedState_restore___redArg(x_70, x_6, x_8);
lean_dec(x_70);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
lean_dec_ref(x_74);
x_75 = l_Lean_Meta_saveState___redArg(x_6, x_8);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_17);
x_77 = l_Lean_MVarId_hrefl(x_17, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_77) == 0)
{
lean_dec(x_76);
x_41 = x_77;
goto block_42;
}
else
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = l_Lean_Exception_isInterrupt(x_78);
if (x_79 == 0)
{
uint8_t x_80; 
x_80 = l_Lean_Exception_isRuntime(x_78);
x_43 = x_76;
x_44 = x_77;
x_45 = x_80;
goto block_60;
}
else
{
lean_dec(x_78);
x_43 = x_76;
x_44 = x_77;
x_45 = x_79;
goto block_60;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_88; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_81 = lean_ctor_get(x_75, 0);
x_88 = !lean_is_exclusive(x_75);
if (x_88 == 0)
{
x_82 = x_75;
x_83 = x_88;
goto block_87;
}
else
{
lean_inc(x_81);
lean_dec(x_75);
x_82 = lean_box(0);
x_83 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_84; 
if (x_83 == 0)
{
x_84 = x_82;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_81);
x_84 = x_86;
goto block_85;
}
block_85:
{
return x_84;
}
}
}
}
else
{
x_41 = x_74;
goto block_42;
}
}
else
{
lean_dec(x_70);
x_41 = x_71;
goto block_42;
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_99; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_92 = lean_ctor_get(x_69, 0);
x_99 = !lean_is_exclusive(x_69);
if (x_99 == 0)
{
x_93 = x_69;
x_94 = x_99;
goto block_98;
}
else
{
lean_inc(x_92);
lean_dec(x_69);
x_93 = lean_box(0);
x_94 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_95; 
if (x_94 == 0)
{
x_95 = x_93;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_92);
x_95 = x_97;
goto block_96;
}
block_96:
{
return x_95;
}
}
}
}
}
else
{
lean_object* x_100; 
lean_dec(x_65);
x_100 = l_Lean_Meta_saveState___redArg(x_6, x_8);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec_ref(x_100);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_17);
x_102 = l_Lean_MVarId_assumption(x_17, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_102) == 0)
{
lean_dec(x_101);
x_21 = x_102;
goto block_22;
}
else
{
lean_object* x_103; uint8_t x_104; uint8_t x_121; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_121 = l_Lean_Exception_isInterrupt(x_103);
if (x_121 == 0)
{
uint8_t x_122; 
x_122 = l_Lean_Exception_isRuntime(x_103);
x_104 = x_122;
goto block_120;
}
else
{
lean_dec(x_103);
x_104 = x_121;
goto block_120;
}
block_120:
{
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec_ref(x_102);
x_105 = l_Lean_Meta_SavedState_restore___redArg(x_101, x_6, x_8);
lean_dec(x_101);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; 
lean_dec_ref(x_105);
x_106 = l_Lean_Meta_saveState___redArg(x_6, x_8);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec_ref(x_106);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_17);
x_108 = l_Lean_MVarId_refl(x_17, x_67, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_108) == 0)
{
lean_dec(x_107);
x_21 = x_108;
goto block_22;
}
else
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = l_Lean_Exception_isInterrupt(x_109);
if (x_110 == 0)
{
uint8_t x_111; 
x_111 = l_Lean_Exception_isRuntime(x_109);
x_23 = x_107;
x_24 = x_108;
x_25 = x_111;
goto block_40;
}
else
{
lean_dec(x_109);
x_23 = x_107;
x_24 = x_108;
x_25 = x_110;
goto block_40;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_119; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_112 = lean_ctor_get(x_106, 0);
x_119 = !lean_is_exclusive(x_106);
if (x_119 == 0)
{
x_113 = x_106;
x_114 = x_119;
goto block_118;
}
else
{
lean_inc(x_112);
lean_dec(x_106);
x_113 = lean_box(0);
x_114 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_115; 
if (x_114 == 0)
{
x_115 = x_113;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_112);
x_115 = x_117;
goto block_116;
}
block_116:
{
return x_115;
}
}
}
}
else
{
x_21 = x_105;
goto block_22;
}
}
else
{
lean_dec(x_101);
x_21 = x_102;
goto block_22;
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_130; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_123 = lean_ctor_get(x_100, 0);
x_130 = !lean_is_exclusive(x_100);
if (x_130 == 0)
{
x_124 = x_100;
x_125 = x_130;
goto block_129;
}
else
{
lean_inc(x_123);
lean_dec(x_100);
x_124 = lean_box(0);
x_125 = x_130;
goto block_129;
}
block_129:
{
lean_object* x_126; 
if (x_125 == 0)
{
x_126 = x_124;
goto block_127;
}
else
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_123);
x_126 = x_128;
goto block_127;
}
block_127:
{
return x_126;
}
}
}
}
}
else
{
lean_object* x_131; 
lean_dec(x_65);
x_131 = l_Lean_Meta_saveState___redArg(x_6, x_8);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec_ref(x_131);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_17);
x_133 = l_Lean_MVarId_assumption(x_17, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_133) == 0)
{
lean_dec(x_132);
x_61 = x_133;
goto block_62;
}
else
{
lean_object* x_134; uint8_t x_135; uint8_t x_151; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_151 = l_Lean_Exception_isInterrupt(x_134);
if (x_151 == 0)
{
uint8_t x_152; 
x_152 = l_Lean_Exception_isRuntime(x_134);
x_135 = x_152;
goto block_150;
}
else
{
lean_dec(x_134);
x_135 = x_151;
goto block_150;
}
block_150:
{
if (x_135 == 0)
{
lean_object* x_136; 
lean_dec_ref(x_133);
x_136 = l_Lean_Meta_SavedState_restore___redArg(x_132, x_6, x_8);
lean_dec(x_132);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; uint8_t x_138; uint8_t x_148; 
x_148 = !lean_is_exclusive(x_136);
if (x_148 == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_136, 0);
lean_dec(x_149);
x_137 = x_136;
x_138 = x_148;
goto block_147;
}
else
{
lean_dec(x_136);
x_137 = lean_box(0);
x_138 = x_148;
goto block_147;
}
block_147:
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__5);
lean_inc(x_17);
if (x_138 == 0)
{
lean_ctor_set_tag(x_137, 1);
lean_ctor_set(x_137, 0, x_17);
x_140 = x_137;
goto block_145;
}
else
{
lean_object* x_146; 
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_17);
x_140 = x_146;
goto block_145;
}
block_145:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_141 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(x_143, x_5, x_6, x_7, x_8);
x_61 = x_144;
goto block_62;
}
}
}
else
{
x_61 = x_136;
goto block_62;
}
}
else
{
lean_dec(x_132);
x_61 = x_133;
goto block_62;
}
}
}
}
else
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; uint8_t x_160; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_153 = lean_ctor_get(x_131, 0);
x_160 = !lean_is_exclusive(x_131);
if (x_160 == 0)
{
x_154 = x_131;
x_155 = x_160;
goto block_159;
}
else
{
lean_inc(x_153);
lean_dec(x_131);
x_154 = lean_box(0);
x_155 = x_160;
goto block_159;
}
block_159:
{
lean_object* x_156; 
if (x_155 == 0)
{
x_156 = x_154;
goto block_157;
}
else
{
lean_object* x_158; 
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_153);
x_156 = x_158;
goto block_157;
}
block_157:
{
return x_156;
}
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; uint8_t x_168; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_161 = lean_ctor_get(x_64, 0);
x_168 = !lean_is_exclusive(x_64);
if (x_168 == 0)
{
x_162 = x_64;
x_163 = x_168;
goto block_167;
}
else
{
lean_inc(x_161);
lean_dec(x_64);
x_162 = lean_box(0);
x_163 = x_168;
goto block_167;
}
block_167:
{
lean_object* x_164; 
if (x_163 == 0)
{
x_164 = x_162;
goto block_165;
}
else
{
lean_object* x_166; 
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_161);
x_164 = x_166;
goto block_165;
}
block_165:
{
return x_164;
}
}
}
}
else
{
x_10 = x_20;
goto block_14;
}
block_22:
{
if (lean_obj_tag(x_21) == 0)
{
lean_dec_ref(x_21);
x_10 = x_20;
goto block_14;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_21;
}
}
block_40:
{
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec_ref(x_24);
x_26 = l_Lean_Meta_SavedState_restore___redArg(x_23, x_6, x_8);
lean_dec_ref(x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; uint8_t x_38; 
x_38 = !lean_is_exclusive(x_26);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_26, 0);
lean_dec(x_39);
x_27 = x_26;
x_28 = x_38;
goto block_37;
}
else
{
lean_dec(x_26);
x_27 = lean_box(0);
x_28 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1);
lean_inc(x_17);
if (x_28 == 0)
{
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 0, x_17);
x_30 = x_27;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_17);
x_30 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(x_33, x_5, x_6, x_7, x_8);
x_21 = x_34;
goto block_22;
}
}
}
else
{
x_21 = x_26;
goto block_22;
}
}
else
{
lean_dec_ref(x_23);
x_21 = x_24;
goto block_22;
}
}
block_42:
{
if (lean_obj_tag(x_41) == 0)
{
lean_dec_ref(x_41);
x_10 = x_20;
goto block_14;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_41;
}
}
block_60:
{
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec_ref(x_44);
x_46 = l_Lean_Meta_SavedState_restore___redArg(x_43, x_6, x_8);
lean_dec_ref(x_43);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; uint8_t x_58; 
x_58 = !lean_is_exclusive(x_46);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_46, 0);
lean_dec(x_59);
x_47 = x_46;
x_48 = x_58;
goto block_57;
}
else
{
lean_dec(x_46);
x_47 = lean_box(0);
x_48 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1);
lean_inc(x_17);
if (x_48 == 0)
{
lean_ctor_set_tag(x_47, 1);
lean_ctor_set(x_47, 0, x_17);
x_50 = x_47;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_17);
x_50 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(x_53, x_5, x_6, x_7, x_8);
x_41 = x_54;
goto block_42;
}
}
}
else
{
x_41 = x_46;
goto block_42;
}
}
else
{
lean_dec_ref(x_43);
x_41 = x_44;
goto block_42;
}
}
block_62:
{
if (lean_obj_tag(x_61) == 0)
{
lean_dec_ref(x_61);
x_10 = x_20;
goto block_14;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_61;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; uint8_t x_176; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_169 = lean_ctor_get(x_18, 0);
x_176 = !lean_is_exclusive(x_18);
if (x_176 == 0)
{
x_170 = x_18;
x_171 = x_176;
goto block_175;
}
else
{
lean_inc(x_169);
lean_dec(x_18);
x_170 = lean_box(0);
x_171 = x_176;
goto block_175;
}
block_175:
{
lean_object* x_172; 
if (x_171 == 0)
{
x_172 = x_170;
goto block_173;
}
else
{
lean_object* x_174; 
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_169);
x_172 = x_174;
goto block_173;
}
block_173:
{
return x_172;
}
}
}
}
block_14:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
x_4 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_2, x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_19; 
x_16 = lean_array_uget_borrowed(x_1, x_2);
x_19 = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(x_16, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
goto block_18;
}
else
{
x_10 = x_4;
goto block_14;
}
}
else
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec_ref(x_19);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
x_10 = x_4;
goto block_14;
}
else
{
goto block_18;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
lean_dec_ref(x_4);
x_24 = lean_ctor_get(x_19, 0);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
x_25 = x_19;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
block_18:
{
lean_object* x_17; 
lean_inc(x_16);
x_17 = lean_array_push(x_4, x_16);
x_10 = x_17;
goto block_14;
}
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_4);
return x_32;
}
block_14:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Expr_mvarId_x21(x_5);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
x_6 = x_1;
x_7 = x_14;
goto block_13;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_4);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_8);
x_9 = x_6;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_2);
x_9 = x_12;
goto block_11;
}
block_11:
{
x_1 = x_5;
x_2 = x_9;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__8));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__11));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__13));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__15));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__21));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__24(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__23));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__26(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__25));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_18; lean_object* x_19; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_117; size_t x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_147; size_t x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_191; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_1);
x_191 = lean_infer_type(x_1, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; uint8_t x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
lean_dec_ref(x_191);
x_193 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_194 = l_Lean_Meta_forallMetaTelescope(x_192, x_193, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; uint8_t x_262; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
lean_dec_ref(x_194);
x_196 = lean_ctor_get(x_195, 1);
x_197 = lean_ctor_get(x_195, 0);
x_262 = !lean_is_exclusive(x_195);
if (x_262 == 0)
{
x_198 = x_195;
x_199 = x_262;
goto block_261;
}
else
{
lean_inc(x_196);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_box(0);
x_199 = x_262;
goto block_261;
}
block_261:
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; uint8_t x_259; 
x_200 = lean_ctor_get(x_196, 1);
x_259 = !lean_is_exclusive(x_196);
if (x_259 == 0)
{
lean_object* x_260; 
x_260 = lean_ctor_get(x_196, 0);
lean_dec(x_260);
x_201 = x_196;
x_202 = x_259;
goto block_258;
}
else
{
lean_inc(x_200);
lean_dec(x_196);
x_201 = lean_box(0);
x_202 = x_259;
goto block_258;
}
block_258:
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
lean_inc(x_2);
x_243 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg(x_2, x_9);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
lean_dec_ref(x_243);
x_245 = lean_unbox(x_244);
lean_dec(x_244);
if (x_245 == 0)
{
lean_dec(x_2);
x_203 = x_7;
x_204 = x_8;
x_205 = x_9;
x_206 = x_10;
goto block_242;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_246 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__26, &l_Lean_Meta_rwMatcher___lam__1___closed__26_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__26);
lean_inc(x_200);
x_247 = l_Lean_indentExpr(x_200);
x_248 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
x_249 = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(x_2, x_248, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_249) == 0)
{
lean_dec_ref(x_249);
x_203 = x_7;
x_204 = x_8;
x_205 = x_9;
x_206 = x_10;
goto block_242;
}
else
{
lean_object* x_250; lean_object* x_251; uint8_t x_252; uint8_t x_257; 
lean_del_object(x_201);
lean_dec(x_200);
lean_del_object(x_198);
lean_dec(x_197);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_250 = lean_ctor_get(x_249, 0);
x_257 = !lean_is_exclusive(x_249);
if (x_257 == 0)
{
x_251 = x_249;
x_252 = x_257;
goto block_256;
}
else
{
lean_inc(x_250);
lean_dec(x_249);
x_251 = lean_box(0);
x_252 = x_257;
goto block_256;
}
block_256:
{
lean_object* x_253; 
if (x_252 == 0)
{
x_253 = x_251;
goto block_254;
}
else
{
lean_object* x_255; 
x_255 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_255, 0, x_250);
x_253 = x_255;
goto block_254;
}
block_254:
{
return x_253;
}
}
}
}
block_242:
{
lean_object* x_207; size_t x_208; size_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_207 = l_Lean_mkAppN(x_1, x_197);
x_208 = lean_array_size(x_197);
x_209 = 0;
x_210 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4(x_208, x_209, x_197);
x_211 = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__18));
x_212 = lean_unsigned_to_nat(4u);
x_213 = l_Lean_Expr_isAppOfArity(x_200, x_211, x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_214 = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__20));
x_215 = lean_unsigned_to_nat(3u);
x_216 = l_Lean_Expr_isAppOfArity(x_200, x_214, x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec_ref(x_210);
lean_dec_ref(x_207);
lean_dec(x_200);
lean_dec_ref(x_5);
x_217 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__22, &l_Lean_Meta_rwMatcher___lam__1___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__22);
x_218 = l_Lean_MessageData_ofConstName(x_4, x_216);
if (x_202 == 0)
{
lean_ctor_set_tag(x_201, 7);
lean_ctor_set(x_201, 1, x_218);
lean_ctor_set(x_201, 0, x_217);
x_219 = x_201;
goto block_233;
}
else
{
lean_object* x_234; 
x_234 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_234, 0, x_217);
lean_ctor_set(x_234, 1, x_218);
x_219 = x_234;
goto block_233;
}
block_233:
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__24, &l_Lean_Meta_rwMatcher___lam__1___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__24);
if (x_199 == 0)
{
lean_ctor_set_tag(x_198, 7);
lean_ctor_set(x_198, 1, x_220);
lean_ctor_set(x_198, 0, x_219);
x_221 = x_198;
goto block_231;
}
else
{
lean_object* x_232; 
x_232 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_232, 0, x_219);
lean_ctor_set(x_232, 1, x_220);
x_221 = x_232;
goto block_231;
}
block_231:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; uint8_t x_230; 
x_222 = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(x_221, x_203, x_204, x_205, x_206);
lean_dec(x_206);
lean_dec_ref(x_205);
lean_dec(x_204);
lean_dec_ref(x_203);
x_223 = lean_ctor_get(x_222, 0);
x_230 = !lean_is_exclusive(x_222);
if (x_230 == 0)
{
x_224 = x_222;
x_225 = x_230;
goto block_229;
}
else
{
lean_inc(x_223);
lean_dec(x_222);
x_224 = lean_box(0);
x_225 = x_230;
goto block_229;
}
block_229:
{
lean_object* x_226; 
if (x_225 == 0)
{
x_226 = x_224;
goto block_227;
}
else
{
lean_object* x_228; 
x_228 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_228, 0, x_223);
x_226 = x_228;
goto block_227;
}
block_227:
{
return x_226;
}
}
}
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_del_object(x_201);
lean_del_object(x_198);
x_235 = l_Lean_Expr_appFn_x21(x_200);
x_236 = l_Lean_Expr_appArg_x21(x_235);
lean_dec_ref(x_235);
x_237 = l_Lean_Expr_appArg_x21(x_200);
lean_dec(x_200);
x_147 = x_207;
x_148 = x_209;
x_149 = x_210;
x_150 = x_213;
x_151 = x_236;
x_152 = x_237;
x_153 = x_203;
x_154 = x_204;
x_155 = x_205;
x_156 = x_206;
goto block_190;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_del_object(x_201);
lean_del_object(x_198);
x_238 = l_Lean_Expr_appFn_x21(x_200);
x_239 = l_Lean_Expr_appFn_x21(x_238);
lean_dec_ref(x_238);
x_240 = l_Lean_Expr_appArg_x21(x_239);
lean_dec_ref(x_239);
x_241 = l_Lean_Expr_appArg_x21(x_200);
lean_dec(x_200);
x_147 = x_207;
x_148 = x_209;
x_149 = x_210;
x_150 = x_3;
x_151 = x_240;
x_152 = x_241;
x_153 = x_203;
x_154 = x_204;
x_155 = x_205;
x_156 = x_206;
goto block_190;
}
}
}
}
}
else
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; uint8_t x_270; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_263 = lean_ctor_get(x_194, 0);
x_270 = !lean_is_exclusive(x_194);
if (x_270 == 0)
{
x_264 = x_194;
x_265 = x_270;
goto block_269;
}
else
{
lean_inc(x_263);
lean_dec(x_194);
x_264 = lean_box(0);
x_265 = x_270;
goto block_269;
}
block_269:
{
lean_object* x_266; 
if (x_265 == 0)
{
x_266 = x_264;
goto block_267;
}
else
{
lean_object* x_268; 
x_268 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_268, 0, x_263);
x_266 = x_268;
goto block_267;
}
block_267:
{
return x_266;
}
}
}
}
else
{
lean_object* x_271; lean_object* x_272; uint8_t x_273; uint8_t x_278; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_271 = lean_ctor_get(x_191, 0);
x_278 = !lean_is_exclusive(x_191);
if (x_278 == 0)
{
x_272 = x_191;
x_273 = x_278;
goto block_277;
}
else
{
lean_inc(x_271);
lean_dec(x_191);
x_272 = lean_box(0);
x_273 = x_278;
goto block_277;
}
block_277:
{
lean_object* x_274; 
if (x_273 == 0)
{
x_274 = x_272;
goto block_275;
}
else
{
lean_object* x_276; 
x_276 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_276, 0, x_271);
x_274 = x_276;
goto block_275;
}
block_275:
{
return x_274;
}
}
}
block_17:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_3);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
block_29:
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_12 = x_18;
x_13 = x_20;
goto block_17;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_dec_ref(x_18);
x_21 = lean_ctor_get(x_19, 0);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
x_22 = x_19;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
block_50:
{
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec_ref(x_36);
x_39 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__1, &l_Lean_Meta_rwMatcher___lam__1___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__1);
x_40 = l_Lean_MessageData_ofExpr(x_37);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__3, &l_Lean_Meta_rwMatcher___lam__1___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__3);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Exception_toMessageData(x_30);
x_45 = l_Lean_indentD(x_44);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__5, &l_Lean_Meta_rwMatcher___lam__1___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__5);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(x_48, x_32, x_34, x_33, x_35);
lean_dec(x_35);
lean_dec_ref(x_33);
lean_dec(x_34);
lean_dec_ref(x_32);
x_18 = x_31;
x_19 = x_49;
goto block_29;
}
else
{
lean_dec_ref(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_dec_ref(x_30);
x_18 = x_31;
x_19 = x_36;
goto block_29;
}
}
block_67:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(x_53, x_55);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(x_51, x_55);
if (x_52 == 0)
{
lean_object* x_61; 
lean_dec(x_57);
lean_dec_ref(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
x_12 = x_59;
x_13 = x_61;
goto block_17;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec_ref(x_60);
lean_inc(x_57);
lean_inc_ref(x_56);
lean_inc(x_55);
lean_inc_ref(x_54);
lean_inc(x_62);
x_63 = l_Lean_Meta_mkEqOfHEq(x_62, x_3, x_54, x_55, x_56, x_57);
if (lean_obj_tag(x_63) == 0)
{
lean_dec(x_62);
lean_dec(x_57);
lean_dec_ref(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
x_18 = x_59;
x_19 = x_63;
goto block_29;
}
else
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = l_Lean_Exception_isInterrupt(x_64);
if (x_65 == 0)
{
uint8_t x_66; 
lean_inc(x_64);
x_66 = l_Lean_Exception_isRuntime(x_64);
x_30 = x_64;
x_31 = x_59;
x_32 = x_54;
x_33 = x_56;
x_34 = x_55;
x_35 = x_57;
x_36 = x_63;
x_37 = x_62;
x_38 = x_66;
goto block_50;
}
else
{
x_30 = x_64;
x_31 = x_59;
x_32 = x_54;
x_33 = x_56;
x_34 = x_55;
x_35 = x_57;
x_36 = x_63;
x_37 = x_62;
x_38 = x_65;
goto block_50;
}
}
}
}
block_98:
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_array_get_size(x_75);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_nat_dec_eq(x_76, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_97; 
lean_dec_ref(x_74);
lean_dec_ref(x_68);
x_79 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__7, &l_Lean_Meta_rwMatcher___lam__1___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__7);
x_80 = l_Lean_MessageData_ofConstName(x_4, x_78);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__9, &l_Lean_Meta_rwMatcher___lam__1___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__9);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_array_to_list(x_75);
x_85 = lean_box(0);
x_86 = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__7(x_84, x_85);
x_87 = l_Lean_MessageData_ofList(x_86);
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(x_88, x_71, x_72, x_69, x_70);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_72);
lean_dec_ref(x_71);
x_90 = lean_ctor_get(x_89, 0);
x_97 = !lean_is_exclusive(x_89);
if (x_97 == 0)
{
x_91 = x_89;
x_92 = x_97;
goto block_96;
}
else
{
lean_inc(x_90);
lean_dec(x_89);
x_91 = lean_box(0);
x_92 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_93; 
if (x_92 == 0)
{
x_93 = x_91;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_90);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
else
{
lean_dec_ref(x_75);
lean_dec(x_4);
x_51 = x_68;
x_52 = x_73;
x_53 = x_74;
x_54 = x_71;
x_55 = x_72;
x_56 = x_69;
x_57 = x_70;
goto block_67;
}
}
block_116:
{
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec_ref(x_106);
x_68 = x_100;
x_69 = x_99;
x_70 = x_102;
x_71 = x_101;
x_72 = x_103;
x_73 = x_104;
x_74 = x_105;
x_75 = x_107;
goto block_98;
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; uint8_t x_115; 
lean_dec_ref(x_105);
lean_dec(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec_ref(x_100);
lean_dec_ref(x_99);
lean_dec(x_4);
x_108 = lean_ctor_get(x_106, 0);
x_115 = !lean_is_exclusive(x_106);
if (x_115 == 0)
{
x_109 = x_106;
x_110 = x_115;
goto block_114;
}
else
{
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_box(0);
x_110 = x_115;
goto block_114;
}
block_114:
{
lean_object* x_111; 
if (x_110 == 0)
{
x_111 = x_109;
goto block_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_108);
x_111 = x_113;
goto block_112;
}
block_112:
{
return x_111;
}
}
}
}
block_146:
{
lean_object* x_126; size_t x_127; lean_object* x_128; 
x_126 = lean_box(0);
x_127 = lean_array_size(x_119);
lean_inc(x_125);
lean_inc_ref(x_124);
lean_inc(x_123);
lean_inc_ref(x_122);
x_128 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8(x_119, x_127, x_118, x_126, x_122, x_123, x_124, x_125);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
lean_dec_ref(x_128);
x_129 = lean_unsigned_to_nat(0u);
x_130 = lean_array_get_size(x_119);
x_131 = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__10));
x_132 = lean_nat_dec_lt(x_129, x_130);
if (x_132 == 0)
{
lean_dec_ref(x_119);
x_68 = x_117;
x_69 = x_124;
x_70 = x_125;
x_71 = x_122;
x_72 = x_123;
x_73 = x_120;
x_74 = x_121;
x_75 = x_131;
goto block_98;
}
else
{
uint8_t x_133; 
x_133 = lean_nat_dec_le(x_130, x_130);
if (x_133 == 0)
{
if (x_132 == 0)
{
lean_dec_ref(x_119);
x_68 = x_117;
x_69 = x_124;
x_70 = x_125;
x_71 = x_122;
x_72 = x_123;
x_73 = x_120;
x_74 = x_121;
x_75 = x_131;
goto block_98;
}
else
{
size_t x_134; lean_object* x_135; 
x_134 = lean_usize_of_nat(x_130);
x_135 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9(x_119, x_118, x_134, x_131, x_122, x_123, x_124, x_125);
lean_dec_ref(x_119);
x_99 = x_124;
x_100 = x_117;
x_101 = x_122;
x_102 = x_125;
x_103 = x_123;
x_104 = x_120;
x_105 = x_121;
x_106 = x_135;
goto block_116;
}
}
else
{
size_t x_136; lean_object* x_137; 
x_136 = lean_usize_of_nat(x_130);
x_137 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9(x_119, x_118, x_136, x_131, x_122, x_123, x_124, x_125);
lean_dec_ref(x_119);
x_99 = x_124;
x_100 = x_117;
x_101 = x_122;
x_102 = x_125;
x_103 = x_123;
x_104 = x_120;
x_105 = x_121;
x_106 = x_137;
goto block_116;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_145; 
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec(x_123);
lean_dec_ref(x_122);
lean_dec_ref(x_121);
lean_dec_ref(x_119);
lean_dec_ref(x_117);
lean_dec(x_4);
x_138 = lean_ctor_get(x_128, 0);
x_145 = !lean_is_exclusive(x_128);
if (x_145 == 0)
{
x_139 = x_128;
x_140 = x_145;
goto block_144;
}
else
{
lean_inc(x_138);
lean_dec(x_128);
x_139 = lean_box(0);
x_140 = x_145;
goto block_144;
}
block_144:
{
lean_object* x_141; 
if (x_140 == 0)
{
x_141 = x_139;
goto block_142;
}
else
{
lean_object* x_143; 
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_138);
x_141 = x_143;
goto block_142;
}
block_142:
{
return x_141;
}
}
}
}
block_190:
{
lean_object* x_157; 
lean_inc(x_156);
lean_inc_ref(x_155);
lean_inc(x_154);
lean_inc_ref(x_153);
lean_inc_ref(x_151);
lean_inc_ref(x_5);
x_157 = l_Lean_Meta_isExprDefEq(x_5, x_151, x_153, x_154, x_155, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; uint8_t x_159; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
lean_dec_ref(x_157);
x_159 = lean_unbox(x_158);
lean_dec(x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; uint8_t x_181; 
lean_dec_ref(x_152);
lean_dec_ref(x_149);
lean_dec_ref(x_147);
x_160 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__12, &l_Lean_Meta_rwMatcher___lam__1___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__12);
x_161 = l_Lean_MessageData_ofExpr(x_151);
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__14, &l_Lean_Meta_rwMatcher___lam__1___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__14);
x_164 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_165 = l_Lean_MessageData_ofConstName(x_4, x_6);
x_166 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__16, &l_Lean_Meta_rwMatcher___lam__1___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__16);
x_168 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_169 = l_Lean_MessageData_ofExpr(x_5);
x_170 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
x_172 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
x_173 = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(x_172, x_153, x_154, x_155, x_156);
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec_ref(x_153);
x_174 = lean_ctor_get(x_173, 0);
x_181 = !lean_is_exclusive(x_173);
if (x_181 == 0)
{
x_175 = x_173;
x_176 = x_181;
goto block_180;
}
else
{
lean_inc(x_174);
lean_dec(x_173);
x_175 = lean_box(0);
x_176 = x_181;
goto block_180;
}
block_180:
{
lean_object* x_177; 
if (x_176 == 0)
{
x_177 = x_175;
goto block_178;
}
else
{
lean_object* x_179; 
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_174);
x_177 = x_179;
goto block_178;
}
block_178:
{
return x_177;
}
}
}
else
{
lean_dec_ref(x_151);
lean_dec_ref(x_5);
x_117 = x_147;
x_118 = x_148;
x_119 = x_149;
x_120 = x_150;
x_121 = x_152;
x_122 = x_153;
x_123 = x_154;
x_124 = x_155;
x_125 = x_156;
goto block_146;
}
}
else
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; uint8_t x_189; 
lean_dec(x_156);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec_ref(x_153);
lean_dec_ref(x_152);
lean_dec_ref(x_151);
lean_dec_ref(x_149);
lean_dec_ref(x_147);
lean_dec_ref(x_5);
lean_dec(x_4);
x_182 = lean_ctor_get(x_157, 0);
x_189 = !lean_is_exclusive(x_157);
if (x_189 == 0)
{
x_183 = x_157;
x_184 = x_189;
goto block_188;
}
else
{
lean_inc(x_182);
lean_dec(x_157);
x_183 = lean_box(0);
x_184 = x_189;
goto block_188;
}
block_188:
{
lean_object* x_185; 
if (x_184 == 0)
{
x_185 = x_183;
goto block_186;
}
else
{
lean_object* x_187; 
x_187 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_187, 0, x_182);
x_185 = x_187;
goto block_186;
}
block_186:
{
return x_185;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
x_13 = lean_unbox(x_6);
x_14 = l_Lean_Meta_rwMatcher___lam__1(x_1, x_2, x_12, x_4, x_5, x_13, x_7, x_8, x_9, x_10);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = l_Lean_exceptEmoji___redArg(x_4);
x_11 = l_Lean_stringToMessageData(x_10);
x_12 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_MessageData_ofConstName(x_1, x_2);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_indentExpr(x_3);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lean_Meta_rwMatcher___lam__2(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_16; 
x_16 = lean_usize_dec_eq(x_3, x_4);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_20; lean_object* x_22; 
x_17 = lean_array_uget_borrowed(x_2, x_3);
x_22 = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(x_17, x_7);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
goto block_19;
}
else
{
x_20 = x_1;
goto block_21;
}
}
else
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec_ref(x_22);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
x_20 = x_26;
goto block_21;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
lean_dec_ref(x_5);
x_27 = lean_ctor_get(x_22, 0);
x_34 = !lean_is_exclusive(x_22);
if (x_34 == 0)
{
x_28 = x_22;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
block_19:
{
lean_object* x_18; 
lean_inc(x_17);
x_18 = lean_array_push(x_5, x_17);
x_11 = x_18;
goto block_15;
}
block_21:
{
if (x_20 == 0)
{
x_11 = x_5;
goto block_15;
}
else
{
goto block_19;
}
}
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_5);
return x_35;
}
block_15:
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_5 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(x_11, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_20; lean_object* x_21; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; size_t x_117; size_t x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; uint8_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_53 = l_Lean_mkAppN(x_2, x_3);
x_117 = lean_array_size(x_3);
x_118 = 0;
x_119 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4(x_117, x_118, x_3);
x_192 = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__18));
x_193 = lean_unsigned_to_nat(4u);
x_194 = l_Lean_Expr_isAppOfArity(x_7, x_192, x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_195 = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__20));
x_196 = lean_unsigned_to_nat(3u);
x_197 = l_Lean_Expr_isAppOfArity(x_7, x_195, x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; uint8_t x_211; 
lean_dec_ref(x_119);
lean_dec_ref(x_53);
lean_dec_ref(x_6);
x_198 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__22, &l_Lean_Meta_rwMatcher___lam__1___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__22);
x_199 = l_Lean_MessageData_ofConstName(x_4, x_5);
x_200 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__24, &l_Lean_Meta_rwMatcher___lam__1___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__24);
x_202 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
x_203 = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(x_202, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_204 = lean_ctor_get(x_203, 0);
x_211 = !lean_is_exclusive(x_203);
if (x_211 == 0)
{
x_205 = x_203;
x_206 = x_211;
goto block_210;
}
else
{
lean_inc(x_204);
lean_dec(x_203);
x_205 = lean_box(0);
x_206 = x_211;
goto block_210;
}
block_210:
{
lean_object* x_207; 
if (x_206 == 0)
{
x_207 = x_205;
goto block_208;
}
else
{
lean_object* x_209; 
x_209 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_209, 0, x_204);
x_207 = x_209;
goto block_208;
}
block_208:
{
return x_207;
}
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = l_Lean_Expr_appFn_x21(x_7);
x_213 = l_Lean_Expr_appArg_x21(x_212);
lean_dec_ref(x_212);
x_214 = l_Lean_Expr_appArg_x21(x_7);
x_177 = x_5;
x_178 = x_213;
x_179 = x_214;
goto block_191;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_215 = l_Lean_Expr_appFn_x21(x_7);
x_216 = l_Lean_Expr_appFn_x21(x_215);
lean_dec_ref(x_215);
x_217 = l_Lean_Expr_appArg_x21(x_216);
lean_dec_ref(x_216);
x_218 = l_Lean_Expr_appArg_x21(x_7);
x_177 = x_1;
x_178 = x_217;
x_179 = x_218;
goto block_191;
}
block_19:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_1);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
block_31:
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_14 = x_20;
x_15 = x_22;
goto block_19;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_dec_ref(x_20);
x_23 = lean_ctor_get(x_21, 0);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
x_24 = x_21;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
block_52:
{
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec_ref(x_37);
x_41 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__1, &l_Lean_Meta_rwMatcher___lam__1___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__1);
x_42 = l_Lean_MessageData_ofExpr(x_34);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__3, &l_Lean_Meta_rwMatcher___lam__1___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__3);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Exception_toMessageData(x_39);
x_47 = l_Lean_indentD(x_46);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__5, &l_Lean_Meta_rwMatcher___lam__1___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__5);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(x_50, x_38, x_33, x_32, x_35);
lean_dec(x_35);
lean_dec_ref(x_32);
lean_dec(x_33);
lean_dec_ref(x_38);
x_20 = x_36;
x_21 = x_51;
goto block_31;
}
else
{
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
x_20 = x_36;
x_21 = x_37;
goto block_31;
}
}
block_69:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(x_54, x_57);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
x_62 = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(x_53, x_57);
if (x_55 == 0)
{
lean_object* x_63; 
lean_dec(x_59);
lean_dec_ref(x_58);
lean_dec(x_57);
lean_dec_ref(x_56);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_14 = x_61;
x_15 = x_63;
goto block_19;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec_ref(x_62);
lean_inc(x_59);
lean_inc_ref(x_58);
lean_inc(x_57);
lean_inc_ref(x_56);
lean_inc(x_64);
x_65 = l_Lean_Meta_mkEqOfHEq(x_64, x_1, x_56, x_57, x_58, x_59);
if (lean_obj_tag(x_65) == 0)
{
lean_dec(x_64);
lean_dec(x_59);
lean_dec_ref(x_58);
lean_dec(x_57);
lean_dec_ref(x_56);
x_20 = x_61;
x_21 = x_65;
goto block_31;
}
else
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = l_Lean_Exception_isInterrupt(x_66);
if (x_67 == 0)
{
uint8_t x_68; 
lean_inc(x_66);
x_68 = l_Lean_Exception_isRuntime(x_66);
x_32 = x_58;
x_33 = x_57;
x_34 = x_64;
x_35 = x_59;
x_36 = x_61;
x_37 = x_65;
x_38 = x_56;
x_39 = x_66;
x_40 = x_68;
goto block_52;
}
else
{
x_32 = x_58;
x_33 = x_57;
x_34 = x_64;
x_35 = x_59;
x_36 = x_61;
x_37 = x_65;
x_38 = x_56;
x_39 = x_66;
x_40 = x_67;
goto block_52;
}
}
}
}
block_99:
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_array_get_size(x_76);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_nat_dec_eq(x_77, x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_98; 
lean_dec_ref(x_71);
lean_dec_ref(x_53);
x_80 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__7, &l_Lean_Meta_rwMatcher___lam__1___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__7);
x_81 = l_Lean_MessageData_ofConstName(x_4, x_5);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__9, &l_Lean_Meta_rwMatcher___lam__1___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__9);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_array_to_list(x_76);
x_86 = lean_box(0);
x_87 = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__7(x_85, x_86);
x_88 = l_Lean_MessageData_ofList(x_87);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_84);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(x_89, x_74, x_73, x_75, x_70);
lean_dec(x_70);
lean_dec_ref(x_75);
lean_dec(x_73);
lean_dec_ref(x_74);
x_91 = lean_ctor_get(x_90, 0);
x_98 = !lean_is_exclusive(x_90);
if (x_98 == 0)
{
x_92 = x_90;
x_93 = x_98;
goto block_97;
}
else
{
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_box(0);
x_93 = x_98;
goto block_97;
}
block_97:
{
lean_object* x_94; 
if (x_93 == 0)
{
x_94 = x_92;
goto block_95;
}
else
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_91);
x_94 = x_96;
goto block_95;
}
block_95:
{
return x_94;
}
}
}
else
{
lean_dec_ref(x_76);
lean_dec(x_4);
x_54 = x_71;
x_55 = x_72;
x_56 = x_74;
x_57 = x_73;
x_58 = x_75;
x_59 = x_70;
goto block_69;
}
}
block_116:
{
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec_ref(x_106);
x_70 = x_100;
x_71 = x_101;
x_72 = x_104;
x_73 = x_103;
x_74 = x_102;
x_75 = x_105;
x_76 = x_107;
goto block_99;
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; uint8_t x_115; 
lean_dec_ref(x_105);
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec_ref(x_53);
lean_dec(x_4);
x_108 = lean_ctor_get(x_106, 0);
x_115 = !lean_is_exclusive(x_106);
if (x_115 == 0)
{
x_109 = x_106;
x_110 = x_115;
goto block_114;
}
else
{
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_box(0);
x_110 = x_115;
goto block_114;
}
block_114:
{
lean_object* x_111; 
if (x_110 == 0)
{
x_111 = x_109;
goto block_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_108);
x_111 = x_113;
goto block_112;
}
block_112:
{
return x_111;
}
}
}
}
block_146:
{
lean_object* x_126; size_t x_127; lean_object* x_128; 
x_126 = lean_box(0);
x_127 = lean_array_size(x_119);
lean_inc(x_125);
lean_inc_ref(x_124);
lean_inc(x_123);
lean_inc_ref(x_122);
x_128 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8(x_119, x_127, x_118, x_126, x_122, x_123, x_124, x_125);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
lean_dec_ref(x_128);
x_129 = lean_unsigned_to_nat(0u);
x_130 = lean_array_get_size(x_119);
x_131 = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__10));
x_132 = lean_nat_dec_lt(x_129, x_130);
if (x_132 == 0)
{
lean_dec_ref(x_119);
x_70 = x_125;
x_71 = x_120;
x_72 = x_121;
x_73 = x_123;
x_74 = x_122;
x_75 = x_124;
x_76 = x_131;
goto block_99;
}
else
{
uint8_t x_133; 
x_133 = lean_nat_dec_le(x_130, x_130);
if (x_133 == 0)
{
if (x_132 == 0)
{
lean_dec_ref(x_119);
x_70 = x_125;
x_71 = x_120;
x_72 = x_121;
x_73 = x_123;
x_74 = x_122;
x_75 = x_124;
x_76 = x_131;
goto block_99;
}
else
{
size_t x_134; lean_object* x_135; 
x_134 = lean_usize_of_nat(x_130);
x_135 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(x_5, x_119, x_118, x_134, x_131, x_122, x_123, x_124, x_125);
lean_dec_ref(x_119);
x_100 = x_125;
x_101 = x_120;
x_102 = x_122;
x_103 = x_123;
x_104 = x_121;
x_105 = x_124;
x_106 = x_135;
goto block_116;
}
}
else
{
size_t x_136; lean_object* x_137; 
x_136 = lean_usize_of_nat(x_130);
x_137 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(x_5, x_119, x_118, x_136, x_131, x_122, x_123, x_124, x_125);
lean_dec_ref(x_119);
x_100 = x_125;
x_101 = x_120;
x_102 = x_122;
x_103 = x_123;
x_104 = x_121;
x_105 = x_124;
x_106 = x_137;
goto block_116;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_145; 
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec(x_123);
lean_dec_ref(x_122);
lean_dec_ref(x_120);
lean_dec_ref(x_119);
lean_dec_ref(x_53);
lean_dec(x_4);
x_138 = lean_ctor_get(x_128, 0);
x_145 = !lean_is_exclusive(x_128);
if (x_145 == 0)
{
x_139 = x_128;
x_140 = x_145;
goto block_144;
}
else
{
lean_inc(x_138);
lean_dec(x_128);
x_139 = lean_box(0);
x_140 = x_145;
goto block_144;
}
block_144:
{
lean_object* x_141; 
if (x_140 == 0)
{
x_141 = x_139;
goto block_142;
}
else
{
lean_object* x_143; 
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_138);
x_141 = x_143;
goto block_142;
}
block_142:
{
return x_141;
}
}
}
}
block_176:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; uint8_t x_175; 
lean_dec_ref(x_148);
x_154 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__12, &l_Lean_Meta_rwMatcher___lam__1___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__12);
x_155 = l_Lean_MessageData_ofExpr(x_150);
x_156 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__14, &l_Lean_Meta_rwMatcher___lam__1___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__14);
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = l_Lean_MessageData_ofConstName(x_4, x_5);
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__16, &l_Lean_Meta_rwMatcher___lam__1___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__16);
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = l_Lean_MessageData_ofExpr(x_6);
x_164 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
x_166 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(x_166, x_149, x_147, x_153, x_152);
lean_dec(x_152);
lean_dec_ref(x_153);
lean_dec(x_147);
lean_dec_ref(x_149);
x_168 = lean_ctor_get(x_167, 0);
x_175 = !lean_is_exclusive(x_167);
if (x_175 == 0)
{
x_169 = x_167;
x_170 = x_175;
goto block_174;
}
else
{
lean_inc(x_168);
lean_dec(x_167);
x_169 = lean_box(0);
x_170 = x_175;
goto block_174;
}
block_174:
{
lean_object* x_171; 
if (x_170 == 0)
{
x_171 = x_169;
goto block_172;
}
else
{
lean_object* x_173; 
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_168);
x_171 = x_173;
goto block_172;
}
block_172:
{
return x_171;
}
}
}
block_191:
{
lean_object* x_180; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_178);
lean_inc_ref(x_6);
x_180 = l_Lean_Meta_isExprDefEq(x_6, x_178, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; uint8_t x_182; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
lean_dec_ref(x_180);
x_182 = lean_unbox(x_181);
lean_dec(x_181);
if (x_182 == 0)
{
lean_dec_ref(x_119);
lean_dec_ref(x_53);
x_147 = x_10;
x_148 = x_179;
x_149 = x_9;
x_150 = x_178;
x_151 = x_177;
x_152 = x_12;
x_153 = x_11;
goto block_176;
}
else
{
if (x_5 == 0)
{
lean_dec_ref(x_178);
lean_dec_ref(x_6);
x_120 = x_179;
x_121 = x_177;
x_122 = x_9;
x_123 = x_10;
x_124 = x_11;
x_125 = x_12;
goto block_146;
}
else
{
lean_dec_ref(x_119);
lean_dec_ref(x_53);
x_147 = x_10;
x_148 = x_179;
x_149 = x_9;
x_150 = x_178;
x_151 = x_177;
x_152 = x_12;
x_153 = x_11;
goto block_176;
}
}
}
else
{
lean_object* x_183; lean_object* x_184; uint8_t x_185; uint8_t x_190; 
lean_dec_ref(x_179);
lean_dec_ref(x_178);
lean_dec_ref(x_119);
lean_dec_ref(x_53);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec(x_4);
x_183 = lean_ctor_get(x_180, 0);
x_190 = !lean_is_exclusive(x_180);
if (x_190 == 0)
{
x_184 = x_180;
x_185 = x_190;
goto block_189;
}
else
{
lean_inc(x_183);
lean_dec(x_180);
x_184 = lean_box(0);
x_185 = x_190;
goto block_189;
}
block_189:
{
lean_object* x_186; 
if (x_185 == 0)
{
x_186 = x_184;
goto block_187;
}
else
{
lean_object* x_188; 
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_183);
x_186 = x_188;
goto block_187;
}
block_187:
{
return x_186;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_1);
x_15 = lean_unbox(x_5);
x_16 = l_Lean_Meta_rwMatcher___lam__3(x_14, x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_7);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__14(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_16; 
x_16 = lean_usize_dec_eq(x_3, x_4);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_21; 
x_17 = lean_array_uget_borrowed(x_2, x_3);
x_21 = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(x_17, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
x_18 = x_1;
goto block_20;
}
else
{
x_11 = x_5;
goto block_15;
}
}
else
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec_ref(x_21);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
x_18 = x_25;
goto block_20;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec_ref(x_5);
x_26 = lean_ctor_get(x_21, 0);
x_33 = !lean_is_exclusive(x_21);
if (x_33 == 0)
{
x_27 = x_21;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
block_20:
{
if (x_18 == 0)
{
x_11 = x_5;
goto block_15;
}
else
{
lean_object* x_19; 
lean_inc(x_17);
x_19 = lean_array_push(x_5, x_17);
x_11 = x_19;
goto block_15;
}
}
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_5);
return x_34;
}
block_15:
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_5 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__14(x_11, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_21; lean_object* x_22; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; size_t x_118; size_t x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_54 = l_Lean_mkAppN(x_2, x_3);
x_118 = lean_array_size(x_3);
x_119 = 0;
x_120 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4(x_118, x_119, x_3);
x_185 = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__18));
x_186 = lean_unsigned_to_nat(4u);
x_187 = l_Lean_Expr_isAppOfArity(x_8, x_185, x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_188 = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__20));
x_189 = lean_unsigned_to_nat(3u);
x_190 = l_Lean_Expr_isAppOfArity(x_8, x_188, x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; uint8_t x_204; 
lean_dec_ref(x_120);
lean_dec_ref(x_54);
lean_dec_ref(x_6);
x_191 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__22, &l_Lean_Meta_rwMatcher___lam__1___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__22);
x_192 = l_Lean_MessageData_ofConstName(x_4, x_190);
x_193 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__24, &l_Lean_Meta_rwMatcher___lam__1___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__24);
x_195 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
x_196 = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(x_195, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_197 = lean_ctor_get(x_196, 0);
x_204 = !lean_is_exclusive(x_196);
if (x_204 == 0)
{
x_198 = x_196;
x_199 = x_204;
goto block_203;
}
else
{
lean_inc(x_197);
lean_dec(x_196);
x_198 = lean_box(0);
x_199 = x_204;
goto block_203;
}
block_203:
{
lean_object* x_200; 
if (x_199 == 0)
{
x_200 = x_198;
goto block_201;
}
else
{
lean_object* x_202; 
x_202 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_202, 0, x_197);
x_200 = x_202;
goto block_201;
}
block_201:
{
return x_200;
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = l_Lean_Expr_appFn_x21(x_8);
x_206 = l_Lean_Expr_appArg_x21(x_205);
lean_dec_ref(x_205);
x_207 = l_Lean_Expr_appArg_x21(x_8);
x_148 = x_187;
x_149 = x_206;
x_150 = x_207;
goto block_184;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_208 = l_Lean_Expr_appFn_x21(x_8);
x_209 = l_Lean_Expr_appFn_x21(x_208);
lean_dec_ref(x_208);
x_210 = l_Lean_Expr_appArg_x21(x_209);
lean_dec_ref(x_209);
x_211 = l_Lean_Expr_appArg_x21(x_8);
x_148 = x_1;
x_149 = x_210;
x_150 = x_211;
goto block_184;
}
block_20:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_1);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
block_32:
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_15 = x_21;
x_16 = x_23;
goto block_20;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
lean_dec_ref(x_21);
x_24 = lean_ctor_get(x_22, 0);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
x_25 = x_22;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
block_53:
{
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec_ref(x_35);
x_42 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__1, &l_Lean_Meta_rwMatcher___lam__1___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__1);
x_43 = l_Lean_MessageData_ofExpr(x_34);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__3, &l_Lean_Meta_rwMatcher___lam__1___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__3);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Exception_toMessageData(x_33);
x_48 = l_Lean_indentD(x_47);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__5, &l_Lean_Meta_rwMatcher___lam__1___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__5);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(x_51, x_39, x_40, x_38, x_36);
lean_dec(x_36);
lean_dec_ref(x_38);
lean_dec(x_40);
lean_dec_ref(x_39);
x_21 = x_37;
x_22 = x_52;
goto block_32;
}
else
{
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec_ref(x_33);
x_21 = x_37;
x_22 = x_35;
goto block_32;
}
}
block_70:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(x_56, x_58);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
x_63 = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(x_54, x_58);
if (x_55 == 0)
{
lean_object* x_64; 
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_15 = x_62;
x_16 = x_64;
goto block_20;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec_ref(x_63);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_65);
x_66 = l_Lean_Meta_mkEqOfHEq(x_65, x_1, x_57, x_58, x_59, x_60);
if (lean_obj_tag(x_66) == 0)
{
lean_dec(x_65);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
x_21 = x_62;
x_22 = x_66;
goto block_32;
}
else
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = l_Lean_Exception_isInterrupt(x_67);
if (x_68 == 0)
{
uint8_t x_69; 
lean_inc(x_67);
x_69 = l_Lean_Exception_isRuntime(x_67);
x_33 = x_67;
x_34 = x_65;
x_35 = x_66;
x_36 = x_60;
x_37 = x_62;
x_38 = x_59;
x_39 = x_57;
x_40 = x_58;
x_41 = x_69;
goto block_53;
}
else
{
x_33 = x_67;
x_34 = x_65;
x_35 = x_66;
x_36 = x_60;
x_37 = x_62;
x_38 = x_59;
x_39 = x_57;
x_40 = x_58;
x_41 = x_68;
goto block_53;
}
}
}
}
block_100:
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_array_get_size(x_77);
x_79 = lean_unsigned_to_nat(0u);
x_80 = lean_nat_dec_eq(x_78, x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_99; 
lean_dec_ref(x_72);
lean_dec_ref(x_54);
x_81 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__7, &l_Lean_Meta_rwMatcher___lam__1___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__7);
x_82 = l_Lean_MessageData_ofConstName(x_4, x_80);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__9, &l_Lean_Meta_rwMatcher___lam__1___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__9);
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_array_to_list(x_77);
x_87 = lean_box(0);
x_88 = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__7(x_86, x_87);
x_89 = l_Lean_MessageData_ofList(x_88);
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_85);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(x_90, x_74, x_76, x_71, x_75);
lean_dec(x_75);
lean_dec_ref(x_71);
lean_dec(x_76);
lean_dec_ref(x_74);
x_92 = lean_ctor_get(x_91, 0);
x_99 = !lean_is_exclusive(x_91);
if (x_99 == 0)
{
x_93 = x_91;
x_94 = x_99;
goto block_98;
}
else
{
lean_inc(x_92);
lean_dec(x_91);
x_93 = lean_box(0);
x_94 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_95; 
if (x_94 == 0)
{
x_95 = x_93;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_92);
x_95 = x_97;
goto block_96;
}
block_96:
{
return x_95;
}
}
}
else
{
lean_dec_ref(x_77);
lean_dec(x_4);
x_55 = x_73;
x_56 = x_72;
x_57 = x_74;
x_58 = x_76;
x_59 = x_71;
x_60 = x_75;
goto block_70;
}
}
block_117:
{
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_71 = x_101;
x_72 = x_104;
x_73 = x_103;
x_74 = x_102;
x_75 = x_105;
x_76 = x_106;
x_77 = x_108;
goto block_100;
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_116; 
lean_dec(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec_ref(x_102);
lean_dec_ref(x_101);
lean_dec_ref(x_54);
lean_dec(x_4);
x_109 = lean_ctor_get(x_107, 0);
x_116 = !lean_is_exclusive(x_107);
if (x_116 == 0)
{
x_110 = x_107;
x_111 = x_116;
goto block_115;
}
else
{
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_box(0);
x_111 = x_116;
goto block_115;
}
block_115:
{
lean_object* x_112; 
if (x_111 == 0)
{
x_112 = x_110;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_109);
x_112 = x_114;
goto block_113;
}
block_113:
{
return x_112;
}
}
}
}
block_147:
{
lean_object* x_127; size_t x_128; lean_object* x_129; 
x_127 = lean_box(0);
x_128 = lean_array_size(x_120);
lean_inc(x_126);
lean_inc_ref(x_125);
lean_inc(x_124);
lean_inc_ref(x_123);
x_129 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8(x_120, x_128, x_119, x_127, x_123, x_124, x_125, x_126);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
lean_dec_ref(x_129);
x_130 = lean_unsigned_to_nat(0u);
x_131 = lean_array_get_size(x_120);
x_132 = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__10));
x_133 = lean_nat_dec_lt(x_130, x_131);
if (x_133 == 0)
{
lean_dec_ref(x_120);
x_71 = x_125;
x_72 = x_122;
x_73 = x_121;
x_74 = x_123;
x_75 = x_126;
x_76 = x_124;
x_77 = x_132;
goto block_100;
}
else
{
uint8_t x_134; 
x_134 = lean_nat_dec_le(x_131, x_131);
if (x_134 == 0)
{
if (x_133 == 0)
{
lean_dec_ref(x_120);
x_71 = x_125;
x_72 = x_122;
x_73 = x_121;
x_74 = x_123;
x_75 = x_126;
x_76 = x_124;
x_77 = x_132;
goto block_100;
}
else
{
size_t x_135; lean_object* x_136; 
x_135 = lean_usize_of_nat(x_131);
x_136 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__14(x_5, x_120, x_119, x_135, x_132, x_123, x_124, x_125, x_126);
lean_dec_ref(x_120);
x_101 = x_125;
x_102 = x_123;
x_103 = x_121;
x_104 = x_122;
x_105 = x_126;
x_106 = x_124;
x_107 = x_136;
goto block_117;
}
}
else
{
size_t x_137; lean_object* x_138; 
x_137 = lean_usize_of_nat(x_131);
x_138 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__14(x_5, x_120, x_119, x_137, x_132, x_123, x_124, x_125, x_126);
lean_dec_ref(x_120);
x_101 = x_125;
x_102 = x_123;
x_103 = x_121;
x_104 = x_122;
x_105 = x_126;
x_106 = x_124;
x_107 = x_138;
goto block_117;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; uint8_t x_146; 
lean_dec(x_126);
lean_dec_ref(x_125);
lean_dec(x_124);
lean_dec_ref(x_123);
lean_dec_ref(x_122);
lean_dec_ref(x_120);
lean_dec_ref(x_54);
lean_dec(x_4);
x_139 = lean_ctor_get(x_129, 0);
x_146 = !lean_is_exclusive(x_129);
if (x_146 == 0)
{
x_140 = x_129;
x_141 = x_146;
goto block_145;
}
else
{
lean_inc(x_139);
lean_dec(x_129);
x_140 = lean_box(0);
x_141 = x_146;
goto block_145;
}
block_145:
{
lean_object* x_142; 
if (x_141 == 0)
{
x_142 = x_140;
goto block_143;
}
else
{
lean_object* x_144; 
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_139);
x_142 = x_144;
goto block_143;
}
block_143:
{
return x_142;
}
}
}
}
block_184:
{
lean_object* x_151; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_149);
lean_inc_ref(x_6);
x_151 = l_Lean_Meta_isExprDefEq(x_6, x_149, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; uint8_t x_153; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
lean_dec_ref(x_151);
x_153 = lean_unbox(x_152);
lean_dec(x_152);
if (x_153 == 0)
{
if (x_5 == 0)
{
lean_dec_ref(x_149);
lean_dec_ref(x_6);
x_121 = x_148;
x_122 = x_150;
x_123 = x_10;
x_124 = x_11;
x_125 = x_12;
x_126 = x_13;
goto block_147;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; uint8_t x_175; 
lean_dec_ref(x_150);
lean_dec_ref(x_120);
lean_dec_ref(x_54);
x_154 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__12, &l_Lean_Meta_rwMatcher___lam__1___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__12);
x_155 = l_Lean_MessageData_ofExpr(x_149);
x_156 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__14, &l_Lean_Meta_rwMatcher___lam__1___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__14);
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = l_Lean_MessageData_ofConstName(x_4, x_7);
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__16, &l_Lean_Meta_rwMatcher___lam__1___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__16);
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = l_Lean_MessageData_ofExpr(x_6);
x_164 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
x_166 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(x_166, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_168 = lean_ctor_get(x_167, 0);
x_175 = !lean_is_exclusive(x_167);
if (x_175 == 0)
{
x_169 = x_167;
x_170 = x_175;
goto block_174;
}
else
{
lean_inc(x_168);
lean_dec(x_167);
x_169 = lean_box(0);
x_170 = x_175;
goto block_174;
}
block_174:
{
lean_object* x_171; 
if (x_170 == 0)
{
x_171 = x_169;
goto block_172;
}
else
{
lean_object* x_173; 
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_168);
x_171 = x_173;
goto block_172;
}
block_172:
{
return x_171;
}
}
}
}
else
{
lean_dec_ref(x_149);
lean_dec_ref(x_6);
x_121 = x_148;
x_122 = x_150;
x_123 = x_10;
x_124 = x_11;
x_125 = x_12;
x_126 = x_13;
goto block_147;
}
}
else
{
lean_object* x_176; lean_object* x_177; uint8_t x_178; uint8_t x_183; 
lean_dec_ref(x_150);
lean_dec_ref(x_149);
lean_dec_ref(x_120);
lean_dec_ref(x_54);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_6);
lean_dec(x_4);
x_176 = lean_ctor_get(x_151, 0);
x_183 = !lean_is_exclusive(x_151);
if (x_183 == 0)
{
x_177 = x_151;
x_178 = x_183;
goto block_182;
}
else
{
lean_inc(x_176);
lean_dec(x_151);
x_177 = lean_box(0);
x_178 = x_183;
goto block_182;
}
block_182:
{
lean_object* x_179; 
if (x_178 == 0)
{
x_179 = x_177;
goto block_180;
}
else
{
lean_object* x_181; 
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_176);
x_179 = x_181;
goto block_180;
}
block_180:
{
return x_179;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_1);
x_16 = lean_unbox(x_5);
x_17 = lean_unbox(x_7);
x_18 = l_Lean_Meta_rwMatcher___lam__4(x_15, x_2, x_3, x_4, x_16, x_6, x_17, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_8);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_rwMatcher_spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_7 = l_Lean_Meta_reduceRecMatcher_x3f(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_21; 
x_8 = lean_ctor_get(x_7, 0);
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
x_9 = x_7;
x_10 = x_21;
goto block_20;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_21;
goto block_20;
}
block_20:
{
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_11; lean_object* x_12; 
lean_del_object(x_9);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = l_Lean_Expr_headBeta(x_11);
x_1 = x_12;
goto _start;
}
else
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_8);
lean_inc_ref(x_1);
x_14 = l_Lean_Expr_headBeta(x_1);
x_15 = lean_expr_eqv(x_1, x_14);
if (x_15 == 0)
{
lean_del_object(x_9);
lean_dec_ref(x_1);
x_1 = x_14;
goto _start;
}
else
{
lean_object* x_17; 
lean_dec_ref(x_14);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_1);
x_17 = x_9;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_1);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_29; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_22 = lean_ctor_get(x_7, 0);
x_29 = !lean_is_exclusive(x_7);
if (x_29 == 0)
{
x_23 = x_7;
x_24 = x_29;
goto block_28;
}
else
{
lean_inc(x_22);
lean_dec(x_7);
x_23 = lean_box(0);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_rwMatcher_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_rwMatcher_spec__15(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
x_3 = lean_ctor_get(x_1, 0);
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
x_4 = x_1;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
lean_ctor_set_tag(x_4, 1);
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_18; 
x_11 = lean_ctor_get(x_1, 0);
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
x_12 = x_1;
x_13 = x_18;
goto block_17;
}
else
{
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_14; 
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 0);
x_14 = x_12;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14_spec__16(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget_borrowed(x_3, x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14_spec__16(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_80; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_7, 2);
x_13 = lean_ctor_get(x_7, 3);
x_14 = lean_ctor_get(x_7, 4);
x_15 = lean_ctor_get(x_7, 5);
x_16 = lean_ctor_get(x_7, 6);
x_17 = lean_ctor_get(x_7, 7);
x_18 = lean_ctor_get(x_7, 8);
x_19 = lean_ctor_get(x_7, 9);
x_20 = lean_ctor_get(x_7, 10);
x_21 = lean_ctor_get(x_7, 11);
x_22 = lean_ctor_get_uint8(x_7, sizeof(void*)*14);
x_23 = lean_ctor_get(x_7, 12);
x_24 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_25 = lean_ctor_get(x_7, 13);
x_80 = !lean_is_exclusive(x_7);
if (x_80 == 0)
{
x_26 = x_7;
x_27 = x_80;
goto block_79;
}
else
{
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_7);
x_26 = lean_box(0);
x_27 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_st_ref_get(x_8);
x_29 = lean_ctor_get(x_28, 4);
lean_inc_ref(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc_ref(x_30);
lean_dec_ref(x_29);
x_31 = l_Lean_replaceRef(x_3, x_15);
lean_dec(x_15);
if (x_27 == 0)
{
lean_ctor_set(x_26, 5, x_31);
x_32 = x_26;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_78, 0, x_10);
lean_ctor_set(x_78, 1, x_11);
lean_ctor_set(x_78, 2, x_12);
lean_ctor_set(x_78, 3, x_13);
lean_ctor_set(x_78, 4, x_14);
lean_ctor_set(x_78, 5, x_31);
lean_ctor_set(x_78, 6, x_16);
lean_ctor_set(x_78, 7, x_17);
lean_ctor_set(x_78, 8, x_18);
lean_ctor_set(x_78, 9, x_19);
lean_ctor_set(x_78, 10, x_20);
lean_ctor_set(x_78, 11, x_21);
lean_ctor_set(x_78, 12, x_23);
lean_ctor_set(x_78, 13, x_25);
lean_ctor_set_uint8(x_78, sizeof(void*)*14, x_22);
lean_ctor_set_uint8(x_78, sizeof(void*)*14 + 1, x_24);
x_32 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_76; 
x_33 = l_Lean_PersistentArray_toArray___redArg(x_30);
lean_dec_ref(x_30);
x_34 = lean_array_size(x_33);
x_35 = 0;
x_36 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14_spec__16(x_34, x_35, x_33);
x_37 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_4);
lean_ctor_set(x_37, 2, x_36);
x_38 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3_spec__4(x_37, x_5, x_6, x_32, x_8);
lean_dec_ref(x_32);
x_39 = lean_ctor_get(x_38, 0);
x_76 = !lean_is_exclusive(x_38);
if (x_76 == 0)
{
x_40 = x_38;
x_41 = x_76;
goto block_75;
}
else
{
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_74; 
x_42 = lean_st_ref_take(x_8);
x_43 = lean_ctor_get(x_42, 4);
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
x_46 = lean_ctor_get(x_42, 2);
x_47 = lean_ctor_get(x_42, 3);
x_48 = lean_ctor_get(x_42, 5);
x_49 = lean_ctor_get(x_42, 6);
x_50 = lean_ctor_get(x_42, 7);
x_51 = lean_ctor_get(x_42, 8);
x_74 = !lean_is_exclusive(x_42);
if (x_74 == 0)
{
x_52 = x_42;
x_53 = x_74;
goto block_73;
}
else
{
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_43);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_42);
x_52 = lean_box(0);
x_53 = x_74;
goto block_73;
}
block_73:
{
uint64_t x_54; lean_object* x_55; uint8_t x_56; uint8_t x_71; 
x_54 = lean_ctor_get_uint64(x_43, sizeof(void*)*1);
x_71 = !lean_is_exclusive(x_43);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_43, 0);
lean_dec(x_72);
x_55 = x_43;
x_56 = x_71;
goto block_70;
}
else
{
lean_dec(x_43);
x_55 = lean_box(0);
x_56 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_3);
lean_ctor_set(x_57, 1, x_39);
x_58 = l_Lean_PersistentArray_push___redArg(x_1, x_57);
if (x_56 == 0)
{
lean_ctor_set(x_55, 0, x_58);
x_59 = x_55;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_69, 0, x_58);
lean_ctor_set_uint64(x_69, sizeof(void*)*1, x_54);
x_59 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_60; 
if (x_53 == 0)
{
lean_ctor_set(x_52, 4, x_59);
x_60 = x_52;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_67, 0, x_44);
lean_ctor_set(x_67, 1, x_45);
lean_ctor_set(x_67, 2, x_46);
lean_ctor_set(x_67, 3, x_47);
lean_ctor_set(x_67, 4, x_59);
lean_ctor_set(x_67, 5, x_48);
lean_ctor_set(x_67, 6, x_49);
lean_ctor_set(x_67, 7, x_50);
lean_ctor_set(x_67, 8, x_51);
x_60 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_st_ref_set(x_8, x_60);
x_62 = lean_box(0);
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_62);
x_63 = x_40;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_62);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_7) == 3)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
return x_8;
}
else
{
lean_dec(x_7);
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___redArg___closed__2(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1000u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; uint8_t x_51; double x_82; 
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec_ref(x_8);
x_34 = lean_ctor_get(x_15, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_dec(x_15);
x_36 = l_Lean_trace_profiler;
x_37 = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11(x_4, x_36);
if (x_37 == 0)
{
x_51 = x_37;
goto block_81;
}
else
{
lean_object* x_88; uint8_t x_89; 
x_88 = l_Lean_trace_profiler_useHeartbeats;
x_89 = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11(x_4, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; double x_92; double x_93; double x_94; 
x_90 = l_Lean_trace_profiler_threshold;
x_91 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16(x_4, x_90);
x_92 = lean_float_of_nat(x_91);
x_93 = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___redArg___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___redArg___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___redArg___closed__2);
x_94 = lean_float_div(x_92, x_93);
x_82 = x_94;
goto block_87;
}
else
{
lean_object* x_95; lean_object* x_96; double x_97; 
x_95 = l_Lean_trace_profiler_threshold;
x_96 = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16(x_4, x_95);
x_97 = lean_float_of_nat(x_96);
x_82 = x_97;
goto block_87;
}
}
block_33:
{
lean_object* x_23; 
x_23 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14(x_6, x_18, x_16, x_17, x_19, x_20, x_21, x_22);
lean_dec(x_22);
lean_dec(x_20);
lean_dec_ref(x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_dec_ref(x_23);
x_24 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___redArg(x_14);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
lean_dec(x_14);
x_25 = lean_ctor_get(x_23, 0);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
x_26 = x_23;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
block_45:
{
double x_40; lean_object* x_41; 
x_40 = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0);
lean_inc_ref(x_3);
lean_inc(x_1);
x_41 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_3);
lean_ctor_set_float(x_41, sizeof(void*)*2, x_40);
lean_ctor_set_float(x_41, sizeof(void*)*2 + 8, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 16, x_2);
if (x_37 == 0)
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec_ref(x_3);
lean_dec(x_1);
x_16 = x_38;
x_17 = x_39;
x_18 = x_41;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
goto block_33;
}
else
{
lean_object* x_42; double x_43; double x_44; 
lean_dec_ref(x_41);
x_42 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_3);
x_43 = lean_unbox_float(x_34);
lean_dec(x_34);
lean_ctor_set_float(x_42, sizeof(void*)*2, x_43);
x_44 = lean_unbox_float(x_35);
lean_dec(x_35);
lean_ctor_set_float(x_42, sizeof(void*)*2 + 8, x_44);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 16, x_2);
x_16 = x_38;
x_17 = x_39;
x_18 = x_42;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
x_22 = x_12;
goto block_33;
}
}
block_50:
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_11, 5);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_14);
x_47 = lean_apply_6(x_7, x_14, x_9, x_10, x_11, x_12, lean_box(0));
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
lean_inc(x_46);
x_38 = x_46;
x_39 = x_48;
goto block_45;
}
else
{
lean_object* x_49; 
lean_dec_ref(x_47);
x_49 = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___redArg___closed__1);
lean_inc(x_46);
x_38 = x_46;
x_39 = x_49;
goto block_45;
}
}
block_81:
{
if (x_5 == 0)
{
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_80; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
x_52 = lean_st_ref_take(x_12);
x_53 = lean_ctor_get(x_52, 4);
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
x_56 = lean_ctor_get(x_52, 2);
x_57 = lean_ctor_get(x_52, 3);
x_58 = lean_ctor_get(x_52, 5);
x_59 = lean_ctor_get(x_52, 6);
x_60 = lean_ctor_get(x_52, 7);
x_61 = lean_ctor_get(x_52, 8);
x_80 = !lean_is_exclusive(x_52);
if (x_80 == 0)
{
x_62 = x_52;
x_63 = x_80;
goto block_79;
}
else
{
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_53);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_52);
x_62 = lean_box(0);
x_63 = x_80;
goto block_79;
}
block_79:
{
uint64_t x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_78; 
x_64 = lean_ctor_get_uint64(x_53, sizeof(void*)*1);
x_65 = lean_ctor_get(x_53, 0);
x_78 = !lean_is_exclusive(x_53);
if (x_78 == 0)
{
x_66 = x_53;
x_67 = x_78;
goto block_77;
}
else
{
lean_inc(x_65);
lean_dec(x_53);
x_66 = lean_box(0);
x_67 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_68; lean_object* x_69; 
x_68 = l_Lean_PersistentArray_append___redArg(x_6, x_65);
lean_dec_ref(x_65);
if (x_67 == 0)
{
lean_ctor_set(x_66, 0, x_68);
x_69 = x_66;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_76, 0, x_68);
lean_ctor_set_uint64(x_76, sizeof(void*)*1, x_64);
x_69 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_70; 
if (x_63 == 0)
{
lean_ctor_set(x_62, 4, x_69);
x_70 = x_62;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_74, 0, x_54);
lean_ctor_set(x_74, 1, x_55);
lean_ctor_set(x_74, 2, x_56);
lean_ctor_set(x_74, 3, x_57);
lean_ctor_set(x_74, 4, x_69);
lean_ctor_set(x_74, 5, x_58);
lean_ctor_set(x_74, 6, x_59);
lean_ctor_set(x_74, 7, x_60);
lean_ctor_set(x_74, 8, x_61);
x_70 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_st_ref_set(x_12, x_70);
lean_dec(x_12);
x_72 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___redArg(x_14);
return x_72;
}
}
}
}
}
else
{
goto block_50;
}
}
else
{
goto block_50;
}
}
block_87:
{
double x_83; double x_84; double x_85; uint8_t x_86; 
x_83 = lean_unbox_float(x_35);
x_84 = lean_unbox_float(x_34);
x_85 = lean_float_sub(x_83, x_84);
x_86 = lean_float_decLt(x_82, x_85);
x_51 = x_86;
goto block_81;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
x_15 = lean_unbox(x_5);
x_16 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___redArg(x_1, x_14, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_4);
return x_16;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static double _init_l_Lean_Meta_rwMatcher___closed__4(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1000000000u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__9));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__11));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__13));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__15));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_71; uint8_t x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_94; uint8_t x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_107; uint8_t x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_182; uint8_t x_187; uint8_t x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_270; lean_object* x_393; uint8_t x_394; 
x_393 = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__20));
x_394 = l_Lean_Expr_isAppOf(x_2, x_393);
if (x_394 == 0)
{
lean_object* x_395; uint8_t x_396; 
x_395 = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__22));
x_396 = l_Lean_Expr_isAppOf(x_2, x_395);
x_270 = x_396;
goto block_392;
}
else
{
x_270 = x_394;
goto block_392;
}
block_26:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
x_18 = lean_ctor_get(x_8, 0);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
x_19 = x_8;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
block_57:
{
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_inc(x_29);
x_32 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg(x_29, x_5);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_28);
x_35 = lean_box(0);
x_36 = lean_apply_6(x_27, x_35, x_3, x_4, x_5, x_6, lean_box(0));
x_8 = x_36;
goto block_26;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__1, &l_Lean_Meta_rwMatcher___closed__1_once, _init_l_Lean_Meta_rwMatcher___closed__1);
x_38 = l_Lean_MessageData_ofConstName(x_28, x_31);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__3, &l_Lean_Meta_rwMatcher___closed__3_once, _init_l_Lean_Meta_rwMatcher___closed__3);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Exception_toMessageData(x_30);
x_43 = l_Lean_indentD(x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(x_29, x_44, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_apply_6(x_27, x_46, x_3, x_4, x_5, x_6, lean_box(0));
x_8 = x_47;
goto block_26;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_55; 
lean_dec_ref(x_27);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_48 = lean_ctor_get(x_45, 0);
x_55 = !lean_is_exclusive(x_45);
if (x_55 == 0)
{
x_49 = x_45;
x_50 = x_55;
goto block_54;
}
else
{
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_box(0);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_50 == 0)
{
x_51 = x_49;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_48);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
else
{
lean_object* x_56; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_30);
return x_56;
}
}
block_64:
{
uint8_t x_62; 
x_62 = l_Lean_Exception_isInterrupt(x_61);
if (x_62 == 0)
{
uint8_t x_63; 
lean_inc_ref(x_61);
x_63 = l_Lean_Exception_isRuntime(x_61);
x_27 = x_58;
x_28 = x_60;
x_29 = x_59;
x_30 = x_61;
x_31 = x_63;
goto block_57;
}
else
{
x_27 = x_58;
x_28 = x_60;
x_29 = x_59;
x_30 = x_61;
x_31 = x_62;
goto block_57;
}
}
block_70:
{
if (lean_obj_tag(x_68) == 0)
{
lean_dec(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_68;
}
else
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_58 = x_65;
x_59 = x_67;
x_60 = x_66;
x_61 = x_69;
goto block_64;
}
}
block_93:
{
lean_object* x_82; double x_83; double x_84; double x_85; double x_86; double x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_82 = lean_io_mono_nanos_now();
x_83 = lean_float_of_nat(x_71);
x_84 = lean_float_once(&l_Lean_Meta_rwMatcher___closed__4, &l_Lean_Meta_rwMatcher___closed__4_once, _init_l_Lean_Meta_rwMatcher___closed__4);
x_85 = lean_float_div(x_83, x_84);
x_86 = lean_float_of_nat(x_82);
x_87 = lean_float_div(x_86, x_84);
x_88 = lean_box_float(x_85);
x_89 = lean_box_float(x_87);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_81);
lean_ctor_set(x_91, 1, x_90);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_77);
x_92 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___redArg(x_77, x_73, x_75, x_80, x_72, x_79, x_78, x_91, x_3, x_4, x_5, x_6);
lean_dec_ref(x_80);
x_65 = x_74;
x_66 = x_76;
x_67 = x_77;
x_68 = x_92;
goto block_70;
}
block_106:
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_71 = x_94;
x_72 = x_96;
x_73 = x_95;
x_74 = x_97;
x_75 = x_98;
x_76 = x_100;
x_77 = x_99;
x_78 = x_101;
x_79 = x_103;
x_80 = x_102;
x_81 = x_105;
goto block_93;
}
block_127:
{
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; uint8_t x_125; 
x_118 = lean_ctor_get(x_117, 0);
x_125 = !lean_is_exclusive(x_117);
if (x_125 == 0)
{
x_119 = x_117;
x_120 = x_125;
goto block_124;
}
else
{
lean_inc(x_118);
lean_dec(x_117);
x_119 = lean_box(0);
x_120 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_121; 
if (x_120 == 0)
{
lean_ctor_set_tag(x_119, 1);
x_121 = x_119;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_118);
x_121 = x_123;
goto block_122;
}
block_122:
{
x_71 = x_107;
x_72 = x_109;
x_73 = x_108;
x_74 = x_110;
x_75 = x_111;
x_76 = x_113;
x_77 = x_112;
x_78 = x_114;
x_79 = x_116;
x_80 = x_115;
x_81 = x_121;
goto block_93;
}
}
}
else
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_117, 0);
lean_inc(x_126);
lean_dec_ref(x_117);
x_94 = x_107;
x_95 = x_108;
x_96 = x_109;
x_97 = x_110;
x_98 = x_111;
x_99 = x_112;
x_100 = x_113;
x_101 = x_114;
x_102 = x_115;
x_103 = x_116;
x_104 = x_126;
goto block_106;
}
}
block_147:
{
lean_object* x_139; double x_140; double x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_139 = lean_io_get_num_heartbeats();
x_140 = lean_float_of_nat(x_134);
x_141 = lean_float_of_nat(x_139);
x_142 = lean_box_float(x_140);
x_143 = lean_box_float(x_141);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_138);
lean_ctor_set(x_145, 1, x_144);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_133);
x_146 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___redArg(x_133, x_129, x_131, x_137, x_128, x_136, x_135, x_145, x_3, x_4, x_5, x_6);
lean_dec_ref(x_137);
x_65 = x_130;
x_66 = x_132;
x_67 = x_133;
x_68 = x_146;
goto block_70;
}
block_160:
{
lean_object* x_159; 
x_159 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_159, 0, x_158);
x_128 = x_149;
x_129 = x_148;
x_130 = x_150;
x_131 = x_151;
x_132 = x_153;
x_133 = x_152;
x_134 = x_154;
x_135 = x_155;
x_136 = x_157;
x_137 = x_156;
x_138 = x_159;
goto block_147;
}
block_181:
{
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; uint8_t x_179; 
x_172 = lean_ctor_get(x_171, 0);
x_179 = !lean_is_exclusive(x_171);
if (x_179 == 0)
{
x_173 = x_171;
x_174 = x_179;
goto block_178;
}
else
{
lean_inc(x_172);
lean_dec(x_171);
x_173 = lean_box(0);
x_174 = x_179;
goto block_178;
}
block_178:
{
lean_object* x_175; 
if (x_174 == 0)
{
lean_ctor_set_tag(x_173, 1);
x_175 = x_173;
goto block_176;
}
else
{
lean_object* x_177; 
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_172);
x_175 = x_177;
goto block_176;
}
block_176:
{
x_128 = x_162;
x_129 = x_161;
x_130 = x_163;
x_131 = x_164;
x_132 = x_166;
x_133 = x_165;
x_134 = x_167;
x_135 = x_168;
x_136 = x_170;
x_137 = x_169;
x_138 = x_175;
goto block_147;
}
}
}
else
{
lean_object* x_180; 
x_180 = lean_ctor_get(x_171, 0);
lean_inc(x_180);
lean_dec_ref(x_171);
x_148 = x_161;
x_149 = x_162;
x_150 = x_163;
x_151 = x_164;
x_152 = x_165;
x_153 = x_166;
x_154 = x_167;
x_155 = x_168;
x_156 = x_169;
x_157 = x_170;
x_158 = x_180;
goto block_160;
}
}
block_186:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_box(0);
x_184 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_184, 0, x_2);
lean_ctor_set(x_184, 1, x_183);
lean_ctor_set_uint8(x_184, sizeof(void*)*2, x_182);
x_185 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_185, 0, x_184);
return x_185;
}
block_191:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_box(0);
x_189 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_189, 0, x_2);
lean_ctor_set(x_189, 1, x_188);
lean_ctor_set_uint8(x_189, sizeof(void*)*2, x_187);
x_190 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_190, 0, x_189);
return x_190;
}
block_269:
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_205 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg(x_6);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
lean_dec_ref(x_205);
x_207 = l_Lean_trace_profiler_useHeartbeats;
x_208 = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11(x_204, x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_io_mono_nanos_now();
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_210 = lean_infer_type(x_198, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; uint8_t x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
lean_dec_ref(x_210);
x_212 = 0;
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_213 = l_Lean_Meta_forallMetaTelescope(x_211, x_212, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; uint8_t x_235; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
lean_dec_ref(x_213);
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 0);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_ctor_get(x_215, 1);
x_235 = !lean_is_exclusive(x_215);
if (x_235 == 0)
{
lean_object* x_236; 
x_236 = lean_ctor_get(x_215, 0);
lean_dec(x_236);
x_218 = x_215;
x_219 = x_235;
goto block_234;
}
else
{
lean_inc(x_217);
lean_dec(x_215);
x_218 = lean_box(0);
x_219 = x_235;
goto block_234;
}
block_234:
{
lean_object* x_220; lean_object* x_221; uint8_t x_222; 
lean_inc(x_202);
x_220 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg(x_202, x_5);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
lean_dec_ref(x_220);
x_222 = lean_unbox(x_221);
lean_dec(x_221);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; 
lean_del_object(x_218);
x_223 = lean_box(0);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_224 = l_Lean_Meta_rwMatcher___lam__3(x_194, x_193, x_216, x_195, x_208, x_2, x_217, x_223, x_3, x_4, x_5, x_6);
lean_dec(x_217);
x_107 = x_209;
x_108 = x_199;
x_109 = x_192;
x_110 = x_200;
x_111 = x_201;
x_112 = x_202;
x_113 = x_203;
x_114 = x_197;
x_115 = x_204;
x_116 = x_206;
x_117 = x_224;
goto block_127;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__26, &l_Lean_Meta_rwMatcher___lam__1___closed__26_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__26);
lean_inc(x_217);
x_226 = l_Lean_indentExpr(x_217);
if (x_219 == 0)
{
lean_ctor_set_tag(x_218, 7);
lean_ctor_set(x_218, 1, x_226);
lean_ctor_set(x_218, 0, x_225);
x_227 = x_218;
goto block_232;
}
else
{
lean_object* x_233; 
x_233 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_233, 0, x_225);
lean_ctor_set(x_233, 1, x_226);
x_227 = x_233;
goto block_232;
}
block_232:
{
lean_object* x_228; 
lean_inc(x_202);
x_228 = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(x_202, x_227, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
lean_dec_ref(x_228);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_230 = l_Lean_Meta_rwMatcher___lam__3(x_194, x_193, x_216, x_195, x_208, x_2, x_217, x_229, x_3, x_4, x_5, x_6);
lean_dec(x_217);
x_107 = x_209;
x_108 = x_199;
x_109 = x_192;
x_110 = x_200;
x_111 = x_201;
x_112 = x_202;
x_113 = x_203;
x_114 = x_197;
x_115 = x_204;
x_116 = x_206;
x_117 = x_230;
goto block_127;
}
else
{
lean_object* x_231; 
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_195);
lean_dec_ref(x_193);
lean_dec_ref(x_2);
x_231 = lean_ctor_get(x_228, 0);
lean_inc(x_231);
lean_dec_ref(x_228);
x_94 = x_209;
x_95 = x_199;
x_96 = x_192;
x_97 = x_200;
x_98 = x_201;
x_99 = x_202;
x_100 = x_203;
x_101 = x_197;
x_102 = x_204;
x_103 = x_206;
x_104 = x_231;
goto block_106;
}
}
}
}
}
else
{
lean_object* x_237; 
lean_dec(x_195);
lean_dec_ref(x_193);
lean_dec_ref(x_2);
x_237 = lean_ctor_get(x_213, 0);
lean_inc(x_237);
lean_dec_ref(x_213);
x_94 = x_209;
x_95 = x_199;
x_96 = x_192;
x_97 = x_200;
x_98 = x_201;
x_99 = x_202;
x_100 = x_203;
x_101 = x_197;
x_102 = x_204;
x_103 = x_206;
x_104 = x_237;
goto block_106;
}
}
else
{
lean_object* x_238; 
lean_dec(x_195);
lean_dec_ref(x_193);
lean_dec_ref(x_2);
x_238 = lean_ctor_get(x_210, 0);
lean_inc(x_238);
lean_dec_ref(x_210);
x_94 = x_209;
x_95 = x_199;
x_96 = x_192;
x_97 = x_200;
x_98 = x_201;
x_99 = x_202;
x_100 = x_203;
x_101 = x_197;
x_102 = x_204;
x_103 = x_206;
x_104 = x_238;
goto block_106;
}
}
else
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_io_get_num_heartbeats();
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_240 = lean_infer_type(x_198, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; uint8_t x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
lean_dec_ref(x_240);
x_242 = 0;
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_243 = l_Lean_Meta_forallMetaTelescope(x_241, x_242, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; uint8_t x_265; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
lean_dec_ref(x_243);
x_245 = lean_ctor_get(x_244, 1);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 0);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_ctor_get(x_245, 1);
x_265 = !lean_is_exclusive(x_245);
if (x_265 == 0)
{
lean_object* x_266; 
x_266 = lean_ctor_get(x_245, 0);
lean_dec(x_266);
x_248 = x_245;
x_249 = x_265;
goto block_264;
}
else
{
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_box(0);
x_249 = x_265;
goto block_264;
}
block_264:
{
lean_object* x_250; lean_object* x_251; uint8_t x_252; 
lean_inc(x_202);
x_250 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg(x_202, x_5);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
lean_dec_ref(x_250);
x_252 = lean_unbox(x_251);
lean_dec(x_251);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; 
lean_del_object(x_248);
x_253 = lean_box(0);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_254 = l_Lean_Meta_rwMatcher___lam__4(x_194, x_193, x_246, x_195, x_208, x_2, x_196, x_247, x_253, x_3, x_4, x_5, x_6);
lean_dec(x_247);
x_161 = x_199;
x_162 = x_192;
x_163 = x_200;
x_164 = x_201;
x_165 = x_202;
x_166 = x_203;
x_167 = x_239;
x_168 = x_197;
x_169 = x_204;
x_170 = x_206;
x_171 = x_254;
goto block_181;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__26, &l_Lean_Meta_rwMatcher___lam__1___closed__26_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__26);
lean_inc(x_247);
x_256 = l_Lean_indentExpr(x_247);
if (x_249 == 0)
{
lean_ctor_set_tag(x_248, 7);
lean_ctor_set(x_248, 1, x_256);
lean_ctor_set(x_248, 0, x_255);
x_257 = x_248;
goto block_262;
}
else
{
lean_object* x_263; 
x_263 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_263, 0, x_255);
lean_ctor_set(x_263, 1, x_256);
x_257 = x_263;
goto block_262;
}
block_262:
{
lean_object* x_258; 
lean_inc(x_202);
x_258 = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(x_202, x_257, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
lean_dec_ref(x_258);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_260 = l_Lean_Meta_rwMatcher___lam__4(x_194, x_193, x_246, x_195, x_208, x_2, x_196, x_247, x_259, x_3, x_4, x_5, x_6);
lean_dec(x_247);
x_161 = x_199;
x_162 = x_192;
x_163 = x_200;
x_164 = x_201;
x_165 = x_202;
x_166 = x_203;
x_167 = x_239;
x_168 = x_197;
x_169 = x_204;
x_170 = x_206;
x_171 = x_260;
goto block_181;
}
else
{
lean_object* x_261; 
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_195);
lean_dec_ref(x_193);
lean_dec_ref(x_2);
x_261 = lean_ctor_get(x_258, 0);
lean_inc(x_261);
lean_dec_ref(x_258);
x_148 = x_199;
x_149 = x_192;
x_150 = x_200;
x_151 = x_201;
x_152 = x_202;
x_153 = x_203;
x_154 = x_239;
x_155 = x_197;
x_156 = x_204;
x_157 = x_206;
x_158 = x_261;
goto block_160;
}
}
}
}
}
else
{
lean_object* x_267; 
lean_dec(x_195);
lean_dec_ref(x_193);
lean_dec_ref(x_2);
x_267 = lean_ctor_get(x_243, 0);
lean_inc(x_267);
lean_dec_ref(x_243);
x_148 = x_199;
x_149 = x_192;
x_150 = x_200;
x_151 = x_201;
x_152 = x_202;
x_153 = x_203;
x_154 = x_239;
x_155 = x_197;
x_156 = x_204;
x_157 = x_206;
x_158 = x_267;
goto block_160;
}
}
else
{
lean_object* x_268; 
lean_dec(x_195);
lean_dec_ref(x_193);
lean_dec_ref(x_2);
x_268 = lean_ctor_get(x_240, 0);
lean_inc(x_268);
lean_dec_ref(x_240);
x_148 = x_199;
x_149 = x_192;
x_150 = x_200;
x_151 = x_201;
x_152 = x_202;
x_153 = x_203;
x_154 = x_239;
x_155 = x_197;
x_156 = x_204;
x_157 = x_206;
x_158 = x_268;
goto block_160;
}
}
}
block_392:
{
uint8_t x_271; 
x_271 = 1;
if (x_270 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; uint8_t x_372; 
x_272 = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(x_2, x_6);
x_273 = lean_ctor_get(x_272, 0);
x_372 = !lean_is_exclusive(x_272);
if (x_372 == 0)
{
x_274 = x_272;
x_275 = x_372;
goto block_371;
}
else
{
lean_inc(x_273);
lean_dec(x_272);
x_274 = lean_box(0);
x_275 = x_372;
goto block_371;
}
block_371:
{
uint8_t x_276; 
x_276 = lean_unbox(x_273);
lean_dec(x_273);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
lean_del_object(x_274);
lean_dec(x_1);
x_277 = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__8));
x_278 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg(x_277, x_5);
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
lean_dec_ref(x_278);
x_280 = lean_unbox(x_279);
lean_dec(x_279);
if (x_280 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_182 = x_271;
goto block_186;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_281 = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__10, &l_Lean_Meta_rwMatcher___closed__10_once, _init_l_Lean_Meta_rwMatcher___closed__10);
lean_inc_ref(x_2);
x_282 = l_Lean_indentExpr(x_2);
x_283 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
x_284 = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(x_277, x_283, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
if (lean_obj_tag(x_284) == 0)
{
lean_dec_ref(x_284);
x_182 = x_271;
goto block_186;
}
else
{
lean_object* x_285; lean_object* x_286; uint8_t x_287; uint8_t x_292; 
lean_dec_ref(x_2);
x_285 = lean_ctor_get(x_284, 0);
x_292 = !lean_is_exclusive(x_284);
if (x_292 == 0)
{
x_286 = x_284;
x_287 = x_292;
goto block_291;
}
else
{
lean_inc(x_285);
lean_dec(x_284);
x_286 = lean_box(0);
x_287 = x_292;
goto block_291;
}
block_291:
{
lean_object* x_288; 
if (x_287 == 0)
{
x_288 = x_286;
goto block_289;
}
else
{
lean_object* x_290; 
x_290 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_290, 0, x_285);
x_288 = x_290;
goto block_289;
}
block_289:
{
return x_288;
}
}
}
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = l_Lean_Expr_getAppFn(x_2);
x_294 = l_Lean_Expr_constName_x21(x_293);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_294);
x_295 = lean_get_congr_match_equations_for(x_294, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
lean_dec_ref(x_295);
x_297 = lean_array_get_size(x_296);
x_298 = lean_nat_dec_lt(x_1, x_297);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; uint8_t x_334; 
lean_dec(x_296);
lean_dec_ref(x_293);
x_299 = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__8));
x_300 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg(x_299, x_5);
x_301 = lean_ctor_get(x_300, 0);
x_334 = !lean_is_exclusive(x_300);
if (x_334 == 0)
{
x_302 = x_300;
x_303 = x_334;
goto block_333;
}
else
{
lean_inc(x_301);
lean_dec(x_300);
x_302 = lean_box(0);
x_303 = x_334;
goto block_333;
}
block_333:
{
uint8_t x_304; 
x_304 = lean_unbox(x_301);
lean_dec(x_301);
if (x_304 == 0)
{
lean_del_object(x_302);
lean_dec(x_294);
lean_del_object(x_274);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_187 = x_271;
goto block_191;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__12, &l_Lean_Meta_rwMatcher___closed__12_once, _init_l_Lean_Meta_rwMatcher___closed__12);
x_306 = l_Nat_reprFast(x_1);
if (x_303 == 0)
{
lean_ctor_set_tag(x_302, 3);
lean_ctor_set(x_302, 0, x_306);
x_307 = x_302;
goto block_331;
}
else
{
lean_object* x_332; 
x_332 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_332, 0, x_306);
x_307 = x_332;
goto block_331;
}
block_331:
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_308 = l_Lean_MessageData_ofFormat(x_307);
x_309 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_309, 0, x_305);
lean_ctor_set(x_309, 1, x_308);
x_310 = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__14, &l_Lean_Meta_rwMatcher___closed__14_once, _init_l_Lean_Meta_rwMatcher___closed__14);
x_311 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
x_312 = l_Nat_reprFast(x_297);
if (x_275 == 0)
{
lean_ctor_set_tag(x_274, 3);
lean_ctor_set(x_274, 0, x_312);
x_313 = x_274;
goto block_329;
}
else
{
lean_object* x_330; 
x_330 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_330, 0, x_312);
x_313 = x_330;
goto block_329;
}
block_329:
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_314 = l_Lean_MessageData_ofFormat(x_313);
x_315 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_315, 0, x_311);
lean_ctor_set(x_315, 1, x_314);
x_316 = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__16, &l_Lean_Meta_rwMatcher___closed__16_once, _init_l_Lean_Meta_rwMatcher___closed__16);
x_317 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
x_318 = l_Lean_MessageData_ofConstName(x_294, x_270);
x_319 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_319, 0, x_317);
lean_ctor_set(x_319, 1, x_318);
x_320 = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(x_299, x_319, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
if (lean_obj_tag(x_320) == 0)
{
lean_dec_ref(x_320);
x_187 = x_271;
goto block_191;
}
else
{
lean_object* x_321; lean_object* x_322; uint8_t x_323; uint8_t x_328; 
lean_dec_ref(x_2);
x_321 = lean_ctor_get(x_320, 0);
x_328 = !lean_is_exclusive(x_320);
if (x_328 == 0)
{
x_322 = x_320;
x_323 = x_328;
goto block_327;
}
else
{
lean_inc(x_321);
lean_dec(x_320);
x_322 = lean_box(0);
x_323 = x_328;
goto block_327;
}
block_327:
{
lean_object* x_324; 
if (x_323 == 0)
{
x_324 = x_322;
goto block_325;
}
else
{
lean_object* x_326; 
x_326 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_326, 0, x_321);
x_324 = x_326;
goto block_325;
}
block_325:
{
return x_324;
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
lean_object* x_335; uint8_t x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_294);
lean_del_object(x_274);
x_335 = lean_ctor_get(x_5, 2);
x_336 = lean_ctor_get_uint8(x_335, sizeof(void*)*1);
x_337 = l_Lean_Expr_getAppNumArgs(x_2);
x_338 = lean_box(x_271);
lean_inc_ref(x_2);
x_339 = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__0___boxed), 8, 2);
lean_closure_set(x_339, 0, x_2);
lean_closure_set(x_339, 1, x_338);
x_340 = lean_box(0);
x_341 = lean_array_get(x_340, x_296, x_1);
lean_dec(x_1);
lean_dec(x_296);
x_342 = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__8));
x_343 = l_Lean_Expr_constLevels_x21(x_293);
lean_dec_ref(x_293);
lean_inc(x_341);
x_344 = l_Lean_mkConst(x_341, x_343);
x_345 = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__17, &l_Lean_Meta_rwMatcher___closed__17_once, _init_l_Lean_Meta_rwMatcher___closed__17);
lean_inc(x_337);
x_346 = lean_mk_array(x_337, x_345);
x_347 = lean_unsigned_to_nat(1u);
x_348 = lean_nat_sub(x_337, x_347);
lean_dec(x_337);
lean_inc_ref(x_2);
x_349 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_346, x_348);
x_350 = l_Lean_mkAppN(x_344, x_349);
lean_dec_ref(x_349);
if (x_336 == 0)
{
lean_object* x_351; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_341);
x_351 = l_Lean_Meta_rwMatcher___lam__1(x_350, x_342, x_271, x_341, x_2, x_270, x_3, x_4, x_5, x_6);
x_65 = x_339;
x_66 = x_341;
x_67 = x_342;
x_68 = x_351;
goto block_70;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_352 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg(x_342, x_5);
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
lean_dec_ref(x_352);
x_354 = lean_box(x_270);
lean_inc_ref(x_2);
lean_inc(x_341);
x_355 = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__2___boxed), 9, 3);
lean_closure_set(x_355, 0, x_341);
lean_closure_set(x_355, 1, x_354);
lean_closure_set(x_355, 2, x_2);
x_356 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__1));
x_357 = lean_unbox(x_353);
if (x_357 == 0)
{
lean_object* x_358; uint8_t x_359; 
x_358 = l_Lean_trace_profiler;
x_359 = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11(x_335, x_358);
if (x_359 == 0)
{
lean_object* x_360; 
lean_dec_ref(x_355);
lean_dec(x_353);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_341);
x_360 = l_Lean_Meta_rwMatcher___lam__1(x_350, x_342, x_271, x_341, x_2, x_270, x_3, x_4, x_5, x_6);
x_65 = x_339;
x_66 = x_341;
x_67 = x_342;
x_68 = x_360;
goto block_70;
}
else
{
uint8_t x_361; 
x_361 = lean_unbox(x_353);
lean_dec(x_353);
lean_inc_ref(x_335);
lean_inc(x_341);
lean_inc_ref(x_350);
x_192 = x_361;
x_193 = x_350;
x_194 = x_271;
x_195 = x_341;
x_196 = x_270;
x_197 = x_355;
x_198 = x_350;
x_199 = x_271;
x_200 = x_339;
x_201 = x_356;
x_202 = x_342;
x_203 = x_341;
x_204 = x_335;
goto block_269;
}
}
else
{
uint8_t x_362; 
x_362 = lean_unbox(x_353);
lean_dec(x_353);
lean_inc_ref(x_335);
lean_inc(x_341);
lean_inc_ref(x_350);
x_192 = x_362;
x_193 = x_350;
x_194 = x_271;
x_195 = x_341;
x_196 = x_270;
x_197 = x_355;
x_198 = x_350;
x_199 = x_271;
x_200 = x_339;
x_201 = x_356;
x_202 = x_342;
x_203 = x_341;
x_204 = x_335;
goto block_269;
}
}
}
}
else
{
lean_object* x_363; lean_object* x_364; uint8_t x_365; uint8_t x_370; 
lean_dec(x_294);
lean_dec_ref(x_293);
lean_del_object(x_274);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_363 = lean_ctor_get(x_295, 0);
x_370 = !lean_is_exclusive(x_295);
if (x_370 == 0)
{
x_364 = x_295;
x_365 = x_370;
goto block_369;
}
else
{
lean_inc(x_363);
lean_dec(x_295);
x_364 = lean_box(0);
x_365 = x_370;
goto block_369;
}
block_369:
{
lean_object* x_366; 
if (x_365 == 0)
{
x_366 = x_364;
goto block_367;
}
else
{
lean_object* x_368; 
x_368 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_368, 0, x_363);
x_366 = x_368;
goto block_367;
}
block_367:
{
return x_366;
}
}
}
}
}
}
else
{
lean_object* x_373; 
lean_dec(x_1);
x_373 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_rwMatcher_spec__15(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; uint8_t x_376; uint8_t x_383; 
x_374 = lean_ctor_get(x_373, 0);
x_383 = !lean_is_exclusive(x_373);
if (x_383 == 0)
{
x_375 = x_373;
x_376 = x_383;
goto block_382;
}
else
{
lean_inc(x_374);
lean_dec(x_373);
x_375 = lean_box(0);
x_376 = x_383;
goto block_382;
}
block_382:
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_377 = lean_box(0);
x_378 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_378, 0, x_374);
lean_ctor_set(x_378, 1, x_377);
lean_ctor_set_uint8(x_378, sizeof(void*)*2, x_271);
if (x_376 == 0)
{
lean_ctor_set(x_375, 0, x_378);
x_379 = x_375;
goto block_380;
}
else
{
lean_object* x_381; 
x_381 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_381, 0, x_378);
x_379 = x_381;
goto block_380;
}
block_380:
{
return x_379;
}
}
}
else
{
lean_object* x_384; lean_object* x_385; uint8_t x_386; uint8_t x_391; 
x_384 = lean_ctor_get(x_373, 0);
x_391 = !lean_is_exclusive(x_373);
if (x_391 == 0)
{
x_385 = x_373;
x_386 = x_391;
goto block_390;
}
else
{
lean_inc(x_384);
lean_dec(x_373);
x_385 = lean_box(0);
x_386 = x_391;
goto block_390;
}
block_390:
{
lean_object* x_387; 
if (x_386 == 0)
{
x_387 = x_385;
goto block_388;
}
else
{
lean_object* x_389; 
x_389 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_389, 0, x_384);
x_387 = x_389;
goto block_388;
}
block_388:
{
return x_387;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_rwMatcher(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___redArg(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_3);
x_16 = lean_unbox(x_6);
x_17 = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12(x_1, x_2, x_15, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_5);
return x_17;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6(x_1, x_2, x_5, x_4);
lean_dec(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6_spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6_spec__20___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6_spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6_spec__20(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp_Types(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Assumption(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Match_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Types(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assumption(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Refl(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_Rewrite(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Match_Rewrite(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Match_Rewrite(builtin);
}
#ifdef __cplusplus
}
#endif
