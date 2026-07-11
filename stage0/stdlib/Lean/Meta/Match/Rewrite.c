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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_Lean_Meta_isMatcherAppCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_io_mono_nanos_now();
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis(lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_hrefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* lean_get_congr_match_equations_for(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_rwIfWith___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l_Lean_Meta_rwIfWith___closed__0 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__0_value;
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
static const lean_ctor_object l_Lean_Meta_rwIfWith___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwIfWith___closed__14_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_rwIfWith___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_rwIfWith___closed__16_value_aux_0),((lean_object*)&l_Lean_Meta_rwIfWith___closed__15_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Meta_rwIfWith___closed__16 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__16_value;
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
LEAN_EXPORT lean_object* l_Lean_Meta_rwIfWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwIfWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__3___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_rwMatcher___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "rewriting with "};
static const lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__1;
static const lean_string_object l_Lean_Meta_rwMatcher___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " in"};
static const lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__9(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Failed to resolve `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Failed to discharge `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_rwMatcher___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Could not un-HEq `"};
static const lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__1;
static const lean_string_object l_Lean_Meta_rwMatcher___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`:"};
static const lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__2 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__2___closed__2_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__3;
static const lean_string_object l_Lean_Meta_rwMatcher___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__4 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__2___closed__4_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__5;
static const lean_string_object l_Lean_Meta_rwMatcher___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Not all hypotheses of `"};
static const lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__6 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__2___closed__6_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__7;
static const lean_string_object l_Lean_Meta_rwMatcher___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "` could be discharged: "};
static const lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__8 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__2___closed__8_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__2___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__9;
static const lean_array_object l_Lean_Meta_rwMatcher___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__10 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__2___closed__10_value;
static const lean_string_object l_Lean_Meta_rwMatcher___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Left-hand side `"};
static const lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__11 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__2___closed__11_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__2___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__12;
static const lean_string_object l_Lean_Meta_rwMatcher___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "` of `"};
static const lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__13 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__2___closed__13_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__2___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__14;
static const lean_string_object l_Lean_Meta_rwMatcher___lam__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` does not apply to `"};
static const lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__15 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__2___closed__15_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__2___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__16;
static const lean_string_object l_Lean_Meta_rwMatcher___lam__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__17 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__2___closed__17_value;
static const lean_ctor_object l_Lean_Meta_rwMatcher___lam__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwMatcher___lam__2___closed__17_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__18 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__2___closed__18_value;
static const lean_string_object l_Lean_Meta_rwMatcher___lam__2___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__19 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__2___closed__19_value;
static const lean_ctor_object l_Lean_Meta_rwMatcher___lam__2___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwMatcher___lam__2___closed__19_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__20 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__2___closed__20_value;
static const lean_string_object l_Lean_Meta_rwMatcher___lam__2___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Type of `"};
static const lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__21 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__2___closed__21_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__2___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__22;
static const lean_string_object l_Lean_Meta_rwMatcher___lam__2___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "` is not an equality"};
static const lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__23 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__2___closed__23_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__2___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__24;
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__9(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__9___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__7_spec__10(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__10___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_rwMatcher___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__0 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__0_value;
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwMatcher___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_rwMatcher___closed__1 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__1_value;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Failed to apply "};
static const lean_object* l_Lean_Meta_rwMatcher___closed__2 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__2_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__3;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__4 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__4_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__5;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_rwMatcher___closed__6;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "eqProof has type"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__7 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__7_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__8;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__9 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__9_value;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Match"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__10 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__10_value;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__11 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__11_value;
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwMatcher___closed__9_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_rwMatcher___closed__12_value_aux_0),((lean_object*)&l_Lean_Meta_rwMatcher___closed__10_value),LEAN_SCALAR_PTR_LITERAL(250, 1, 225, 180, 135, 246, 184, 244)}};
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_rwMatcher___closed__12_value_aux_1),((lean_object*)&l_Lean_Meta_rwMatcher___closed__11_value),LEAN_SCALAR_PTR_LITERAL(253, 56, 25, 25, 156, 146, 62, 130)}};
static const lean_object* l_Lean_Meta_rwMatcher___closed__12 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__12_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__13;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Not a matcher application:"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__14 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__14_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__15;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "When trying to reduce arm "};
static const lean_object* l_Lean_Meta_rwMatcher___closed__16 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__16_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__17;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ", only "};
static const lean_object* l_Lean_Meta_rwMatcher___closed__18 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__18_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__19;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " equations for "};
static const lean_object* l_Lean_Meta_rwMatcher___closed__20 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__20_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__21;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__22;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "PSum"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__23 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__23_value;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "casesOn"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__24 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__24_value;
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwMatcher___closed__23_value),LEAN_SCALAR_PTR_LITERAL(147, 224, 206, 173, 168, 27, 198, 53)}};
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_rwMatcher___closed__25_value_aux_0),((lean_object*)&l_Lean_Meta_rwMatcher___closed__24_value),LEAN_SCALAR_PTR_LITERAL(166, 115, 173, 38, 27, 113, 160, 8)}};
static const lean_object* l_Lean_Meta_rwMatcher___closed__25 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__25_value;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "PSigma"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__26 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__26_value;
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwMatcher___closed__26_value),LEAN_SCALAR_PTR_LITERAL(0, 171, 149, 177, 120, 131, 37, 223)}};
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_rwMatcher___closed__27_value_aux_0),((lean_object*)&l_Lean_Meta_rwMatcher___closed__24_value),LEAN_SCALAR_PTR_LITERAL(225, 129, 3, 119, 45, 252, 168, 83)}};
static const lean_object* l_Lean_Meta_rwMatcher___closed__27 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__27_value;
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_rwIfWith___closed__17(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = lean_box(0);
v___x_28_ = ((lean_object*)(l_Lean_Meta_rwIfWith___closed__16));
v___x_29_ = l_Lean_mkConst(v___x_28_, v___x_27_);
return v___x_29_;
}
}
static lean_object* _init_l_Lean_Meta_rwIfWith___closed__20(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_box(0);
v___x_35_ = ((lean_object*)(l_Lean_Meta_rwIfWith___closed__19));
v___x_36_ = l_Lean_mkConst(v___x_35_, v___x_34_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwIfWith(lean_object* v_hc_45_, lean_object* v_e_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_57_; 
lean_inc_ref(v_e_46_);
v___x_57_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_46_, v_a_48_);
if (lean_obj_tag(v___x_57_) == 0)
{
lean_object* v_a_58_; lean_object* v___x_59_; uint8_t v___x_60_; 
v_a_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc(v_a_58_);
lean_dec_ref_known(v___x_57_, 1);
v___x_59_ = l_Lean_Expr_cleanupAnnotations(v_a_58_);
v___x_60_ = l_Lean_Expr_isApp(v___x_59_);
if (v___x_60_ == 0)
{
lean_dec_ref(v___x_59_);
lean_dec_ref(v_hc_45_);
goto v___jp_52_;
}
else
{
lean_object* v_arg_61_; lean_object* v___x_62_; uint8_t v___x_63_; 
v_arg_61_ = lean_ctor_get(v___x_59_, 1);
lean_inc_ref(v_arg_61_);
v___x_62_ = l_Lean_Expr_appFnCleanup___redArg(v___x_59_);
v___x_63_ = l_Lean_Expr_isApp(v___x_62_);
if (v___x_63_ == 0)
{
lean_dec_ref(v___x_62_);
lean_dec_ref(v_arg_61_);
lean_dec_ref(v_hc_45_);
goto v___jp_52_;
}
else
{
lean_object* v_arg_64_; lean_object* v___x_65_; uint8_t v___x_66_; 
v_arg_64_ = lean_ctor_get(v___x_62_, 1);
lean_inc_ref(v_arg_64_);
v___x_65_ = l_Lean_Expr_appFnCleanup___redArg(v___x_62_);
v___x_66_ = l_Lean_Expr_isApp(v___x_65_);
if (v___x_66_ == 0)
{
lean_dec_ref(v___x_65_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
lean_dec_ref(v_hc_45_);
goto v___jp_52_;
}
else
{
lean_object* v_arg_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v_arg_67_ = lean_ctor_get(v___x_65_, 1);
lean_inc_ref(v_arg_67_);
v___x_68_ = l_Lean_Expr_appFnCleanup___redArg(v___x_65_);
v___x_69_ = l_Lean_Expr_isApp(v___x_68_);
if (v___x_69_ == 0)
{
lean_dec_ref(v___x_68_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
lean_dec_ref(v_hc_45_);
goto v___jp_52_;
}
else
{
lean_object* v_arg_70_; lean_object* v___x_71_; lean_object* v___x_72_; uint8_t v___x_73_; 
v_arg_70_ = lean_ctor_get(v___x_68_, 1);
lean_inc_ref(v_arg_70_);
v___x_71_ = l_Lean_Expr_appFnCleanup___redArg(v___x_68_);
v___x_72_ = ((lean_object*)(l_Lean_Meta_rwIfWith___closed__1));
v___x_73_ = l_Lean_Expr_isConstOf(v___x_71_, v___x_72_);
if (v___x_73_ == 0)
{
uint8_t v___x_74_; 
v___x_74_ = l_Lean_Expr_isApp(v___x_71_);
if (v___x_74_ == 0)
{
lean_dec_ref(v___x_71_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
lean_dec_ref(v_hc_45_);
goto v___jp_52_;
}
else
{
lean_object* v_arg_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
v_arg_75_ = lean_ctor_get(v___x_71_, 1);
lean_inc_ref(v_arg_75_);
v___x_76_ = l_Lean_Expr_appFnCleanup___redArg(v___x_71_);
v___x_77_ = ((lean_object*)(l_Lean_Meta_rwIfWith___closed__3));
v___x_78_ = l_Lean_Expr_isConstOf(v___x_76_, v___x_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = ((lean_object*)(l_Lean_Meta_rwIfWith___closed__5));
v___x_80_ = l_Lean_Expr_isConstOf(v___x_76_, v___x_79_);
if (v___x_80_ == 0)
{
lean_dec_ref(v___x_76_);
lean_dec_ref(v_arg_75_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
lean_dec_ref(v_hc_45_);
goto v___jp_52_;
}
else
{
lean_object* v___x_81_; 
lean_inc(v_a_50_);
lean_inc_ref(v_a_49_);
lean_inc(v_a_48_);
lean_inc_ref(v_a_47_);
lean_inc_ref(v_hc_45_);
v___x_81_ = lean_infer_type(v_hc_45_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v_a_82_; lean_object* v___x_83_; 
v_a_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_a_82_);
lean_dec_ref_known(v___x_81_, 1);
lean_inc_ref(v_arg_70_);
v___x_83_ = l_Lean_Meta_isExprDefEq(v_arg_70_, v_a_82_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_83_) == 0)
{
lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_148_; 
v_a_84_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_148_ == 0)
{
v___x_86_ = v___x_83_;
v_isShared_87_ = v_isSharedCheck_148_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_dec(v___x_83_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_148_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_88_ = l_Lean_Expr_constLevels_x21(v___x_76_);
lean_dec_ref(v___x_76_);
v___x_89_ = lean_unbox(v_a_84_);
lean_dec(v_a_84_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; 
lean_del_object(v___x_86_);
lean_inc(v_a_50_);
lean_inc_ref(v_a_49_);
lean_inc(v_a_48_);
lean_inc_ref(v_a_47_);
lean_inc_ref(v_hc_45_);
v___x_90_ = lean_infer_type(v_hc_45_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v_a_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v_a_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_a_91_);
lean_dec_ref_known(v___x_90_, 1);
lean_inc_ref(v_arg_70_);
v___x_92_ = l_Lean_mkNot(v_arg_70_);
v___x_93_ = l_Lean_Meta_isExprDefEq(v___x_92_, v_a_91_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_93_) == 0)
{
lean_object* v_a_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_115_; 
v_a_94_ = lean_ctor_get(v___x_93_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_115_ == 0)
{
v___x_96_ = v___x_93_;
v_isShared_97_ = v_isSharedCheck_115_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_a_94_);
lean_dec(v___x_93_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_115_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
uint8_t v___x_98_; 
v___x_98_ = lean_unbox(v_a_94_);
lean_dec(v_a_94_);
if (v___x_98_ == 0)
{
lean_del_object(v___x_96_);
lean_dec(v___x_88_);
lean_dec_ref(v_arg_75_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
lean_dec_ref(v_hc_45_);
goto v___jp_52_;
}
else
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_113_; 
lean_dec_ref(v_e_46_);
v___x_99_ = ((lean_object*)(l_Lean_Meta_rwIfWith___closed__7));
v___x_100_ = l_Lean_mkConst(v___x_99_, v___x_88_);
v___x_101_ = lean_unsigned_to_nat(6u);
v___x_102_ = lean_mk_empty_array_with_capacity(v___x_101_);
v___x_103_ = lean_array_push(v___x_102_, v_arg_70_);
v___x_104_ = lean_array_push(v___x_103_, v_arg_67_);
v___x_105_ = lean_array_push(v___x_104_, v_hc_45_);
v___x_106_ = lean_array_push(v___x_105_, v_arg_75_);
v___x_107_ = lean_array_push(v___x_106_, v_arg_64_);
lean_inc_ref(v_arg_61_);
v___x_108_ = lean_array_push(v___x_107_, v_arg_61_);
v___x_109_ = l_Lean_mkAppN(v___x_100_, v___x_108_);
lean_dec_ref(v___x_108_);
v___x_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
v___x_111_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_111_, 0, v_arg_61_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
lean_ctor_set_uint8(v___x_111_, sizeof(void*)*2, v___x_80_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 0, v___x_111_);
v___x_113_ = v___x_96_;
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
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_123_; 
lean_dec(v___x_88_);
lean_dec_ref(v_arg_75_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_hc_45_);
v_a_116_ = lean_ctor_get(v___x_93_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_123_ == 0)
{
v___x_118_ = v___x_93_;
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_93_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_a_116_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
else
{
lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
lean_dec(v___x_88_);
lean_dec_ref(v_arg_75_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_hc_45_);
v_a_124_ = lean_ctor_get(v___x_90_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_131_ == 0)
{
v___x_126_ = v___x_90_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_90_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_124_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
else
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_146_; 
lean_dec_ref(v_e_46_);
v___x_132_ = ((lean_object*)(l_Lean_Meta_rwIfWith___closed__9));
v___x_133_ = l_Lean_mkConst(v___x_132_, v___x_88_);
v___x_134_ = lean_unsigned_to_nat(6u);
v___x_135_ = lean_mk_empty_array_with_capacity(v___x_134_);
v___x_136_ = lean_array_push(v___x_135_, v_arg_70_);
v___x_137_ = lean_array_push(v___x_136_, v_arg_67_);
v___x_138_ = lean_array_push(v___x_137_, v_hc_45_);
v___x_139_ = lean_array_push(v___x_138_, v_arg_75_);
lean_inc_ref(v_arg_64_);
v___x_140_ = lean_array_push(v___x_139_, v_arg_64_);
v___x_141_ = lean_array_push(v___x_140_, v_arg_61_);
v___x_142_ = l_Lean_mkAppN(v___x_133_, v___x_141_);
lean_dec_ref(v___x_141_);
v___x_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
v___x_144_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_144_, 0, v_arg_64_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
lean_ctor_set_uint8(v___x_144_, sizeof(void*)*2, v___x_80_);
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 0, v___x_144_);
v___x_146_ = v___x_86_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_144_);
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
else
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
lean_dec_ref(v___x_76_);
lean_dec_ref(v_arg_75_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_hc_45_);
v_a_149_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_83_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_83_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_149_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
else
{
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_164_; 
lean_dec_ref(v___x_76_);
lean_dec_ref(v_arg_75_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_hc_45_);
v_a_157_ = lean_ctor_get(v___x_81_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_164_ == 0)
{
v___x_159_ = v___x_81_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_81_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
if (v_isShared_160_ == 0)
{
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_a_157_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
}
else
{
lean_object* v___x_165_; 
lean_inc(v_a_50_);
lean_inc_ref(v_a_49_);
lean_inc(v_a_48_);
lean_inc_ref(v_a_47_);
lean_inc_ref(v_hc_45_);
v___x_165_ = lean_infer_type(v_hc_45_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v_a_166_; lean_object* v___x_167_; 
v_a_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_a_166_);
lean_dec_ref_known(v___x_165_, 1);
lean_inc_ref(v_arg_70_);
v___x_167_ = l_Lean_Meta_isExprDefEq(v_arg_70_, v_a_166_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_240_; 
v_a_168_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_240_ == 0)
{
v___x_170_ = v___x_167_;
v_isShared_171_ = v_isSharedCheck_240_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_167_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_240_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = l_Lean_Expr_constLevels_x21(v___x_76_);
lean_dec_ref(v___x_76_);
v___x_173_ = lean_unbox(v_a_168_);
lean_dec(v_a_168_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; 
lean_del_object(v___x_170_);
lean_inc(v_a_50_);
lean_inc_ref(v_a_49_);
lean_inc(v_a_48_);
lean_inc_ref(v_a_47_);
lean_inc_ref(v_hc_45_);
v___x_174_ = lean_infer_type(v_hc_45_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_a_175_);
lean_dec_ref_known(v___x_174_, 1);
lean_inc_ref(v_arg_70_);
v___x_176_ = l_Lean_mkNot(v_arg_70_);
v___x_177_ = l_Lean_Meta_isExprDefEq(v___x_176_, v_a_175_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_203_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_203_ == 0)
{
v___x_180_ = v___x_177_;
v_isShared_181_ = v_isSharedCheck_203_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_177_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_203_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
uint8_t v___x_182_; 
v___x_182_ = lean_unbox(v_a_178_);
lean_dec(v_a_178_);
if (v___x_182_ == 0)
{
lean_del_object(v___x_180_);
lean_dec(v___x_172_);
lean_dec_ref(v_arg_75_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
lean_dec_ref(v_hc_45_);
goto v___jp_52_;
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_201_; 
lean_dec_ref(v_e_46_);
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = lean_mk_empty_array_with_capacity(v___x_183_);
lean_inc_ref(v_hc_45_);
v___x_185_ = lean_array_push(v___x_184_, v_hc_45_);
lean_inc_ref(v_arg_61_);
v___x_186_ = l_Lean_Expr_beta(v_arg_61_, v___x_185_);
v___x_187_ = ((lean_object*)(l_Lean_Meta_rwIfWith___closed__11));
v___x_188_ = l_Lean_mkConst(v___x_187_, v___x_172_);
v___x_189_ = lean_unsigned_to_nat(6u);
v___x_190_ = lean_mk_empty_array_with_capacity(v___x_189_);
v___x_191_ = lean_array_push(v___x_190_, v_arg_70_);
v___x_192_ = lean_array_push(v___x_191_, v_arg_67_);
v___x_193_ = lean_array_push(v___x_192_, v_hc_45_);
v___x_194_ = lean_array_push(v___x_193_, v_arg_75_);
v___x_195_ = lean_array_push(v___x_194_, v_arg_64_);
v___x_196_ = lean_array_push(v___x_195_, v_arg_61_);
v___x_197_ = l_Lean_mkAppN(v___x_188_, v___x_196_);
lean_dec_ref(v___x_196_);
v___x_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
v___x_199_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_199_, 0, v___x_186_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
lean_ctor_set_uint8(v___x_199_, sizeof(void*)*2, v___x_78_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_199_);
v___x_201_ = v___x_180_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_199_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
else
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
lean_dec(v___x_172_);
lean_dec_ref(v_arg_75_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_hc_45_);
v_a_204_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_211_ == 0)
{
v___x_206_ = v___x_177_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_177_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_a_204_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
else
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_219_; 
lean_dec(v___x_172_);
lean_dec_ref(v_arg_75_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_hc_45_);
v_a_212_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_219_ == 0)
{
v___x_214_ = v___x_174_;
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_174_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_a_212_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
else
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
lean_dec_ref(v_e_46_);
v___x_220_ = lean_unsigned_to_nat(1u);
v___x_221_ = lean_mk_empty_array_with_capacity(v___x_220_);
lean_inc_ref(v_hc_45_);
v___x_222_ = lean_array_push(v___x_221_, v_hc_45_);
lean_inc_ref(v_arg_64_);
v___x_223_ = l_Lean_Expr_beta(v_arg_64_, v___x_222_);
v___x_224_ = ((lean_object*)(l_Lean_Meta_rwIfWith___closed__13));
v___x_225_ = l_Lean_mkConst(v___x_224_, v___x_172_);
v___x_226_ = lean_unsigned_to_nat(6u);
v___x_227_ = lean_mk_empty_array_with_capacity(v___x_226_);
v___x_228_ = lean_array_push(v___x_227_, v_arg_70_);
v___x_229_ = lean_array_push(v___x_228_, v_arg_67_);
v___x_230_ = lean_array_push(v___x_229_, v_hc_45_);
v___x_231_ = lean_array_push(v___x_230_, v_arg_75_);
v___x_232_ = lean_array_push(v___x_231_, v_arg_64_);
v___x_233_ = lean_array_push(v___x_232_, v_arg_61_);
v___x_234_ = l_Lean_mkAppN(v___x_225_, v___x_233_);
lean_dec_ref(v___x_233_);
v___x_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
v___x_236_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_236_, 0, v___x_223_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*2, v___x_78_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_236_);
v___x_238_ = v___x_170_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
else
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_248_; 
lean_dec_ref(v___x_76_);
lean_dec_ref(v_arg_75_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_hc_45_);
v_a_241_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_248_ == 0)
{
v___x_243_ = v___x_167_;
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_167_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_244_ == 0)
{
v___x_246_ = v___x_243_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_a_241_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
else
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_256_; 
lean_dec_ref(v___x_76_);
lean_dec_ref(v_arg_75_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_hc_45_);
v_a_249_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_256_ == 0)
{
v___x_251_ = v___x_165_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_165_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_252_ == 0)
{
v___x_254_ = v___x_251_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_249_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
}
}
else
{
lean_object* v___x_257_; 
lean_inc(v_a_50_);
lean_inc_ref(v_a_49_);
lean_inc(v_a_48_);
lean_inc_ref(v_a_47_);
lean_inc_ref(v_hc_45_);
v___x_257_ = lean_infer_type(v_hc_45_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_a_258_);
lean_dec_ref_known(v___x_257_, 1);
v___x_259_ = lean_obj_once(&l_Lean_Meta_rwIfWith___closed__17, &l_Lean_Meta_rwIfWith___closed__17_once, _init_l_Lean_Meta_rwIfWith___closed__17);
lean_inc_ref(v_arg_67_);
v___x_260_ = l_Lean_Meta_mkEq(v_arg_67_, v___x_259_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; lean_object* v___x_262_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_a_261_);
lean_dec_ref_known(v___x_260_, 1);
v___x_262_ = l_Lean_Meta_isExprDefEq(v_a_258_, v_a_261_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_335_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_335_ == 0)
{
v___x_265_ = v___x_262_;
v_isShared_266_ = v_isSharedCheck_335_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_262_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_335_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_267_ = l_Lean_Expr_constLevels_x21(v___x_71_);
lean_dec_ref(v___x_71_);
v___x_268_ = lean_unbox(v_a_263_);
lean_dec(v_a_263_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
lean_del_object(v___x_265_);
lean_inc(v_a_50_);
lean_inc_ref(v_a_49_);
lean_inc(v_a_48_);
lean_inc_ref(v_a_47_);
lean_inc_ref(v_hc_45_);
v___x_269_ = lean_infer_type(v_hc_45_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v_a_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_a_270_);
lean_dec_ref_known(v___x_269_, 1);
v___x_271_ = lean_obj_once(&l_Lean_Meta_rwIfWith___closed__20, &l_Lean_Meta_rwIfWith___closed__20_once, _init_l_Lean_Meta_rwIfWith___closed__20);
lean_inc_ref(v_arg_67_);
v___x_272_ = l_Lean_Meta_mkEq(v_arg_67_, v___x_271_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v_a_273_; lean_object* v___x_274_; 
v_a_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_a_273_);
lean_dec_ref_known(v___x_272_, 1);
v___x_274_ = l_Lean_Meta_isExprDefEq(v_a_270_, v_a_273_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_295_; 
v_a_275_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_295_ == 0)
{
v___x_277_ = v___x_274_;
v_isShared_278_ = v_isSharedCheck_295_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_274_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_295_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
uint8_t v___x_279_; 
v___x_279_ = lean_unbox(v_a_275_);
lean_dec(v_a_275_);
if (v___x_279_ == 0)
{
lean_del_object(v___x_277_);
lean_dec(v___x_267_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
lean_dec_ref(v_hc_45_);
goto v___jp_52_;
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_293_; 
lean_dec_ref(v_e_46_);
v___x_280_ = ((lean_object*)(l_Lean_Meta_rwIfWith___closed__22));
v___x_281_ = l_Lean_mkConst(v___x_280_, v___x_267_);
v___x_282_ = lean_unsigned_to_nat(5u);
v___x_283_ = lean_mk_empty_array_with_capacity(v___x_282_);
v___x_284_ = lean_array_push(v___x_283_, v_arg_70_);
v___x_285_ = lean_array_push(v___x_284_, v_arg_67_);
v___x_286_ = lean_array_push(v___x_285_, v_arg_64_);
lean_inc_ref(v_arg_61_);
v___x_287_ = lean_array_push(v___x_286_, v_arg_61_);
v___x_288_ = lean_array_push(v___x_287_, v_hc_45_);
v___x_289_ = l_Lean_mkAppN(v___x_281_, v___x_288_);
lean_dec_ref(v___x_288_);
v___x_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
v___x_291_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_291_, 0, v_arg_61_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
lean_ctor_set_uint8(v___x_291_, sizeof(void*)*2, v___x_73_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 0, v___x_291_);
v___x_293_ = v___x_277_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
else
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
lean_dec(v___x_267_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_hc_45_);
v_a_296_ = lean_ctor_get(v___x_274_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v___x_274_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_274_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_296_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
else
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
lean_dec(v_a_270_);
lean_dec(v___x_267_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_hc_45_);
v_a_304_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_311_ == 0)
{
v___x_306_ = v___x_272_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_272_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_304_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
else
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
lean_dec(v___x_267_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_hc_45_);
v_a_312_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_319_ == 0)
{
v___x_314_ = v___x_269_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_269_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
else
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
lean_dec_ref(v_e_46_);
v___x_320_ = ((lean_object*)(l_Lean_Meta_rwIfWith___closed__24));
v___x_321_ = l_Lean_mkConst(v___x_320_, v___x_267_);
v___x_322_ = lean_unsigned_to_nat(5u);
v___x_323_ = lean_mk_empty_array_with_capacity(v___x_322_);
v___x_324_ = lean_array_push(v___x_323_, v_arg_70_);
v___x_325_ = lean_array_push(v___x_324_, v_arg_67_);
lean_inc_ref(v_arg_64_);
v___x_326_ = lean_array_push(v___x_325_, v_arg_64_);
v___x_327_ = lean_array_push(v___x_326_, v_arg_61_);
v___x_328_ = lean_array_push(v___x_327_, v_hc_45_);
v___x_329_ = l_Lean_mkAppN(v___x_321_, v___x_328_);
lean_dec_ref(v___x_328_);
v___x_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
v___x_331_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_331_, 0, v_arg_64_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*2, v___x_73_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v___x_331_);
v___x_333_ = v___x_265_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
else
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
lean_dec_ref(v___x_71_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_hc_45_);
v_a_336_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_262_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_262_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec(v_a_258_);
lean_dec_ref(v___x_71_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_hc_45_);
v_a_344_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_260_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_260_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
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
lean_dec_ref(v___x_71_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_hc_45_);
v_a_352_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_257_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_257_);
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
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
lean_dec_ref(v_e_46_);
lean_dec_ref(v_hc_45_);
v_a_360_ = lean_ctor_get(v___x_57_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_57_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_57_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_57_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
v___jp_52_:
{
lean_object* v___x_53_; uint8_t v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_53_ = lean_box(0);
v___x_54_ = 1;
v___x_55_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_55_, 0, v_e_46_);
lean_ctor_set(v___x_55_, 1, v___x_53_);
lean_ctor_set_uint8(v___x_55_, sizeof(void*)*2, v___x_54_);
v___x_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
return v___x_56_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwIfWith___boxed(lean_object* v_hc_368_, lean_object* v_e_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_Meta_rwIfWith(v_hc_368_, v_e_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
lean_dec(v_a_371_);
lean_dec_ref(v_a_370_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(lean_object* v_e_376_, lean_object* v___y_377_){
_start:
{
lean_object* v___x_379_; lean_object* v_env_380_; uint8_t v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_379_ = lean_st_ref_get(v___y_377_);
v_env_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc_ref(v_env_380_);
lean_dec(v___x_379_);
v___x_381_ = l_Lean_Meta_isMatcherAppCore(v_env_380_, v_e_376_);
v___x_382_ = lean_box(v___x_381_);
v___x_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg___boxed(lean_object* v_e_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(v_e_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v_e_384_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1(lean_object* v_e_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(v_e_388_, v___y_392_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___boxed(lean_object* v_e_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1(v_e_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec_ref(v_e_395_);
return v_res_401_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_402_ = lean_unsigned_to_nat(32u);
v___x_403_ = lean_mk_empty_array_with_capacity(v___x_402_);
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
return v___x_404_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_405_ = ((size_t)5ULL);
v___x_406_ = lean_unsigned_to_nat(0u);
v___x_407_ = lean_unsigned_to_nat(32u);
v___x_408_ = lean_mk_empty_array_with_capacity(v___x_407_);
v___x_409_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__3___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__3___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__3___redArg___closed__0);
v___x_410_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v___x_408_);
lean_ctor_set(v___x_410_, 2, v___x_406_);
lean_ctor_set(v___x_410_, 3, v___x_406_);
lean_ctor_set_usize(v___x_410_, 4, v___x_405_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__3___redArg(lean_object* v___y_411_){
_start:
{
lean_object* v___x_413_; lean_object* v_traceState_414_; lean_object* v_traces_415_; lean_object* v___x_416_; lean_object* v_traceState_417_; lean_object* v_env_418_; lean_object* v_nextMacroScope_419_; lean_object* v_ngen_420_; lean_object* v_auxDeclNGen_421_; lean_object* v_cache_422_; lean_object* v_messages_423_; lean_object* v_infoState_424_; lean_object* v_snapshotTasks_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_444_; 
v___x_413_ = lean_st_ref_get(v___y_411_);
v_traceState_414_ = lean_ctor_get(v___x_413_, 4);
lean_inc_ref(v_traceState_414_);
lean_dec(v___x_413_);
v_traces_415_ = lean_ctor_get(v_traceState_414_, 0);
lean_inc_ref(v_traces_415_);
lean_dec_ref(v_traceState_414_);
v___x_416_ = lean_st_ref_take(v___y_411_);
v_traceState_417_ = lean_ctor_get(v___x_416_, 4);
v_env_418_ = lean_ctor_get(v___x_416_, 0);
v_nextMacroScope_419_ = lean_ctor_get(v___x_416_, 1);
v_ngen_420_ = lean_ctor_get(v___x_416_, 2);
v_auxDeclNGen_421_ = lean_ctor_get(v___x_416_, 3);
v_cache_422_ = lean_ctor_get(v___x_416_, 5);
v_messages_423_ = lean_ctor_get(v___x_416_, 6);
v_infoState_424_ = lean_ctor_get(v___x_416_, 7);
v_snapshotTasks_425_ = lean_ctor_get(v___x_416_, 8);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_444_ == 0)
{
v___x_427_ = v___x_416_;
v_isShared_428_ = v_isSharedCheck_444_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_snapshotTasks_425_);
lean_inc(v_infoState_424_);
lean_inc(v_messages_423_);
lean_inc(v_cache_422_);
lean_inc(v_traceState_417_);
lean_inc(v_auxDeclNGen_421_);
lean_inc(v_ngen_420_);
lean_inc(v_nextMacroScope_419_);
lean_inc(v_env_418_);
lean_dec(v___x_416_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_444_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
uint64_t v_tid_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_442_; 
v_tid_429_ = lean_ctor_get_uint64(v_traceState_417_, sizeof(void*)*1);
v_isSharedCheck_442_ = !lean_is_exclusive(v_traceState_417_);
if (v_isSharedCheck_442_ == 0)
{
lean_object* v_unused_443_; 
v_unused_443_ = lean_ctor_get(v_traceState_417_, 0);
lean_dec(v_unused_443_);
v___x_431_ = v_traceState_417_;
v_isShared_432_ = v_isSharedCheck_442_;
goto v_resetjp_430_;
}
else
{
lean_dec(v_traceState_417_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_442_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v___x_435_; 
v___x_433_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__3___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__3___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__3___redArg___closed__1);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_433_);
v___x_435_ = v___x_431_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_433_);
lean_ctor_set_uint64(v_reuseFailAlloc_441_, sizeof(void*)*1, v_tid_429_);
v___x_435_ = v_reuseFailAlloc_441_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_437_; 
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 4, v___x_435_);
v___x_437_ = v___x_427_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_env_418_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_nextMacroScope_419_);
lean_ctor_set(v_reuseFailAlloc_440_, 2, v_ngen_420_);
lean_ctor_set(v_reuseFailAlloc_440_, 3, v_auxDeclNGen_421_);
lean_ctor_set(v_reuseFailAlloc_440_, 4, v___x_435_);
lean_ctor_set(v_reuseFailAlloc_440_, 5, v_cache_422_);
lean_ctor_set(v_reuseFailAlloc_440_, 6, v_messages_423_);
lean_ctor_set(v_reuseFailAlloc_440_, 7, v_infoState_424_);
lean_ctor_set(v_reuseFailAlloc_440_, 8, v_snapshotTasks_425_);
v___x_437_ = v_reuseFailAlloc_440_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_st_ref_set(v___y_411_, v___x_437_);
v___x_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_439_, 0, v_traces_415_);
return v___x_439_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__3___redArg___boxed(lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__3___redArg(v___y_445_);
lean_dec(v___y_445_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__3(lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__3___redArg(v___y_451_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__3___boxed(lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__3(v___y_454_, v___y_455_, v___y_456_, v___y_457_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
return v_res_459_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__4(lean_object* v_opts_460_, lean_object* v_opt_461_){
_start:
{
lean_object* v_name_462_; lean_object* v_defValue_463_; lean_object* v_map_464_; lean_object* v___x_465_; 
v_name_462_ = lean_ctor_get(v_opt_461_, 0);
v_defValue_463_ = lean_ctor_get(v_opt_461_, 1);
v_map_464_ = lean_ctor_get(v_opts_460_, 0);
v___x_465_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_464_, v_name_462_);
if (lean_obj_tag(v___x_465_) == 0)
{
uint8_t v___x_466_; 
v___x_466_ = lean_unbox(v_defValue_463_);
return v___x_466_;
}
else
{
lean_object* v_val_467_; 
v_val_467_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_val_467_);
lean_dec_ref_known(v___x_465_, 1);
if (lean_obj_tag(v_val_467_) == 1)
{
uint8_t v_v_468_; 
v_v_468_ = lean_ctor_get_uint8(v_val_467_, 0);
lean_dec_ref_known(v_val_467_, 0);
return v_v_468_;
}
else
{
uint8_t v___x_469_; 
lean_dec(v_val_467_);
v___x_469_ = lean_unbox(v_defValue_463_);
return v___x_469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__4___boxed(lean_object* v_opts_470_, lean_object* v_opt_471_){
_start:
{
uint8_t v_res_472_; lean_object* v_r_473_; 
v_res_472_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__4(v_opts_470_, v_opt_471_);
lean_dec_ref(v_opt_471_);
lean_dec_ref(v_opts_470_);
v_r_473_ = lean_box(v_res_472_);
return v_r_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__7___redArg(lean_object* v_e_474_, lean_object* v___y_475_){
_start:
{
uint8_t v___x_477_; uint8_t v___x_478_; 
v___x_477_ = l_Lean_Expr_hasMVar(v_e_474_);
v___x_478_ = lean_bool_not(v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v_mctx_480_; lean_object* v___x_481_; lean_object* v_fst_482_; lean_object* v_snd_483_; lean_object* v___x_484_; lean_object* v_cache_485_; lean_object* v_zetaDeltaFVarIds_486_; lean_object* v_postponed_487_; lean_object* v_diag_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_497_; 
v___x_479_ = lean_st_ref_get(v___y_475_);
v_mctx_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc_ref(v_mctx_480_);
lean_dec(v___x_479_);
v___x_481_ = l_Lean_instantiateMVarsCore(v_mctx_480_, v_e_474_);
v_fst_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_fst_482_);
v_snd_483_ = lean_ctor_get(v___x_481_, 1);
lean_inc(v_snd_483_);
lean_dec_ref(v___x_481_);
v___x_484_ = lean_st_ref_take(v___y_475_);
v_cache_485_ = lean_ctor_get(v___x_484_, 1);
v_zetaDeltaFVarIds_486_ = lean_ctor_get(v___x_484_, 2);
v_postponed_487_ = lean_ctor_get(v___x_484_, 3);
v_diag_488_ = lean_ctor_get(v___x_484_, 4);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_497_ == 0)
{
lean_object* v_unused_498_; 
v_unused_498_ = lean_ctor_get(v___x_484_, 0);
lean_dec(v_unused_498_);
v___x_490_ = v___x_484_;
v_isShared_491_ = v_isSharedCheck_497_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_diag_488_);
lean_inc(v_postponed_487_);
lean_inc(v_zetaDeltaFVarIds_486_);
lean_inc(v_cache_485_);
lean_dec(v___x_484_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_497_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v_snd_483_);
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_snd_483_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_cache_485_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_zetaDeltaFVarIds_486_);
lean_ctor_set(v_reuseFailAlloc_496_, 3, v_postponed_487_);
lean_ctor_set(v_reuseFailAlloc_496_, 4, v_diag_488_);
v___x_493_ = v_reuseFailAlloc_496_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_st_ref_set(v___y_475_, v___x_493_);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v_fst_482_);
return v___x_495_;
}
}
}
else
{
lean_object* v___x_499_; 
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v_e_474_);
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__7___redArg___boxed(lean_object* v_e_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__7___redArg(v_e_500_, v___y_501_);
lean_dec(v___y_501_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__7(lean_object* v_e_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__7___redArg(v_e_504_, v___y_506_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__7___boxed(lean_object* v_e_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__7(v_e_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__0(lean_object* v_e_518_, uint8_t v___x_519_, lean_object* v_____r_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_526_ = lean_box(0);
v___x_527_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_527_, 0, v_e_518_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
lean_ctor_set_uint8(v___x_527_, sizeof(void*)*2, v___x_519_);
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
v___x_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__0___boxed(lean_object* v_e_530_, lean_object* v___x_531_, lean_object* v_____r_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
uint8_t v___x_106383__boxed_538_; lean_object* v_res_539_; 
v___x_106383__boxed_538_ = lean_unbox(v___x_531_);
v_res_539_ = l_Lean_Meta_rwMatcher___lam__0(v_e_530_, v___x_106383__boxed_538_, v_____r_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
return v_res_539_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__1(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__0));
v___x_542_ = l_Lean_stringToMessageData(v___x_541_);
return v___x_542_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__3(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__2));
v___x_545_ = l_Lean_stringToMessageData(v___x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__1(lean_object* v___x_546_, uint8_t v___y_547_, lean_object* v_e_548_, lean_object* v_x_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_555_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__1, &l_Lean_Meta_rwMatcher___lam__1___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__1);
v___x_556_ = l_Lean_MessageData_ofConstName(v___x_546_, v___y_547_);
v___x_557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__3, &l_Lean_Meta_rwMatcher___lam__1___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__3);
v___x_559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_557_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = l_Lean_indentExpr(v_e_548_);
v___x_561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_559_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__1___boxed(lean_object* v___x_563_, lean_object* v___y_564_, lean_object* v_e_565_, lean_object* v_x_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
uint8_t v___y_106425__boxed_572_; lean_object* v_res_573_; 
v___y_106425__boxed_572_ = lean_unbox(v___y_564_);
v_res_573_ = l_Lean_Meta_rwMatcher___lam__1(v___x_563_, v___y_106425__boxed_572_, v_e_565_, v_x_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec_ref(v_x_566_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__9(lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
if (lean_obj_tag(v_a_574_) == 0)
{
lean_object* v___x_576_; 
v___x_576_ = l_List_reverse___redArg(v_a_575_);
return v___x_576_;
}
else
{
lean_object* v_head_577_; lean_object* v_tail_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_587_; 
v_head_577_ = lean_ctor_get(v_a_574_, 0);
v_tail_578_ = lean_ctor_get(v_a_574_, 1);
v_isSharedCheck_587_ = !lean_is_exclusive(v_a_574_);
if (v_isSharedCheck_587_ == 0)
{
v___x_580_ = v_a_574_;
v_isShared_581_ = v_isSharedCheck_587_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_tail_578_);
lean_inc(v_head_577_);
lean_dec(v_a_574_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_587_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v___x_584_; 
v___x_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_582_, 0, v_head_577_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v_a_575_);
lean_ctor_set(v___x_580_, 0, v___x_582_);
v___x_584_ = v___x_580_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_582_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_a_575_);
v___x_584_ = v_reuseFailAlloc_586_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
v_a_574_ = v_tail_578_;
v_a_575_ = v___x_584_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(lean_object* v_keys_588_, lean_object* v_i_589_, lean_object* v_k_590_){
_start:
{
lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_591_ = lean_array_get_size(v_keys_588_);
v___x_592_ = lean_nat_dec_lt(v_i_589_, v___x_591_);
if (v___x_592_ == 0)
{
lean_dec(v_i_589_);
return v___x_592_;
}
else
{
lean_object* v_k_x27_593_; uint8_t v___x_594_; 
v_k_x27_593_ = lean_array_fget_borrowed(v_keys_588_, v_i_589_);
v___x_594_ = l_Lean_instBEqMVarId_beq(v_k_590_, v_k_x27_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_unsigned_to_nat(1u);
v___x_596_ = lean_nat_add(v_i_589_, v___x_595_);
lean_dec(v_i_589_);
v_i_589_ = v___x_596_;
goto _start;
}
else
{
lean_dec(v_i_589_);
return v___x_594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg___boxed(lean_object* v_keys_598_, lean_object* v_i_599_, lean_object* v_k_600_){
_start:
{
uint8_t v_res_601_; lean_object* v_r_602_; 
v_res_601_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(v_keys_598_, v_i_599_, v_k_600_);
lean_dec(v_k_600_);
lean_dec_ref(v_keys_598_);
v_r_602_ = lean_box(v_res_601_);
return v_r_602_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(lean_object* v_x_603_, size_t v_x_604_, lean_object* v_x_605_){
_start:
{
if (lean_obj_tag(v_x_603_) == 0)
{
lean_object* v_es_606_; lean_object* v___x_607_; size_t v___x_608_; size_t v___x_609_; lean_object* v_j_610_; lean_object* v___x_611_; 
v_es_606_ = lean_ctor_get(v_x_603_, 0);
v___x_607_ = lean_box(2);
v___x_608_ = ((size_t)31ULL);
v___x_609_ = lean_usize_land(v_x_604_, v___x_608_);
v_j_610_ = lean_usize_to_nat(v___x_609_);
v___x_611_ = lean_array_get_borrowed(v___x_607_, v_es_606_, v_j_610_);
lean_dec(v_j_610_);
switch(lean_obj_tag(v___x_611_))
{
case 0:
{
lean_object* v_key_612_; uint8_t v___x_613_; 
v_key_612_ = lean_ctor_get(v___x_611_, 0);
v___x_613_ = l_Lean_instBEqMVarId_beq(v_x_605_, v_key_612_);
return v___x_613_;
}
case 1:
{
lean_object* v_node_614_; size_t v___x_615_; size_t v___x_616_; 
v_node_614_ = lean_ctor_get(v___x_611_, 0);
v___x_615_ = ((size_t)5ULL);
v___x_616_ = lean_usize_shift_right(v_x_604_, v___x_615_);
v_x_603_ = v_node_614_;
v_x_604_ = v___x_616_;
goto _start;
}
default: 
{
uint8_t v___x_618_; 
v___x_618_ = 0;
return v___x_618_;
}
}
}
else
{
lean_object* v_ks_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v_ks_619_ = lean_ctor_get(v_x_603_, 0);
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(v_ks_619_, v___x_620_, v_x_605_);
return v___x_621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v_x_624_){
_start:
{
size_t v_x_106511__boxed_625_; uint8_t v_res_626_; lean_object* v_r_627_; 
v_x_106511__boxed_625_ = lean_unbox_usize(v_x_623_);
lean_dec(v_x_623_);
v_res_626_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_622_, v_x_106511__boxed_625_, v_x_624_);
lean_dec(v_x_624_);
lean_dec_ref(v_x_622_);
v_r_627_ = lean_box(v_res_626_);
return v_r_627_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(lean_object* v_x_628_, lean_object* v_x_629_){
_start:
{
uint64_t v___x_630_; size_t v___x_631_; uint8_t v___x_632_; 
v___x_630_ = l_Lean_instHashableMVarId_hash(v_x_629_);
v___x_631_ = lean_uint64_to_usize(v___x_630_);
v___x_632_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_628_, v___x_631_, v_x_629_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg___boxed(lean_object* v_x_633_, lean_object* v_x_634_){
_start:
{
uint8_t v_res_635_; lean_object* v_r_636_; 
v_res_635_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_x_633_, v_x_634_);
lean_dec(v_x_634_);
lean_dec_ref(v_x_633_);
v_r_636_ = lean_box(v_res_635_);
return v_r_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(lean_object* v_mvarId_637_, lean_object* v___y_638_){
_start:
{
lean_object* v___x_640_; lean_object* v_mctx_641_; lean_object* v_eAssignment_642_; uint8_t v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_640_ = lean_st_ref_get(v___y_638_);
v_mctx_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc_ref(v_mctx_641_);
lean_dec(v___x_640_);
v_eAssignment_642_ = lean_ctor_get(v_mctx_641_, 8);
lean_inc_ref(v_eAssignment_642_);
lean_dec_ref(v_mctx_641_);
v___x_643_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_eAssignment_642_, v_mvarId_637_);
lean_dec_ref(v_eAssignment_642_);
v___x_644_ = lean_box(v___x_643_);
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg___boxed(lean_object* v_mvarId_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_mvarId_646_, v___y_647_);
lean_dec(v___y_647_);
lean_dec(v_mvarId_646_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(lean_object* v_msgData_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___x_656_; lean_object* v_env_657_; lean_object* v___x_658_; lean_object* v_mctx_659_; lean_object* v_lctx_660_; lean_object* v_options_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_656_ = lean_st_ref_get(v___y_654_);
v_env_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc_ref(v_env_657_);
lean_dec(v___x_656_);
v___x_658_ = lean_st_ref_get(v___y_652_);
v_mctx_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc_ref(v_mctx_659_);
lean_dec(v___x_658_);
v_lctx_660_ = lean_ctor_get(v___y_651_, 2);
v_options_661_ = lean_ctor_get(v___y_653_, 2);
lean_inc_ref(v_options_661_);
lean_inc_ref(v_lctx_660_);
v___x_662_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_662_, 0, v_env_657_);
lean_ctor_set(v___x_662_, 1, v_mctx_659_);
lean_ctor_set(v___x_662_, 2, v_lctx_660_);
lean_ctor_set(v___x_662_, 3, v_options_661_);
v___x_663_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
lean_ctor_set(v___x_663_, 1, v_msgData_650_);
v___x_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3___boxed(lean_object* v_msgData_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msgData_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___redArg(lean_object* v_msg_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_ref_678_; lean_object* v___x_679_; lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_688_; 
v_ref_678_ = lean_ctor_get(v___y_675_, 5);
v___x_679_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
v_a_680_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_688_ == 0)
{
v___x_682_ = v___x_679_;
v_isShared_683_ = v_isSharedCheck_688_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_679_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_688_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_684_; lean_object* v___x_686_; 
lean_inc(v_ref_678_);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v_ref_678_);
lean_ctor_set(v___x_684_, 1, v_a_680_);
if (v_isShared_683_ == 0)
{
lean_ctor_set_tag(v___x_682_, 1);
lean_ctor_set(v___x_682_, 0, v___x_684_);
v___x_686_ = v___x_682_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___redArg___boxed(lean_object* v_msg_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___redArg(v_msg_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
return v_res_695_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__1(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__0));
v___x_698_ = l_Lean_stringToMessageData(v___x_697_);
return v___x_698_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__3(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__2));
v___x_701_ = l_Lean_stringToMessageData(v___x_700_);
return v___x_701_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__5(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__4));
v___x_704_ = l_Lean_stringToMessageData(v___x_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10(lean_object* v_as_705_, size_t v_sz_706_, size_t v_i_707_, lean_object* v_b_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_a_715_; uint8_t v___x_719_; 
v___x_719_ = lean_usize_dec_lt(v_i_707_, v_sz_706_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; 
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v_b_708_);
return v___x_720_;
}
else
{
lean_object* v_a_721_; lean_object* v___x_722_; 
v_a_721_ = lean_array_uget_borrowed(v_as_705_, v_i_707_);
v___x_722_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_a_721_, v___y_710_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_724_; lean_object* v___y_726_; lean_object* v___y_728_; lean_object* v___y_729_; uint8_t v___y_730_; lean_object* v___y_746_; lean_object* v___y_748_; lean_object* v___y_749_; uint8_t v___y_750_; lean_object* v___y_766_; uint8_t v___x_767_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_a_723_);
lean_dec_ref_known(v___x_722_, 1);
v___x_724_ = lean_box(0);
v___x_767_ = lean_unbox(v_a_723_);
lean_dec(v_a_723_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; 
lean_inc(v_a_721_);
v___x_768_ = l_Lean_MVarId_getType(v_a_721_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; uint8_t v___x_770_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc_n(v_a_769_, 2);
lean_dec_ref_known(v___x_768_, 1);
v___x_770_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_a_769_);
if (v___x_770_ == 0)
{
uint8_t v___x_771_; 
v___x_771_ = l_Lean_Expr_isEq(v_a_769_);
if (v___x_771_ == 0)
{
uint8_t v___x_772_; 
v___x_772_ = l_Lean_Expr_isHEq(v_a_769_);
lean_dec(v_a_769_);
if (v___x_772_ == 0)
{
v_a_715_ = v___x_724_;
goto v___jp_714_;
}
else
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_Meta_saveState___redArg(v___y_710_, v___y_712_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v___x_775_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_774_);
lean_dec_ref_known(v___x_773_, 1);
lean_inc(v_a_721_);
v___x_775_ = l_Lean_MVarId_assumption(v_a_721_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_dec(v_a_774_);
v___y_746_ = v___x_775_;
goto v___jp_745_;
}
else
{
lean_object* v_a_776_; uint8_t v___y_778_; uint8_t v___x_794_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
v___x_794_ = l_Lean_Exception_isInterrupt(v_a_776_);
if (v___x_794_ == 0)
{
uint8_t v___x_795_; 
v___x_795_ = l_Lean_Exception_isRuntime(v_a_776_);
v___y_778_ = v___x_795_;
goto v___jp_777_;
}
else
{
lean_dec(v_a_776_);
v___y_778_ = v___x_794_;
goto v___jp_777_;
}
v___jp_777_:
{
if (v___y_778_ == 0)
{
lean_object* v___x_779_; 
lean_dec_ref_known(v___x_775_, 1);
v___x_779_ = l_Lean_Meta_SavedState_restore___redArg(v_a_774_, v___y_710_, v___y_712_);
lean_dec(v_a_774_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v___x_780_; 
lean_dec_ref_known(v___x_779_, 1);
v___x_780_ = l_Lean_Meta_saveState___redArg(v___y_710_, v___y_712_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; lean_object* v___x_782_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_781_);
lean_dec_ref_known(v___x_780_, 1);
lean_inc(v_a_721_);
v___x_782_ = l_Lean_MVarId_hrefl(v_a_721_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_dec(v_a_781_);
v___y_746_ = v___x_782_;
goto v___jp_745_;
}
else
{
lean_object* v_a_783_; uint8_t v___x_784_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_783_);
v___x_784_ = l_Lean_Exception_isInterrupt(v_a_783_);
if (v___x_784_ == 0)
{
uint8_t v___x_785_; 
v___x_785_ = l_Lean_Exception_isRuntime(v_a_783_);
v___y_748_ = v___x_782_;
v___y_749_ = v_a_781_;
v___y_750_ = v___x_785_;
goto v___jp_747_;
}
else
{
lean_dec(v_a_783_);
v___y_748_ = v___x_782_;
v___y_749_ = v_a_781_;
v___y_750_ = v___x_784_;
goto v___jp_747_;
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
v_a_786_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_780_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_780_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
else
{
v___y_746_ = v___x_779_;
goto v___jp_745_;
}
}
else
{
lean_dec(v_a_774_);
v___y_746_ = v___x_775_;
goto v___jp_745_;
}
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
v_a_796_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_773_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_773_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
else
{
lean_object* v___x_804_; 
lean_dec(v_a_769_);
v___x_804_ = l_Lean_Meta_saveState___redArg(v___y_710_, v___y_712_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; lean_object* v___x_806_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_a_805_);
lean_dec_ref_known(v___x_804_, 1);
lean_inc(v_a_721_);
v___x_806_ = l_Lean_MVarId_assumption(v_a_721_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_dec(v_a_805_);
v___y_726_ = v___x_806_;
goto v___jp_725_;
}
else
{
lean_object* v_a_807_; uint8_t v___y_809_; uint8_t v___x_825_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_807_);
v___x_825_ = l_Lean_Exception_isInterrupt(v_a_807_);
if (v___x_825_ == 0)
{
uint8_t v___x_826_; 
v___x_826_ = l_Lean_Exception_isRuntime(v_a_807_);
v___y_809_ = v___x_826_;
goto v___jp_808_;
}
else
{
lean_dec(v_a_807_);
v___y_809_ = v___x_825_;
goto v___jp_808_;
}
v___jp_808_:
{
if (v___y_809_ == 0)
{
lean_object* v___x_810_; 
lean_dec_ref_known(v___x_806_, 1);
v___x_810_ = l_Lean_Meta_SavedState_restore___redArg(v_a_805_, v___y_710_, v___y_712_);
lean_dec(v_a_805_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v___x_811_; 
lean_dec_ref_known(v___x_810_, 1);
v___x_811_ = l_Lean_Meta_saveState___redArg(v___y_710_, v___y_712_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_813_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_812_);
lean_dec_ref_known(v___x_811_, 1);
lean_inc(v_a_721_);
v___x_813_ = l_Lean_MVarId_refl(v_a_721_, v___x_771_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_dec(v_a_812_);
v___y_726_ = v___x_813_;
goto v___jp_725_;
}
else
{
lean_object* v_a_814_; uint8_t v___x_815_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_a_814_);
v___x_815_ = l_Lean_Exception_isInterrupt(v_a_814_);
if (v___x_815_ == 0)
{
uint8_t v___x_816_; 
v___x_816_ = l_Lean_Exception_isRuntime(v_a_814_);
v___y_728_ = v_a_812_;
v___y_729_ = v___x_813_;
v___y_730_ = v___x_816_;
goto v___jp_727_;
}
else
{
lean_dec(v_a_814_);
v___y_728_ = v_a_812_;
v___y_729_ = v___x_813_;
v___y_730_ = v___x_815_;
goto v___jp_727_;
}
}
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
v_a_817_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_811_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_811_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
else
{
v___y_726_ = v___x_810_;
goto v___jp_725_;
}
}
else
{
lean_dec(v_a_805_);
v___y_726_ = v___x_806_;
goto v___jp_725_;
}
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
v_a_827_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_804_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_804_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
else
{
lean_object* v___x_835_; 
lean_dec(v_a_769_);
v___x_835_ = l_Lean_Meta_saveState___redArg(v___y_710_, v___y_712_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; lean_object* v___x_837_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_a_836_);
lean_dec_ref_known(v___x_835_, 1);
lean_inc(v_a_721_);
v___x_837_ = l_Lean_MVarId_assumption(v_a_721_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_dec(v_a_836_);
v___y_766_ = v___x_837_;
goto v___jp_765_;
}
else
{
lean_object* v_a_838_; uint8_t v___y_840_; uint8_t v___x_855_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
v___x_855_ = l_Lean_Exception_isInterrupt(v_a_838_);
if (v___x_855_ == 0)
{
uint8_t v___x_856_; 
v___x_856_ = l_Lean_Exception_isRuntime(v_a_838_);
v___y_840_ = v___x_856_;
goto v___jp_839_;
}
else
{
lean_dec(v_a_838_);
v___y_840_ = v___x_855_;
goto v___jp_839_;
}
v___jp_839_:
{
if (v___y_840_ == 0)
{
lean_object* v___x_841_; 
lean_dec_ref_known(v___x_837_, 1);
v___x_841_ = l_Lean_Meta_SavedState_restore___redArg(v_a_836_, v___y_710_, v___y_712_);
lean_dec(v_a_836_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_853_; 
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_853_ == 0)
{
lean_object* v_unused_854_; 
v_unused_854_ = lean_ctor_get(v___x_841_, 0);
lean_dec(v_unused_854_);
v___x_843_ = v___x_841_;
v_isShared_844_ = v_isSharedCheck_853_;
goto v_resetjp_842_;
}
else
{
lean_dec(v___x_841_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_853_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_845_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__5);
lean_inc(v_a_721_);
if (v_isShared_844_ == 0)
{
lean_ctor_set_tag(v___x_843_, 1);
lean_ctor_set(v___x_843_, 0, v_a_721_);
v___x_847_ = v___x_843_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_721_);
v___x_847_ = v_reuseFailAlloc_852_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_845_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
v___x_849_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__3);
v___x_850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_848_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___redArg(v___x_850_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
v___y_766_ = v___x_851_;
goto v___jp_765_;
}
}
}
else
{
v___y_766_ = v___x_841_;
goto v___jp_765_;
}
}
else
{
lean_dec(v_a_836_);
v___y_766_ = v___x_837_;
goto v___jp_765_;
}
}
}
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
v_a_857_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_835_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_835_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
v_a_865_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_768_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_768_);
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
else
{
v_a_715_ = v___x_724_;
goto v___jp_714_;
}
v___jp_725_:
{
if (lean_obj_tag(v___y_726_) == 0)
{
lean_dec_ref_known(v___y_726_, 1);
v_a_715_ = v___x_724_;
goto v___jp_714_;
}
else
{
return v___y_726_;
}
}
v___jp_727_:
{
if (v___y_730_ == 0)
{
lean_object* v___x_731_; 
lean_dec_ref(v___y_729_);
v___x_731_ = l_Lean_Meta_SavedState_restore___redArg(v___y_728_, v___y_710_, v___y_712_);
lean_dec_ref(v___y_728_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_743_; 
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_743_ == 0)
{
lean_object* v_unused_744_; 
v_unused_744_ = lean_ctor_get(v___x_731_, 0);
lean_dec(v_unused_744_);
v___x_733_ = v___x_731_;
v_isShared_734_ = v_isSharedCheck_743_;
goto v_resetjp_732_;
}
else
{
lean_dec(v___x_731_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_743_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v___x_737_; 
v___x_735_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__1);
lean_inc(v_a_721_);
if (v_isShared_734_ == 0)
{
lean_ctor_set_tag(v___x_733_, 1);
lean_ctor_set(v___x_733_, 0, v_a_721_);
v___x_737_ = v___x_733_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_721_);
v___x_737_ = v_reuseFailAlloc_742_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_735_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__3);
v___x_740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_738_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___redArg(v___x_740_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
v___y_726_ = v___x_741_;
goto v___jp_725_;
}
}
}
else
{
v___y_726_ = v___x_731_;
goto v___jp_725_;
}
}
else
{
lean_dec_ref(v___y_728_);
v___y_726_ = v___y_729_;
goto v___jp_725_;
}
}
v___jp_745_:
{
if (lean_obj_tag(v___y_746_) == 0)
{
lean_dec_ref_known(v___y_746_, 1);
v_a_715_ = v___x_724_;
goto v___jp_714_;
}
else
{
return v___y_746_;
}
}
v___jp_747_:
{
if (v___y_750_ == 0)
{
lean_object* v___x_751_; 
lean_dec_ref(v___y_748_);
v___x_751_ = l_Lean_Meta_SavedState_restore___redArg(v___y_749_, v___y_710_, v___y_712_);
lean_dec_ref(v___y_749_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_763_; 
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_763_ == 0)
{
lean_object* v_unused_764_; 
v_unused_764_ = lean_ctor_get(v___x_751_, 0);
lean_dec(v_unused_764_);
v___x_753_ = v___x_751_;
v_isShared_754_ = v_isSharedCheck_763_;
goto v_resetjp_752_;
}
else
{
lean_dec(v___x_751_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_763_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_755_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__1);
lean_inc(v_a_721_);
if (v_isShared_754_ == 0)
{
lean_ctor_set_tag(v___x_753_, 1);
lean_ctor_set(v___x_753_, 0, v_a_721_);
v___x_757_ = v___x_753_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_721_);
v___x_757_ = v_reuseFailAlloc_762_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_755_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__3);
v___x_760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_758_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___redArg(v___x_760_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
v___y_746_ = v___x_761_;
goto v___jp_745_;
}
}
}
else
{
v___y_746_ = v___x_751_;
goto v___jp_745_;
}
}
else
{
lean_dec_ref(v___y_749_);
v___y_746_ = v___y_748_;
goto v___jp_745_;
}
}
v___jp_765_:
{
if (lean_obj_tag(v___y_766_) == 0)
{
lean_dec_ref_known(v___y_766_, 1);
v_a_715_ = v___x_724_;
goto v___jp_714_;
}
else
{
return v___y_766_;
}
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
v_a_873_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_722_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_722_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
v___jp_714_:
{
size_t v___x_716_; size_t v___x_717_; 
v___x_716_ = ((size_t)1ULL);
v___x_717_ = lean_usize_add(v_i_707_, v___x_716_);
v_i_707_ = v___x_717_;
v_b_708_ = v_a_715_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___boxed(lean_object* v_as_881_, lean_object* v_sz_882_, lean_object* v_i_883_, lean_object* v_b_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
size_t v_sz_boxed_890_; size_t v_i_boxed_891_; lean_object* v_res_892_; 
v_sz_boxed_890_ = lean_unbox_usize(v_sz_882_);
lean_dec(v_sz_882_);
v_i_boxed_891_ = lean_unbox_usize(v_i_883_);
lean_dec(v_i_883_);
v_res_892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10(v_as_881_, v_sz_boxed_890_, v_i_boxed_891_, v_b_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec_ref(v_as_881_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__6(size_t v_sz_893_, size_t v_i_894_, lean_object* v_bs_895_){
_start:
{
uint8_t v___x_896_; 
v___x_896_ = lean_usize_dec_lt(v_i_894_, v_sz_893_);
if (v___x_896_ == 0)
{
return v_bs_895_;
}
else
{
lean_object* v_v_897_; lean_object* v___x_898_; lean_object* v_bs_x27_899_; lean_object* v___x_900_; size_t v___x_901_; size_t v___x_902_; lean_object* v___x_903_; 
v_v_897_ = lean_array_uget(v_bs_895_, v_i_894_);
v___x_898_ = lean_unsigned_to_nat(0u);
v_bs_x27_899_ = lean_array_uset(v_bs_895_, v_i_894_, v___x_898_);
v___x_900_ = l_Lean_Expr_mvarId_x21(v_v_897_);
lean_dec(v_v_897_);
v___x_901_ = ((size_t)1ULL);
v___x_902_ = lean_usize_add(v_i_894_, v___x_901_);
v___x_903_ = lean_array_uset(v_bs_x27_899_, v_i_894_, v___x_900_);
v_i_894_ = v___x_902_;
v_bs_895_ = v___x_903_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__6___boxed(lean_object* v_sz_905_, lean_object* v_i_906_, lean_object* v_bs_907_){
_start:
{
size_t v_sz_boxed_908_; size_t v_i_boxed_909_; lean_object* v_res_910_; 
v_sz_boxed_908_ = lean_unbox_usize(v_sz_905_);
lean_dec(v_sz_905_);
v_i_boxed_909_ = lean_unbox_usize(v_i_906_);
lean_dec(v_i_906_);
v_res_910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__6(v_sz_boxed_908_, v_i_boxed_909_, v_bs_907_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__11(lean_object* v_as_911_, size_t v_i_912_, size_t v_stop_913_, lean_object* v_b_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_a_921_; uint8_t v___x_925_; 
v___x_925_ = lean_usize_dec_eq(v_i_912_, v_stop_913_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; uint8_t v_a_928_; lean_object* v___x_930_; 
v___x_926_ = lean_array_uget_borrowed(v_as_911_, v_i_912_);
v___x_930_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v___x_926_, v___y_916_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; uint8_t v___x_932_; uint8_t v___x_933_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_a_931_);
lean_dec_ref_known(v___x_930_, 1);
v___x_932_ = lean_unbox(v_a_931_);
lean_dec(v_a_931_);
v___x_933_ = lean_bool_not(v___x_932_);
v_a_928_ = v___x_933_;
goto v___jp_927_;
}
else
{
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_934_; uint8_t v___x_935_; 
v_a_934_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_a_934_);
lean_dec_ref_known(v___x_930_, 1);
v___x_935_ = lean_unbox(v_a_934_);
lean_dec(v_a_934_);
v_a_928_ = v___x_935_;
goto v___jp_927_;
}
else
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
lean_dec_ref(v_b_914_);
v_a_936_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_930_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_930_);
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
v___jp_927_:
{
if (v_a_928_ == 0)
{
v_a_921_ = v_b_914_;
goto v___jp_920_;
}
else
{
lean_object* v___x_929_; 
lean_inc(v___x_926_);
v___x_929_ = lean_array_push(v_b_914_, v___x_926_);
v_a_921_ = v___x_929_;
goto v___jp_920_;
}
}
}
else
{
lean_object* v___x_944_; 
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v_b_914_);
return v___x_944_;
}
v___jp_920_:
{
size_t v___x_922_; size_t v___x_923_; 
v___x_922_ = ((size_t)1ULL);
v___x_923_ = lean_usize_add(v_i_912_, v___x_922_);
v_i_912_ = v___x_923_;
v_b_914_ = v_a_921_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__11___boxed(lean_object* v_as_945_, lean_object* v_i_946_, lean_object* v_stop_947_, lean_object* v_b_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
size_t v_i_boxed_954_; size_t v_stop_boxed_955_; lean_object* v_res_956_; 
v_i_boxed_954_ = lean_unbox_usize(v_i_946_);
lean_dec(v_i_946_);
v_stop_boxed_955_ = lean_unbox_usize(v_stop_947_);
lean_dec(v_stop_947_);
v_res_956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__11(v_as_945_, v_i_boxed_954_, v_stop_boxed_955_, v_b_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec_ref(v_as_945_);
return v_res_956_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__1(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__0));
v___x_959_ = l_Lean_stringToMessageData(v___x_958_);
return v___x_959_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__3(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__2));
v___x_962_ = l_Lean_stringToMessageData(v___x_961_);
return v___x_962_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__5(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__4));
v___x_965_ = l_Lean_stringToMessageData(v___x_964_);
return v___x_965_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__7(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__6));
v___x_968_ = l_Lean_stringToMessageData(v___x_967_);
return v___x_968_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__9(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__8));
v___x_971_ = l_Lean_stringToMessageData(v___x_970_);
return v___x_971_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__12(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__11));
v___x_976_ = l_Lean_stringToMessageData(v___x_975_);
return v___x_976_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__14(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__13));
v___x_979_ = l_Lean_stringToMessageData(v___x_978_);
return v___x_979_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__16(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__15));
v___x_982_ = l_Lean_stringToMessageData(v___x_981_);
return v___x_982_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__22(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__21));
v___x_991_ = l_Lean_stringToMessageData(v___x_990_);
return v___x_991_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__24(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__23));
v___x_994_ = l_Lean_stringToMessageData(v___x_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2(uint8_t v___x_995_, lean_object* v___x_996_, lean_object* v_fst_997_, lean_object* v___x_998_, uint8_t v___x_999_, lean_object* v_e_1000_, lean_object* v_snd_1001_, lean_object* v_____r_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v___y_1009_; lean_object* v_proof_1010_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; uint8_t v___y_1035_; lean_object* v___x_1047_; lean_object* v___y_1049_; uint8_t v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; uint8_t v___y_1069_; lean_object* v___y_1070_; lean_object* v_a_1071_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; uint8_t v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; size_t v_sz_1111_; size_t v___x_1112_; lean_object* v___x_1113_; lean_object* v___y_1115_; uint8_t v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; uint8_t v_fst_1142_; lean_object* v_fst_1143_; lean_object* v_snd_1144_; lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1047_ = l_Lean_mkAppN(v___x_996_, v_fst_997_);
v_sz_1111_ = lean_array_size(v_fst_997_);
v___x_1112_ = ((size_t)0ULL);
v___x_1113_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__6(v_sz_1111_, v___x_1112_, v_fst_997_);
v___x_1179_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1180_ = lean_unsigned_to_nat(4u);
v___x_1181_ = l_Lean_Expr_isAppOfArity(v_snd_1001_, v___x_1179_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; 
v___x_1182_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1183_ = lean_unsigned_to_nat(3u);
v___x_1184_ = l_Lean_Expr_isAppOfArity(v_snd_1001_, v___x_1182_, v___x_1183_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
lean_dec_ref(v___x_1113_);
lean_dec_ref(v___x_1047_);
lean_dec_ref(v_e_1000_);
v___x_1185_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1186_ = l_Lean_MessageData_ofConstName(v___x_998_, v___x_999_);
v___x_1187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1185_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v___x_1188_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___redArg(v___x_1189_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1190_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1190_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
else
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1199_ = l_Lean_Expr_appFn_x21(v_snd_1001_);
v___x_1200_ = l_Lean_Expr_appArg_x21(v___x_1199_);
lean_dec_ref(v___x_1199_);
v___x_1201_ = l_Lean_Expr_appArg_x21(v_snd_1001_);
v_fst_1142_ = v___x_999_;
v_fst_1143_ = v___x_1200_;
v_snd_1144_ = v___x_1201_;
goto v___jp_1141_;
}
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1202_ = l_Lean_Expr_appFn_x21(v_snd_1001_);
v___x_1203_ = l_Lean_Expr_appFn_x21(v___x_1202_);
lean_dec_ref(v___x_1202_);
v___x_1204_ = l_Lean_Expr_appArg_x21(v___x_1203_);
lean_dec_ref(v___x_1203_);
v___x_1205_ = l_Lean_Expr_appArg_x21(v_snd_1001_);
v_fst_1142_ = v___x_995_;
v_fst_1143_ = v___x_1204_;
v_snd_1144_ = v___x_1205_;
goto v___jp_1141_;
}
v___jp_1008_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1011_, 0, v_proof_1010_);
v___x_1012_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1012_, 0, v___y_1009_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
lean_ctor_set_uint8(v___x_1012_, sizeof(void*)*2, v___x_995_);
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
return v___x_1013_;
}
v___jp_1014_:
{
if (lean_obj_tag(v___y_1016_) == 0)
{
lean_object* v_a_1017_; 
v_a_1017_ = lean_ctor_get(v___y_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___y_1016_, 1);
v___y_1009_ = v___y_1015_;
v_proof_1010_ = v_a_1017_;
goto v___jp_1008_;
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec_ref(v___y_1015_);
v_a_1018_ = lean_ctor_get(v___y_1016_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___y_1016_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___y_1016_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___y_1016_);
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
v___jp_1026_:
{
if (v___y_1035_ == 0)
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
lean_dec_ref(v___y_1033_);
v___x_1036_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1037_ = l_Lean_MessageData_ofExpr(v___y_1032_);
v___x_1038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = l_Lean_Exception_toMessageData(v___y_1030_);
v___x_1042_ = l_Lean_indentD(v___x_1041_);
v___x_1043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1040_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1043_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___redArg(v___x_1045_, v___y_1029_, v___y_1031_, v___y_1027_, v___y_1028_);
v___y_1015_ = v___y_1034_;
v___y_1016_ = v___x_1046_;
goto v___jp_1014_;
}
else
{
lean_dec_ref(v___y_1032_);
lean_dec_ref(v___y_1030_);
v___y_1015_ = v___y_1034_;
v___y_1016_ = v___y_1033_;
goto v___jp_1014_;
}
}
v___jp_1048_:
{
lean_object* v___x_1055_; lean_object* v_a_1056_; lean_object* v___x_1057_; 
v___x_1055_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__7___redArg(v___y_1049_, v___y_1052_);
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_a_1056_);
lean_dec_ref(v___x_1055_);
v___x_1057_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__7___redArg(v___x_1047_, v___y_1052_);
if (v___y_1050_ == 0)
{
lean_object* v_a_1058_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1058_);
lean_dec_ref(v___x_1057_);
v___y_1009_ = v_a_1056_;
v_proof_1010_ = v_a_1058_;
goto v___jp_1008_;
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1060_; 
v_a_1059_ = lean_ctor_get(v___x_1057_, 0);
lean_inc_n(v_a_1059_, 2);
lean_dec_ref(v___x_1057_);
v___x_1060_ = l_Lean_Meta_mkEqOfHEq(v_a_1059_, v___x_995_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_dec(v_a_1059_);
v___y_1015_ = v_a_1056_;
v___y_1016_ = v___x_1060_;
goto v___jp_1014_;
}
else
{
lean_object* v_a_1061_; uint8_t v___x_1062_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_a_1061_);
v___x_1062_ = l_Lean_Exception_isInterrupt(v_a_1061_);
if (v___x_1062_ == 0)
{
uint8_t v___x_1063_; 
lean_inc(v_a_1061_);
v___x_1063_ = l_Lean_Exception_isRuntime(v_a_1061_);
v___y_1027_ = v___y_1053_;
v___y_1028_ = v___y_1054_;
v___y_1029_ = v___y_1051_;
v___y_1030_ = v_a_1061_;
v___y_1031_ = v___y_1052_;
v___y_1032_ = v_a_1059_;
v___y_1033_ = v___x_1060_;
v___y_1034_ = v_a_1056_;
v___y_1035_ = v___x_1063_;
goto v___jp_1026_;
}
else
{
v___y_1027_ = v___y_1053_;
v___y_1028_ = v___y_1054_;
v___y_1029_ = v___y_1051_;
v___y_1030_ = v_a_1061_;
v___y_1031_ = v___y_1052_;
v___y_1032_ = v_a_1059_;
v___y_1033_ = v___x_1060_;
v___y_1034_ = v_a_1056_;
v___y_1035_ = v___x_1062_;
goto v___jp_1026_;
}
}
}
}
v___jp_1064_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1072_ = lean_array_get_size(v_a_1071_);
v___x_1073_ = lean_unsigned_to_nat(0u);
v___x_1074_ = lean_nat_dec_eq(v___x_1072_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
lean_dec_ref(v___y_1066_);
lean_dec_ref(v___x_1047_);
v___x_1075_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1076_ = l_Lean_MessageData_ofConstName(v___x_998_, v___x_999_);
v___x_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_array_to_list(v_a_1071_);
v___x_1081_ = lean_box(0);
v___x_1082_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__9(v___x_1080_, v___x_1081_);
v___x_1083_ = l_Lean_MessageData_ofList(v___x_1082_);
v___x_1084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1079_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___redArg(v___x_1084_, v___y_1068_, v___y_1065_, v___y_1070_, v___y_1067_);
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1085_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1085_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
else
{
lean_dec_ref(v_a_1071_);
lean_dec(v___x_998_);
v___y_1049_ = v___y_1066_;
v___y_1050_ = v___y_1069_;
v___y_1051_ = v___y_1068_;
v___y_1052_ = v___y_1065_;
v___y_1053_ = v___y_1070_;
v___y_1054_ = v___y_1067_;
goto v___jp_1048_;
}
}
v___jp_1094_:
{
if (lean_obj_tag(v___y_1101_) == 0)
{
lean_object* v_a_1102_; 
v_a_1102_ = lean_ctor_get(v___y_1101_, 0);
lean_inc(v_a_1102_);
lean_dec_ref_known(v___y_1101_, 1);
v___y_1065_ = v___y_1095_;
v___y_1066_ = v___y_1097_;
v___y_1067_ = v___y_1096_;
v___y_1068_ = v___y_1098_;
v___y_1069_ = v___y_1099_;
v___y_1070_ = v___y_1100_;
v_a_1071_ = v_a_1102_;
goto v___jp_1064_;
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_dec_ref(v___y_1097_);
lean_dec_ref(v___x_1047_);
lean_dec(v___x_998_);
v_a_1103_ = lean_ctor_get(v___y_1101_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___y_1101_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___y_1101_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___y_1101_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
v___jp_1114_:
{
lean_object* v___x_1121_; size_t v_sz_1122_; lean_object* v___x_1123_; 
v___x_1121_ = lean_box(0);
v_sz_1122_ = lean_array_size(v___x_1113_);
v___x_1123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10(v___x_1113_, v_sz_1122_, v___x_1112_, v___x_1121_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; uint8_t v___x_1127_; 
lean_dec_ref_known(v___x_1123_, 1);
v___x_1124_ = lean_unsigned_to_nat(0u);
v___x_1125_ = lean_array_get_size(v___x_1113_);
v___x_1126_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1127_ = lean_nat_dec_lt(v___x_1124_, v___x_1125_);
if (v___x_1127_ == 0)
{
lean_dec_ref(v___x_1113_);
v___y_1065_ = v___y_1118_;
v___y_1066_ = v___y_1115_;
v___y_1067_ = v___y_1120_;
v___y_1068_ = v___y_1117_;
v___y_1069_ = v___y_1116_;
v___y_1070_ = v___y_1119_;
v_a_1071_ = v___x_1126_;
goto v___jp_1064_;
}
else
{
uint8_t v___x_1128_; 
v___x_1128_ = lean_nat_dec_le(v___x_1125_, v___x_1125_);
if (v___x_1128_ == 0)
{
if (v___x_1127_ == 0)
{
lean_dec_ref(v___x_1113_);
v___y_1065_ = v___y_1118_;
v___y_1066_ = v___y_1115_;
v___y_1067_ = v___y_1120_;
v___y_1068_ = v___y_1117_;
v___y_1069_ = v___y_1116_;
v___y_1070_ = v___y_1119_;
v_a_1071_ = v___x_1126_;
goto v___jp_1064_;
}
else
{
size_t v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = lean_usize_of_nat(v___x_1125_);
v___x_1130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__11(v___x_1113_, v___x_1112_, v___x_1129_, v___x_1126_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
lean_dec_ref(v___x_1113_);
v___y_1095_ = v___y_1118_;
v___y_1096_ = v___y_1120_;
v___y_1097_ = v___y_1115_;
v___y_1098_ = v___y_1117_;
v___y_1099_ = v___y_1116_;
v___y_1100_ = v___y_1119_;
v___y_1101_ = v___x_1130_;
goto v___jp_1094_;
}
}
else
{
size_t v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_usize_of_nat(v___x_1125_);
v___x_1132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__11(v___x_1113_, v___x_1112_, v___x_1131_, v___x_1126_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
lean_dec_ref(v___x_1113_);
v___y_1095_ = v___y_1118_;
v___y_1096_ = v___y_1120_;
v___y_1097_ = v___y_1115_;
v___y_1098_ = v___y_1117_;
v___y_1099_ = v___y_1116_;
v___y_1100_ = v___y_1119_;
v___y_1101_ = v___x_1132_;
goto v___jp_1094_;
}
}
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec_ref(v___y_1115_);
lean_dec_ref(v___x_1113_);
lean_dec_ref(v___x_1047_);
lean_dec(v___x_998_);
v_a_1133_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1123_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1123_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
v___jp_1141_:
{
lean_object* v___x_1145_; 
lean_inc_ref(v_fst_1143_);
lean_inc_ref(v_e_1000_);
v___x_1145_ = l_Lean_Meta_isExprDefEq(v_e_1000_, v_fst_1143_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; uint8_t v___x_1147_; uint8_t v___x_1148_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref_known(v___x_1145_, 1);
v___x_1147_ = lean_unbox(v_a_1146_);
lean_dec(v_a_1146_);
v___x_1148_ = lean_bool_not(v___x_1147_);
if (v___x_1148_ == 0)
{
lean_dec_ref(v_fst_1143_);
lean_dec_ref(v_e_1000_);
v___y_1115_ = v_snd_1144_;
v___y_1116_ = v_fst_1142_;
v___y_1117_ = v___y_1003_;
v___y_1118_ = v___y_1004_;
v___y_1119_ = v___y_1005_;
v___y_1120_ = v___y_1006_;
goto v___jp_1114_;
}
else
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
lean_dec_ref(v_snd_1144_);
lean_dec_ref(v___x_1113_);
lean_dec_ref(v___x_1047_);
v___x_1149_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1150_ = l_Lean_MessageData_ofExpr(v_fst_1143_);
v___x_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1149_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1151_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = l_Lean_MessageData_ofConstName(v___x_998_, v___x_999_);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = l_Lean_MessageData_ofExpr(v_e_1000_);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__3);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1159_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v___x_1162_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___redArg(v___x_1161_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1162_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1162_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
lean_dec_ref(v_snd_1144_);
lean_dec_ref(v_fst_1143_);
lean_dec_ref(v___x_1113_);
lean_dec_ref(v___x_1047_);
lean_dec_ref(v_e_1000_);
lean_dec(v___x_998_);
v_a_1171_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1145_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1145_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2___boxed(lean_object* v___x_1206_, lean_object* v___x_1207_, lean_object* v_fst_1208_, lean_object* v___x_1209_, lean_object* v___x_1210_, lean_object* v_e_1211_, lean_object* v_snd_1212_, lean_object* v_____r_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
uint8_t v___x_107200__boxed_1219_; uint8_t v___x_107204__boxed_1220_; lean_object* v_res_1221_; 
v___x_107200__boxed_1219_ = lean_unbox(v___x_1206_);
v___x_107204__boxed_1220_ = lean_unbox(v___x_1210_);
v_res_1221_ = l_Lean_Meta_rwMatcher___lam__2(v___x_107200__boxed_1219_, v___x_1207_, v_fst_1208_, v___x_1209_, v___x_107204__boxed_1220_, v_e_1211_, v_snd_1212_, v_____r_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec_ref(v_snd_1212_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3(uint8_t v___x_1222_, lean_object* v___x_1223_, lean_object* v_fst_1224_, lean_object* v___x_1225_, uint8_t v___x_1226_, lean_object* v_e_1227_, lean_object* v_snd_1228_, lean_object* v_____r_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v___y_1236_; lean_object* v_proof_1237_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; uint8_t v___y_1262_; lean_object* v___x_1274_; lean_object* v___y_1276_; uint8_t v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1292_; lean_object* v___y_1293_; uint8_t v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v_a_1298_; lean_object* v___y_1322_; lean_object* v___y_1323_; uint8_t v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; size_t v_sz_1338_; size_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___y_1342_; uint8_t v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; uint8_t v_fst_1369_; lean_object* v_fst_1370_; lean_object* v_snd_1371_; lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v___x_1274_ = l_Lean_mkAppN(v___x_1223_, v_fst_1224_);
v_sz_1338_ = lean_array_size(v_fst_1224_);
v___x_1339_ = ((size_t)0ULL);
v___x_1340_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__6(v_sz_1338_, v___x_1339_, v_fst_1224_);
v___x_1406_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1407_ = lean_unsigned_to_nat(4u);
v___x_1408_ = l_Lean_Expr_isAppOfArity(v_snd_1228_, v___x_1406_, v___x_1407_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1409_; lean_object* v___x_1410_; uint8_t v___x_1411_; 
v___x_1409_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1410_ = lean_unsigned_to_nat(3u);
v___x_1411_ = l_Lean_Expr_isAppOfArity(v_snd_1228_, v___x_1409_, v___x_1410_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec_ref(v___x_1340_);
lean_dec_ref(v___x_1274_);
lean_dec_ref(v_e_1227_);
v___x_1412_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1413_ = l_Lean_MessageData_ofConstName(v___x_1225_, v___x_1226_);
v___x_1414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1412_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
v___x_1415_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1414_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
v___x_1417_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___redArg(v___x_1416_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1417_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1417_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1426_ = l_Lean_Expr_appFn_x21(v_snd_1228_);
v___x_1427_ = l_Lean_Expr_appArg_x21(v___x_1426_);
lean_dec_ref(v___x_1426_);
v___x_1428_ = l_Lean_Expr_appArg_x21(v_snd_1228_);
v_fst_1369_ = v___x_1226_;
v_fst_1370_ = v___x_1427_;
v_snd_1371_ = v___x_1428_;
goto v___jp_1368_;
}
}
else
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1429_ = l_Lean_Expr_appFn_x21(v_snd_1228_);
v___x_1430_ = l_Lean_Expr_appFn_x21(v___x_1429_);
lean_dec_ref(v___x_1429_);
v___x_1431_ = l_Lean_Expr_appArg_x21(v___x_1430_);
lean_dec_ref(v___x_1430_);
v___x_1432_ = l_Lean_Expr_appArg_x21(v_snd_1228_);
v_fst_1369_ = v___x_1222_;
v_fst_1370_ = v___x_1431_;
v_snd_1371_ = v___x_1432_;
goto v___jp_1368_;
}
v___jp_1235_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1238_, 0, v_proof_1237_);
v___x_1239_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1239_, 0, v___y_1236_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
lean_ctor_set_uint8(v___x_1239_, sizeof(void*)*2, v___x_1222_);
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
return v___x_1240_;
}
v___jp_1241_:
{
if (lean_obj_tag(v___y_1243_) == 0)
{
lean_object* v_a_1244_; 
v_a_1244_ = lean_ctor_get(v___y_1243_, 0);
lean_inc(v_a_1244_);
lean_dec_ref_known(v___y_1243_, 1);
v___y_1236_ = v___y_1242_;
v_proof_1237_ = v_a_1244_;
goto v___jp_1235_;
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec_ref(v___y_1242_);
v_a_1245_ = lean_ctor_get(v___y_1243_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___y_1243_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___y_1243_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___y_1243_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
v___jp_1253_:
{
if (v___y_1262_ == 0)
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
lean_dec_ref(v___y_1256_);
v___x_1263_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1264_ = l_Lean_MessageData_ofExpr(v___y_1257_);
v___x_1265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1263_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
v___x_1266_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1265_);
lean_ctor_set(v___x_1267_, 1, v___x_1266_);
v___x_1268_ = l_Lean_Exception_toMessageData(v___y_1259_);
v___x_1269_ = l_Lean_indentD(v___x_1268_);
v___x_1270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1267_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
v___x_1271_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1270_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
v___x_1273_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___redArg(v___x_1272_, v___y_1260_, v___y_1258_, v___y_1255_, v___y_1261_);
v___y_1242_ = v___y_1254_;
v___y_1243_ = v___x_1273_;
goto v___jp_1241_;
}
else
{
lean_dec_ref(v___y_1259_);
lean_dec_ref(v___y_1257_);
v___y_1242_ = v___y_1254_;
v___y_1243_ = v___y_1256_;
goto v___jp_1241_;
}
}
v___jp_1275_:
{
lean_object* v___x_1282_; lean_object* v_a_1283_; lean_object* v___x_1284_; 
v___x_1282_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__7___redArg(v___y_1276_, v___y_1279_);
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
lean_dec_ref(v___x_1282_);
v___x_1284_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__7___redArg(v___x_1274_, v___y_1279_);
if (v___y_1277_ == 0)
{
lean_object* v_a_1285_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec_ref(v___x_1284_);
v___y_1236_ = v_a_1283_;
v_proof_1237_ = v_a_1285_;
goto v___jp_1235_;
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1287_; 
v_a_1286_ = lean_ctor_get(v___x_1284_, 0);
lean_inc_n(v_a_1286_, 2);
lean_dec_ref(v___x_1284_);
v___x_1287_ = l_Lean_Meta_mkEqOfHEq(v_a_1286_, v___x_1222_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_dec(v_a_1286_);
v___y_1242_ = v_a_1283_;
v___y_1243_ = v___x_1287_;
goto v___jp_1241_;
}
else
{
lean_object* v_a_1288_; uint8_t v___x_1289_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
v___x_1289_ = l_Lean_Exception_isInterrupt(v_a_1288_);
if (v___x_1289_ == 0)
{
uint8_t v___x_1290_; 
lean_inc(v_a_1288_);
v___x_1290_ = l_Lean_Exception_isRuntime(v_a_1288_);
v___y_1254_ = v_a_1283_;
v___y_1255_ = v___y_1280_;
v___y_1256_ = v___x_1287_;
v___y_1257_ = v_a_1286_;
v___y_1258_ = v___y_1279_;
v___y_1259_ = v_a_1288_;
v___y_1260_ = v___y_1278_;
v___y_1261_ = v___y_1281_;
v___y_1262_ = v___x_1290_;
goto v___jp_1253_;
}
else
{
v___y_1254_ = v_a_1283_;
v___y_1255_ = v___y_1280_;
v___y_1256_ = v___x_1287_;
v___y_1257_ = v_a_1286_;
v___y_1258_ = v___y_1279_;
v___y_1259_ = v_a_1288_;
v___y_1260_ = v___y_1278_;
v___y_1261_ = v___y_1281_;
v___y_1262_ = v___x_1289_;
goto v___jp_1253_;
}
}
}
}
v___jp_1291_:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v___x_1299_ = lean_array_get_size(v_a_1298_);
v___x_1300_ = lean_unsigned_to_nat(0u);
v___x_1301_ = lean_nat_dec_eq(v___x_1299_, v___x_1300_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_dec_ref(v___y_1293_);
lean_dec_ref(v___x_1274_);
v___x_1302_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1303_ = l_Lean_MessageData_ofConstName(v___x_1225_, v___x_1226_);
v___x_1304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1302_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
v___x_1305_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1304_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
v___x_1307_ = lean_array_to_list(v_a_1298_);
v___x_1308_ = lean_box(0);
v___x_1309_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__9(v___x_1307_, v___x_1308_);
v___x_1310_ = l_Lean_MessageData_ofList(v___x_1309_);
v___x_1311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1306_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
v___x_1312_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___redArg(v___x_1311_, v___y_1295_, v___y_1297_, v___y_1292_, v___y_1296_);
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1312_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1312_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
else
{
lean_dec_ref(v_a_1298_);
lean_dec(v___x_1225_);
v___y_1276_ = v___y_1293_;
v___y_1277_ = v___y_1294_;
v___y_1278_ = v___y_1295_;
v___y_1279_ = v___y_1297_;
v___y_1280_ = v___y_1292_;
v___y_1281_ = v___y_1296_;
goto v___jp_1275_;
}
}
v___jp_1321_:
{
if (lean_obj_tag(v___y_1328_) == 0)
{
lean_object* v_a_1329_; 
v_a_1329_ = lean_ctor_get(v___y_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref_known(v___y_1328_, 1);
v___y_1292_ = v___y_1322_;
v___y_1293_ = v___y_1323_;
v___y_1294_ = v___y_1324_;
v___y_1295_ = v___y_1325_;
v___y_1296_ = v___y_1326_;
v___y_1297_ = v___y_1327_;
v_a_1298_ = v_a_1329_;
goto v___jp_1291_;
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_dec_ref(v___y_1323_);
lean_dec_ref(v___x_1274_);
lean_dec(v___x_1225_);
v_a_1330_ = lean_ctor_get(v___y_1328_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___y_1328_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___y_1328_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___y_1328_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
v___jp_1341_:
{
lean_object* v___x_1348_; size_t v_sz_1349_; lean_object* v___x_1350_; 
v___x_1348_ = lean_box(0);
v_sz_1349_ = lean_array_size(v___x_1340_);
v___x_1350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10(v___x_1340_, v_sz_1349_, v___x_1339_, v___x_1348_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; 
lean_dec_ref_known(v___x_1350_, 1);
v___x_1351_ = lean_unsigned_to_nat(0u);
v___x_1352_ = lean_array_get_size(v___x_1340_);
v___x_1353_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1354_ = lean_nat_dec_lt(v___x_1351_, v___x_1352_);
if (v___x_1354_ == 0)
{
lean_dec_ref(v___x_1340_);
v___y_1292_ = v___y_1346_;
v___y_1293_ = v___y_1342_;
v___y_1294_ = v___y_1343_;
v___y_1295_ = v___y_1344_;
v___y_1296_ = v___y_1347_;
v___y_1297_ = v___y_1345_;
v_a_1298_ = v___x_1353_;
goto v___jp_1291_;
}
else
{
uint8_t v___x_1355_; 
v___x_1355_ = lean_nat_dec_le(v___x_1352_, v___x_1352_);
if (v___x_1355_ == 0)
{
if (v___x_1354_ == 0)
{
lean_dec_ref(v___x_1340_);
v___y_1292_ = v___y_1346_;
v___y_1293_ = v___y_1342_;
v___y_1294_ = v___y_1343_;
v___y_1295_ = v___y_1344_;
v___y_1296_ = v___y_1347_;
v___y_1297_ = v___y_1345_;
v_a_1298_ = v___x_1353_;
goto v___jp_1291_;
}
else
{
size_t v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_usize_of_nat(v___x_1352_);
v___x_1357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__11(v___x_1340_, v___x_1339_, v___x_1356_, v___x_1353_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
lean_dec_ref(v___x_1340_);
v___y_1322_ = v___y_1346_;
v___y_1323_ = v___y_1342_;
v___y_1324_ = v___y_1343_;
v___y_1325_ = v___y_1344_;
v___y_1326_ = v___y_1347_;
v___y_1327_ = v___y_1345_;
v___y_1328_ = v___x_1357_;
goto v___jp_1321_;
}
}
else
{
size_t v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = lean_usize_of_nat(v___x_1352_);
v___x_1359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__11(v___x_1340_, v___x_1339_, v___x_1358_, v___x_1353_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
lean_dec_ref(v___x_1340_);
v___y_1322_ = v___y_1346_;
v___y_1323_ = v___y_1342_;
v___y_1324_ = v___y_1343_;
v___y_1325_ = v___y_1344_;
v___y_1326_ = v___y_1347_;
v___y_1327_ = v___y_1345_;
v___y_1328_ = v___x_1359_;
goto v___jp_1321_;
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec_ref(v___y_1342_);
lean_dec_ref(v___x_1340_);
lean_dec_ref(v___x_1274_);
lean_dec(v___x_1225_);
v_a_1360_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1350_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1350_);
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
v___jp_1368_:
{
lean_object* v___x_1372_; 
lean_inc_ref(v_fst_1370_);
lean_inc_ref(v_e_1227_);
v___x_1372_ = l_Lean_Meta_isExprDefEq(v_e_1227_, v_fst_1370_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; uint8_t v___x_1374_; uint8_t v___x_1375_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1373_);
lean_dec_ref_known(v___x_1372_, 1);
v___x_1374_ = lean_unbox(v_a_1373_);
lean_dec(v_a_1373_);
v___x_1375_ = lean_bool_not(v___x_1374_);
if (v___x_1375_ == 0)
{
lean_dec_ref(v_fst_1370_);
lean_dec_ref(v_e_1227_);
v___y_1342_ = v_snd_1371_;
v___y_1343_ = v_fst_1369_;
v___y_1344_ = v___y_1230_;
v___y_1345_ = v___y_1231_;
v___y_1346_ = v___y_1232_;
v___y_1347_ = v___y_1233_;
goto v___jp_1341_;
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_dec_ref(v_snd_1371_);
lean_dec_ref(v___x_1340_);
lean_dec_ref(v___x_1274_);
v___x_1376_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1377_ = l_Lean_MessageData_ofExpr(v_fst_1370_);
v___x_1378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1376_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
v___x_1379_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1378_);
lean_ctor_set(v___x_1380_, 1, v___x_1379_);
v___x_1381_ = l_Lean_MessageData_ofConstName(v___x_1225_, v___x_1226_);
v___x_1382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1380_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
v___x_1383_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1382_);
lean_ctor_set(v___x_1384_, 1, v___x_1383_);
v___x_1385_ = l_Lean_MessageData_ofExpr(v_e_1227_);
v___x_1386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1384_);
lean_ctor_set(v___x_1386_, 1, v___x_1385_);
v___x_1387_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__3);
v___x_1388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1386_);
lean_ctor_set(v___x_1388_, 1, v___x_1387_);
v___x_1389_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___redArg(v___x_1388_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1389_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1389_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_dec_ref(v_snd_1371_);
lean_dec_ref(v_fst_1370_);
lean_dec_ref(v___x_1340_);
lean_dec_ref(v___x_1274_);
lean_dec_ref(v_e_1227_);
lean_dec(v___x_1225_);
v_a_1398_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1372_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1372_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3___boxed(lean_object* v___x_1433_, lean_object* v___x_1434_, lean_object* v_fst_1435_, lean_object* v___x_1436_, lean_object* v___x_1437_, lean_object* v_e_1438_, lean_object* v_snd_1439_, lean_object* v_____r_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
uint8_t v___x_107712__boxed_1446_; uint8_t v___x_107716__boxed_1447_; lean_object* v_res_1448_; 
v___x_107712__boxed_1446_ = lean_unbox(v___x_1433_);
v___x_107716__boxed_1447_ = lean_unbox(v___x_1437_);
v_res_1448_ = l_Lean_Meta_rwMatcher___lam__3(v___x_107712__boxed_1446_, v___x_1434_, v_fst_1435_, v___x_1436_, v___x_107716__boxed_1447_, v_e_1438_, v_snd_1439_, v_____r_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec_ref(v_snd_1439_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4(uint8_t v___x_1449_, lean_object* v___x_1450_, lean_object* v_fst_1451_, lean_object* v___x_1452_, uint8_t v___x_1453_, lean_object* v_e_1454_, lean_object* v_snd_1455_, lean_object* v_____r_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v___y_1463_; lean_object* v_proof_1464_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; uint8_t v___y_1489_; lean_object* v___x_1501_; lean_object* v___y_1503_; uint8_t v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; uint8_t v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v_a_1525_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; uint8_t v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; size_t v_sz_1565_; size_t v___x_1566_; lean_object* v___x_1567_; lean_object* v___y_1569_; uint8_t v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; uint8_t v_fst_1596_; lean_object* v_fst_1597_; lean_object* v_snd_1598_; lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v___x_1501_ = l_Lean_mkAppN(v___x_1450_, v_fst_1451_);
v_sz_1565_ = lean_array_size(v_fst_1451_);
v___x_1566_ = ((size_t)0ULL);
v___x_1567_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__6(v_sz_1565_, v___x_1566_, v_fst_1451_);
v___x_1633_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1634_ = lean_unsigned_to_nat(4u);
v___x_1635_ = l_Lean_Expr_isAppOfArity(v_snd_1455_, v___x_1633_, v___x_1634_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1636_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1637_ = lean_unsigned_to_nat(3u);
v___x_1638_ = l_Lean_Expr_isAppOfArity(v_snd_1455_, v___x_1636_, v___x_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
lean_dec_ref(v___x_1567_);
lean_dec_ref(v___x_1501_);
lean_dec_ref(v_e_1454_);
v___x_1639_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1640_ = l_Lean_MessageData_ofConstName(v___x_1452_, v___x_1453_);
v___x_1641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1639_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v___x_1642_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1641_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___redArg(v___x_1643_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1644_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1644_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
else
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1653_ = l_Lean_Expr_appFn_x21(v_snd_1455_);
v___x_1654_ = l_Lean_Expr_appArg_x21(v___x_1653_);
lean_dec_ref(v___x_1653_);
v___x_1655_ = l_Lean_Expr_appArg_x21(v_snd_1455_);
v_fst_1596_ = v___x_1453_;
v_fst_1597_ = v___x_1654_;
v_snd_1598_ = v___x_1655_;
goto v___jp_1595_;
}
}
else
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1656_ = l_Lean_Expr_appFn_x21(v_snd_1455_);
v___x_1657_ = l_Lean_Expr_appFn_x21(v___x_1656_);
lean_dec_ref(v___x_1656_);
v___x_1658_ = l_Lean_Expr_appArg_x21(v___x_1657_);
lean_dec_ref(v___x_1657_);
v___x_1659_ = l_Lean_Expr_appArg_x21(v_snd_1455_);
v_fst_1596_ = v___x_1449_;
v_fst_1597_ = v___x_1658_;
v_snd_1598_ = v___x_1659_;
goto v___jp_1595_;
}
v___jp_1462_:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1465_, 0, v_proof_1464_);
v___x_1466_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1466_, 0, v___y_1463_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
lean_ctor_set_uint8(v___x_1466_, sizeof(void*)*2, v___x_1449_);
v___x_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
return v___x_1467_;
}
v___jp_1468_:
{
if (lean_obj_tag(v___y_1470_) == 0)
{
lean_object* v_a_1471_; 
v_a_1471_ = lean_ctor_get(v___y_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___y_1470_, 1);
v___y_1463_ = v___y_1469_;
v_proof_1464_ = v_a_1471_;
goto v___jp_1462_;
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_dec_ref(v___y_1469_);
v_a_1472_ = lean_ctor_get(v___y_1470_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___y_1470_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___y_1470_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___y_1470_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
v___jp_1480_:
{
if (v___y_1489_ == 0)
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
lean_dec_ref(v___y_1484_);
v___x_1490_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1491_ = l_Lean_MessageData_ofExpr(v___y_1488_);
v___x_1492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1490_);
lean_ctor_set(v___x_1492_, 1, v___x_1491_);
v___x_1493_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1492_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
v___x_1495_ = l_Lean_Exception_toMessageData(v___y_1483_);
v___x_1496_ = l_Lean_indentD(v___x_1495_);
v___x_1497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1494_);
lean_ctor_set(v___x_1497_, 1, v___x_1496_);
v___x_1498_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1497_);
lean_ctor_set(v___x_1499_, 1, v___x_1498_);
v___x_1500_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___redArg(v___x_1499_, v___y_1487_, v___y_1482_, v___y_1486_, v___y_1485_);
v___y_1469_ = v___y_1481_;
v___y_1470_ = v___x_1500_;
goto v___jp_1468_;
}
else
{
lean_dec_ref(v___y_1488_);
lean_dec_ref(v___y_1483_);
v___y_1469_ = v___y_1481_;
v___y_1470_ = v___y_1484_;
goto v___jp_1468_;
}
}
v___jp_1502_:
{
lean_object* v___x_1509_; lean_object* v_a_1510_; lean_object* v___x_1511_; 
v___x_1509_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__7___redArg(v___y_1503_, v___y_1506_);
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
lean_dec_ref(v___x_1509_);
v___x_1511_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__7___redArg(v___x_1501_, v___y_1506_);
if (v___y_1504_ == 0)
{
lean_object* v_a_1512_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1512_);
lean_dec_ref(v___x_1511_);
v___y_1463_ = v_a_1510_;
v_proof_1464_ = v_a_1512_;
goto v___jp_1462_;
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1514_; 
v_a_1513_ = lean_ctor_get(v___x_1511_, 0);
lean_inc_n(v_a_1513_, 2);
lean_dec_ref(v___x_1511_);
v___x_1514_ = l_Lean_Meta_mkEqOfHEq(v_a_1513_, v___x_1449_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_dec(v_a_1513_);
v___y_1469_ = v_a_1510_;
v___y_1470_ = v___x_1514_;
goto v___jp_1468_;
}
else
{
lean_object* v_a_1515_; uint8_t v___x_1516_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
v___x_1516_ = l_Lean_Exception_isInterrupt(v_a_1515_);
if (v___x_1516_ == 0)
{
uint8_t v___x_1517_; 
lean_inc(v_a_1515_);
v___x_1517_ = l_Lean_Exception_isRuntime(v_a_1515_);
v___y_1481_ = v_a_1510_;
v___y_1482_ = v___y_1506_;
v___y_1483_ = v_a_1515_;
v___y_1484_ = v___x_1514_;
v___y_1485_ = v___y_1508_;
v___y_1486_ = v___y_1507_;
v___y_1487_ = v___y_1505_;
v___y_1488_ = v_a_1513_;
v___y_1489_ = v___x_1517_;
goto v___jp_1480_;
}
else
{
v___y_1481_ = v_a_1510_;
v___y_1482_ = v___y_1506_;
v___y_1483_ = v_a_1515_;
v___y_1484_ = v___x_1514_;
v___y_1485_ = v___y_1508_;
v___y_1486_ = v___y_1507_;
v___y_1487_ = v___y_1505_;
v___y_1488_ = v_a_1513_;
v___y_1489_ = v___x_1516_;
goto v___jp_1480_;
}
}
}
}
v___jp_1518_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; 
v___x_1526_ = lean_array_get_size(v_a_1525_);
v___x_1527_ = lean_unsigned_to_nat(0u);
v___x_1528_ = lean_nat_dec_eq(v___x_1526_, v___x_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
lean_dec_ref(v___y_1519_);
lean_dec_ref(v___x_1501_);
v___x_1529_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1530_ = l_Lean_MessageData_ofConstName(v___x_1452_, v___x_1453_);
v___x_1531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1529_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___x_1532_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1531_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = lean_array_to_list(v_a_1525_);
v___x_1535_ = lean_box(0);
v___x_1536_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__9(v___x_1534_, v___x_1535_);
v___x_1537_ = l_Lean_MessageData_ofList(v___x_1536_);
v___x_1538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1533_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___redArg(v___x_1538_, v___y_1524_, v___y_1520_, v___y_1521_, v___y_1523_);
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1542_ = v___x_1539_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1539_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_a_1540_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
else
{
lean_dec_ref(v_a_1525_);
lean_dec(v___x_1452_);
v___y_1503_ = v___y_1519_;
v___y_1504_ = v___y_1522_;
v___y_1505_ = v___y_1524_;
v___y_1506_ = v___y_1520_;
v___y_1507_ = v___y_1521_;
v___y_1508_ = v___y_1523_;
goto v___jp_1502_;
}
}
v___jp_1548_:
{
if (lean_obj_tag(v___y_1555_) == 0)
{
lean_object* v_a_1556_; 
v_a_1556_ = lean_ctor_get(v___y_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref_known(v___y_1555_, 1);
v___y_1519_ = v___y_1549_;
v___y_1520_ = v___y_1550_;
v___y_1521_ = v___y_1551_;
v___y_1522_ = v___y_1552_;
v___y_1523_ = v___y_1554_;
v___y_1524_ = v___y_1553_;
v_a_1525_ = v_a_1556_;
goto v___jp_1518_;
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec_ref(v___y_1549_);
lean_dec_ref(v___x_1501_);
lean_dec(v___x_1452_);
v_a_1557_ = lean_ctor_get(v___y_1555_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___y_1555_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___y_1555_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___y_1555_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
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
v___jp_1568_:
{
lean_object* v___x_1575_; size_t v_sz_1576_; lean_object* v___x_1577_; 
v___x_1575_ = lean_box(0);
v_sz_1576_ = lean_array_size(v___x_1567_);
v___x_1577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10(v___x_1567_, v_sz_1576_, v___x_1566_, v___x_1575_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; uint8_t v___x_1581_; 
lean_dec_ref_known(v___x_1577_, 1);
v___x_1578_ = lean_unsigned_to_nat(0u);
v___x_1579_ = lean_array_get_size(v___x_1567_);
v___x_1580_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1581_ = lean_nat_dec_lt(v___x_1578_, v___x_1579_);
if (v___x_1581_ == 0)
{
lean_dec_ref(v___x_1567_);
v___y_1519_ = v___y_1569_;
v___y_1520_ = v___y_1572_;
v___y_1521_ = v___y_1573_;
v___y_1522_ = v___y_1570_;
v___y_1523_ = v___y_1574_;
v___y_1524_ = v___y_1571_;
v_a_1525_ = v___x_1580_;
goto v___jp_1518_;
}
else
{
uint8_t v___x_1582_; 
v___x_1582_ = lean_nat_dec_le(v___x_1579_, v___x_1579_);
if (v___x_1582_ == 0)
{
if (v___x_1581_ == 0)
{
lean_dec_ref(v___x_1567_);
v___y_1519_ = v___y_1569_;
v___y_1520_ = v___y_1572_;
v___y_1521_ = v___y_1573_;
v___y_1522_ = v___y_1570_;
v___y_1523_ = v___y_1574_;
v___y_1524_ = v___y_1571_;
v_a_1525_ = v___x_1580_;
goto v___jp_1518_;
}
else
{
size_t v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = lean_usize_of_nat(v___x_1579_);
v___x_1584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__11(v___x_1567_, v___x_1566_, v___x_1583_, v___x_1580_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
lean_dec_ref(v___x_1567_);
v___y_1549_ = v___y_1569_;
v___y_1550_ = v___y_1572_;
v___y_1551_ = v___y_1573_;
v___y_1552_ = v___y_1570_;
v___y_1553_ = v___y_1571_;
v___y_1554_ = v___y_1574_;
v___y_1555_ = v___x_1584_;
goto v___jp_1548_;
}
}
else
{
size_t v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = lean_usize_of_nat(v___x_1579_);
v___x_1586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__11(v___x_1567_, v___x_1566_, v___x_1585_, v___x_1580_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
lean_dec_ref(v___x_1567_);
v___y_1549_ = v___y_1569_;
v___y_1550_ = v___y_1572_;
v___y_1551_ = v___y_1573_;
v___y_1552_ = v___y_1570_;
v___y_1553_ = v___y_1571_;
v___y_1554_ = v___y_1574_;
v___y_1555_ = v___x_1586_;
goto v___jp_1548_;
}
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec_ref(v___y_1569_);
lean_dec_ref(v___x_1567_);
lean_dec_ref(v___x_1501_);
lean_dec(v___x_1452_);
v_a_1587_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1577_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1577_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
}
v___jp_1595_:
{
lean_object* v___x_1599_; 
lean_inc_ref(v_fst_1597_);
lean_inc_ref(v_e_1454_);
v___x_1599_ = l_Lean_Meta_isExprDefEq(v_e_1454_, v_fst_1597_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; uint8_t v___x_1601_; uint8_t v___x_1602_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1600_);
lean_dec_ref_known(v___x_1599_, 1);
v___x_1601_ = lean_unbox(v_a_1600_);
lean_dec(v_a_1600_);
v___x_1602_ = lean_bool_not(v___x_1601_);
if (v___x_1602_ == 0)
{
lean_dec_ref(v_fst_1597_);
lean_dec_ref(v_e_1454_);
v___y_1569_ = v_snd_1598_;
v___y_1570_ = v_fst_1596_;
v___y_1571_ = v___y_1457_;
v___y_1572_ = v___y_1458_;
v___y_1573_ = v___y_1459_;
v___y_1574_ = v___y_1460_;
goto v___jp_1568_;
}
else
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
lean_dec_ref(v_snd_1598_);
lean_dec_ref(v___x_1567_);
lean_dec_ref(v___x_1501_);
v___x_1603_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1604_ = l_Lean_MessageData_ofExpr(v_fst_1597_);
v___x_1605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1603_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
v___x_1606_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1605_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
v___x_1608_ = l_Lean_MessageData_ofConstName(v___x_1452_, v___x_1453_);
v___x_1609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1607_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
v___x_1610_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1609_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
v___x_1612_ = l_Lean_MessageData_ofExpr(v_e_1454_);
v___x_1613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1611_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
v___x_1614_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__3);
v___x_1615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1613_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
v___x_1616_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___redArg(v___x_1615_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1616_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1616_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
lean_dec_ref(v_snd_1598_);
lean_dec_ref(v_fst_1597_);
lean_dec_ref(v___x_1567_);
lean_dec_ref(v___x_1501_);
lean_dec_ref(v_e_1454_);
lean_dec(v___x_1452_);
v_a_1625_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1599_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1599_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4___boxed(lean_object* v___x_1660_, lean_object* v___x_1661_, lean_object* v_fst_1662_, lean_object* v___x_1663_, lean_object* v___x_1664_, lean_object* v_e_1665_, lean_object* v_snd_1666_, lean_object* v_____r_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
uint8_t v___x_108199__boxed_1673_; uint8_t v___x_108203__boxed_1674_; lean_object* v_res_1675_; 
v___x_108199__boxed_1673_ = lean_unbox(v___x_1660_);
v___x_108203__boxed_1674_ = lean_unbox(v___x_1664_);
v_res_1675_ = l_Lean_Meta_rwMatcher___lam__4(v___x_108199__boxed_1673_, v___x_1661_, v_fst_1662_, v___x_1663_, v___x_108203__boxed_1674_, v_e_1665_, v_snd_1666_, v_____r_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec_ref(v_snd_1666_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__5(uint8_t v___x_1676_, lean_object* v___x_1677_, lean_object* v_fst_1678_, lean_object* v___x_1679_, lean_object* v_e_1680_, uint8_t v___y_1681_, lean_object* v_snd_1682_, lean_object* v_____r_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v___y_1690_; lean_object* v_proof_1691_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; uint8_t v___y_1716_; lean_object* v___x_1728_; uint8_t v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1746_; uint8_t v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v_a_1752_; lean_object* v___y_1776_; uint8_t v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; size_t v_sz_1792_; size_t v___x_1793_; lean_object* v___x_1794_; uint8_t v___y_1796_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; uint8_t v_fst_1823_; lean_object* v_fst_1824_; lean_object* v_snd_1825_; lean_object* v___x_1860_; lean_object* v___x_1861_; uint8_t v___x_1862_; 
v___x_1728_ = l_Lean_mkAppN(v___x_1677_, v_fst_1678_);
v_sz_1792_ = lean_array_size(v_fst_1678_);
v___x_1793_ = ((size_t)0ULL);
v___x_1794_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__6(v_sz_1792_, v___x_1793_, v_fst_1678_);
v___x_1860_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1861_ = lean_unsigned_to_nat(4u);
v___x_1862_ = l_Lean_Expr_isAppOfArity(v_snd_1682_, v___x_1860_, v___x_1861_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1863_; lean_object* v___x_1864_; uint8_t v___x_1865_; 
v___x_1863_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1864_ = lean_unsigned_to_nat(3u);
v___x_1865_ = l_Lean_Expr_isAppOfArity(v_snd_1682_, v___x_1863_, v___x_1864_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
lean_dec_ref(v___x_1794_);
lean_dec_ref(v___x_1728_);
lean_dec_ref(v_e_1680_);
v___x_1866_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1867_ = l_Lean_MessageData_ofConstName(v___x_1679_, v___x_1865_);
v___x_1868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1866_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
v___x_1869_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1868_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___redArg(v___x_1870_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1871_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1871_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
else
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1880_ = l_Lean_Expr_appFn_x21(v_snd_1682_);
v___x_1881_ = l_Lean_Expr_appArg_x21(v___x_1880_);
lean_dec_ref(v___x_1880_);
v___x_1882_ = l_Lean_Expr_appArg_x21(v_snd_1682_);
v_fst_1823_ = v___x_1862_;
v_fst_1824_ = v___x_1881_;
v_snd_1825_ = v___x_1882_;
goto v___jp_1822_;
}
}
else
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1883_ = l_Lean_Expr_appFn_x21(v_snd_1682_);
v___x_1884_ = l_Lean_Expr_appFn_x21(v___x_1883_);
lean_dec_ref(v___x_1883_);
v___x_1885_ = l_Lean_Expr_appArg_x21(v___x_1884_);
lean_dec_ref(v___x_1884_);
v___x_1886_ = l_Lean_Expr_appArg_x21(v_snd_1682_);
v_fst_1823_ = v___x_1676_;
v_fst_1824_ = v___x_1885_;
v_snd_1825_ = v___x_1886_;
goto v___jp_1822_;
}
v___jp_1689_:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1692_, 0, v_proof_1691_);
v___x_1693_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1693_, 0, v___y_1690_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
lean_ctor_set_uint8(v___x_1693_, sizeof(void*)*2, v___x_1676_);
v___x_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1693_);
return v___x_1694_;
}
v___jp_1695_:
{
if (lean_obj_tag(v___y_1697_) == 0)
{
lean_object* v_a_1698_; 
v_a_1698_ = lean_ctor_get(v___y_1697_, 0);
lean_inc(v_a_1698_);
lean_dec_ref_known(v___y_1697_, 1);
v___y_1690_ = v___y_1696_;
v_proof_1691_ = v_a_1698_;
goto v___jp_1689_;
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
lean_dec_ref(v___y_1696_);
v_a_1699_ = lean_ctor_get(v___y_1697_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___y_1697_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___y_1697_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___y_1697_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
v___jp_1707_:
{
if (v___y_1716_ == 0)
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
lean_dec_ref(v___y_1708_);
v___x_1717_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1718_ = l_Lean_MessageData_ofExpr(v___y_1710_);
v___x_1719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1717_);
lean_ctor_set(v___x_1719_, 1, v___x_1718_);
v___x_1720_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1719_);
lean_ctor_set(v___x_1721_, 1, v___x_1720_);
v___x_1722_ = l_Lean_Exception_toMessageData(v___y_1712_);
v___x_1723_ = l_Lean_indentD(v___x_1722_);
v___x_1724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1721_);
lean_ctor_set(v___x_1724_, 1, v___x_1723_);
v___x_1725_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1724_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
v___x_1727_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___redArg(v___x_1726_, v___y_1711_, v___y_1714_, v___y_1715_, v___y_1709_);
v___y_1696_ = v___y_1713_;
v___y_1697_ = v___x_1727_;
goto v___jp_1695_;
}
else
{
lean_dec_ref(v___y_1712_);
lean_dec_ref(v___y_1710_);
v___y_1696_ = v___y_1713_;
v___y_1697_ = v___y_1708_;
goto v___jp_1695_;
}
}
v___jp_1729_:
{
lean_object* v___x_1736_; lean_object* v_a_1737_; lean_object* v___x_1738_; 
v___x_1736_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__7___redArg(v___y_1731_, v___y_1733_);
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_a_1737_);
lean_dec_ref(v___x_1736_);
v___x_1738_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__7___redArg(v___x_1728_, v___y_1733_);
if (v___y_1730_ == 0)
{
lean_object* v_a_1739_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1739_);
lean_dec_ref(v___x_1738_);
v___y_1690_ = v_a_1737_;
v_proof_1691_ = v_a_1739_;
goto v___jp_1689_;
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1741_; 
v_a_1740_ = lean_ctor_get(v___x_1738_, 0);
lean_inc_n(v_a_1740_, 2);
lean_dec_ref(v___x_1738_);
v___x_1741_ = l_Lean_Meta_mkEqOfHEq(v_a_1740_, v___x_1676_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_dec(v_a_1740_);
v___y_1696_ = v_a_1737_;
v___y_1697_ = v___x_1741_;
goto v___jp_1695_;
}
else
{
lean_object* v_a_1742_; uint8_t v___x_1743_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_a_1742_);
v___x_1743_ = l_Lean_Exception_isInterrupt(v_a_1742_);
if (v___x_1743_ == 0)
{
uint8_t v___x_1744_; 
lean_inc(v_a_1742_);
v___x_1744_ = l_Lean_Exception_isRuntime(v_a_1742_);
v___y_1708_ = v___x_1741_;
v___y_1709_ = v___y_1735_;
v___y_1710_ = v_a_1740_;
v___y_1711_ = v___y_1732_;
v___y_1712_ = v_a_1742_;
v___y_1713_ = v_a_1737_;
v___y_1714_ = v___y_1733_;
v___y_1715_ = v___y_1734_;
v___y_1716_ = v___x_1744_;
goto v___jp_1707_;
}
else
{
v___y_1708_ = v___x_1741_;
v___y_1709_ = v___y_1735_;
v___y_1710_ = v_a_1740_;
v___y_1711_ = v___y_1732_;
v___y_1712_ = v_a_1742_;
v___y_1713_ = v_a_1737_;
v___y_1714_ = v___y_1733_;
v___y_1715_ = v___y_1734_;
v___y_1716_ = v___x_1743_;
goto v___jp_1707_;
}
}
}
}
v___jp_1745_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1753_ = lean_array_get_size(v_a_1752_);
v___x_1754_ = lean_unsigned_to_nat(0u);
v___x_1755_ = lean_nat_dec_eq(v___x_1753_, v___x_1754_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
lean_dec_ref(v___y_1751_);
lean_dec_ref(v___x_1728_);
v___x_1756_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1757_ = l_Lean_MessageData_ofConstName(v___x_1679_, v___x_1755_);
v___x_1758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1756_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
v___x_1759_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1758_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
v___x_1761_ = lean_array_to_list(v_a_1752_);
v___x_1762_ = lean_box(0);
v___x_1763_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__9(v___x_1761_, v___x_1762_);
v___x_1764_ = l_Lean_MessageData_ofList(v___x_1763_);
v___x_1765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1760_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___redArg(v___x_1765_, v___y_1748_, v___y_1746_, v___y_1749_, v___y_1750_);
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1766_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1766_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
else
{
lean_dec_ref(v_a_1752_);
lean_dec(v___x_1679_);
v___y_1730_ = v___y_1747_;
v___y_1731_ = v___y_1751_;
v___y_1732_ = v___y_1748_;
v___y_1733_ = v___y_1746_;
v___y_1734_ = v___y_1749_;
v___y_1735_ = v___y_1750_;
goto v___jp_1729_;
}
}
v___jp_1775_:
{
if (lean_obj_tag(v___y_1782_) == 0)
{
lean_object* v_a_1783_; 
v_a_1783_ = lean_ctor_get(v___y_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref_known(v___y_1782_, 1);
v___y_1746_ = v___y_1776_;
v___y_1747_ = v___y_1777_;
v___y_1748_ = v___y_1778_;
v___y_1749_ = v___y_1779_;
v___y_1750_ = v___y_1780_;
v___y_1751_ = v___y_1781_;
v_a_1752_ = v_a_1783_;
goto v___jp_1745_;
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
lean_dec_ref(v___y_1781_);
lean_dec_ref(v___x_1728_);
lean_dec(v___x_1679_);
v_a_1784_ = lean_ctor_get(v___y_1782_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___y_1782_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___y_1782_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___y_1782_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
v___jp_1795_:
{
lean_object* v___x_1802_; size_t v_sz_1803_; lean_object* v___x_1804_; 
v___x_1802_ = lean_box(0);
v_sz_1803_ = lean_array_size(v___x_1794_);
v___x_1804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10(v___x_1794_, v_sz_1803_, v___x_1793_, v___x_1802_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; 
lean_dec_ref_known(v___x_1804_, 1);
v___x_1805_ = lean_unsigned_to_nat(0u);
v___x_1806_ = lean_array_get_size(v___x_1794_);
v___x_1807_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1808_ = lean_nat_dec_lt(v___x_1805_, v___x_1806_);
if (v___x_1808_ == 0)
{
lean_dec_ref(v___x_1794_);
v___y_1746_ = v___y_1799_;
v___y_1747_ = v___y_1796_;
v___y_1748_ = v___y_1798_;
v___y_1749_ = v___y_1800_;
v___y_1750_ = v___y_1801_;
v___y_1751_ = v___y_1797_;
v_a_1752_ = v___x_1807_;
goto v___jp_1745_;
}
else
{
uint8_t v___x_1809_; 
v___x_1809_ = lean_nat_dec_le(v___x_1806_, v___x_1806_);
if (v___x_1809_ == 0)
{
if (v___x_1808_ == 0)
{
lean_dec_ref(v___x_1794_);
v___y_1746_ = v___y_1799_;
v___y_1747_ = v___y_1796_;
v___y_1748_ = v___y_1798_;
v___y_1749_ = v___y_1800_;
v___y_1750_ = v___y_1801_;
v___y_1751_ = v___y_1797_;
v_a_1752_ = v___x_1807_;
goto v___jp_1745_;
}
else
{
size_t v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = lean_usize_of_nat(v___x_1806_);
v___x_1811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__11(v___x_1794_, v___x_1793_, v___x_1810_, v___x_1807_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
lean_dec_ref(v___x_1794_);
v___y_1776_ = v___y_1799_;
v___y_1777_ = v___y_1796_;
v___y_1778_ = v___y_1798_;
v___y_1779_ = v___y_1800_;
v___y_1780_ = v___y_1801_;
v___y_1781_ = v___y_1797_;
v___y_1782_ = v___x_1811_;
goto v___jp_1775_;
}
}
else
{
size_t v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = lean_usize_of_nat(v___x_1806_);
v___x_1813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__11(v___x_1794_, v___x_1793_, v___x_1812_, v___x_1807_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
lean_dec_ref(v___x_1794_);
v___y_1776_ = v___y_1799_;
v___y_1777_ = v___y_1796_;
v___y_1778_ = v___y_1798_;
v___y_1779_ = v___y_1800_;
v___y_1780_ = v___y_1801_;
v___y_1781_ = v___y_1797_;
v___y_1782_ = v___x_1813_;
goto v___jp_1775_;
}
}
}
else
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
lean_dec_ref(v___y_1797_);
lean_dec_ref(v___x_1794_);
lean_dec_ref(v___x_1728_);
lean_dec(v___x_1679_);
v_a_1814_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1804_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1804_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
v___jp_1822_:
{
lean_object* v___x_1826_; 
lean_inc_ref(v_fst_1824_);
lean_inc_ref(v_e_1680_);
v___x_1826_ = l_Lean_Meta_isExprDefEq(v_e_1680_, v_fst_1824_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; uint8_t v___x_1828_; uint8_t v___x_1829_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_a_1827_);
lean_dec_ref_known(v___x_1826_, 1);
v___x_1828_ = lean_unbox(v_a_1827_);
lean_dec(v_a_1827_);
v___x_1829_ = lean_bool_not(v___x_1828_);
if (v___x_1829_ == 0)
{
lean_dec_ref(v_fst_1824_);
lean_dec_ref(v_e_1680_);
v___y_1796_ = v_fst_1823_;
v___y_1797_ = v_snd_1825_;
v___y_1798_ = v___y_1684_;
v___y_1799_ = v___y_1685_;
v___y_1800_ = v___y_1686_;
v___y_1801_ = v___y_1687_;
goto v___jp_1795_;
}
else
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_dec_ref(v_snd_1825_);
lean_dec_ref(v___x_1794_);
lean_dec_ref(v___x_1728_);
v___x_1830_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1831_ = l_Lean_MessageData_ofExpr(v_fst_1824_);
v___x_1832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1830_);
lean_ctor_set(v___x_1832_, 1, v___x_1831_);
v___x_1833_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1832_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
v___x_1835_ = l_Lean_MessageData_ofConstName(v___x_1679_, v___y_1681_);
v___x_1836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1834_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1836_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = l_Lean_MessageData_ofExpr(v_e_1680_);
v___x_1840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1838_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
v___x_1841_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__10___closed__3);
v___x_1842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1840_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
v___x_1843_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___redArg(v___x_1842_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1843_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1843_);
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
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
lean_dec_ref(v_snd_1825_);
lean_dec_ref(v_fst_1824_);
lean_dec_ref(v___x_1794_);
lean_dec_ref(v___x_1728_);
lean_dec_ref(v_e_1680_);
lean_dec(v___x_1679_);
v_a_1852_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1826_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1826_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__5___boxed(lean_object* v___x_1887_, lean_object* v___x_1888_, lean_object* v_fst_1889_, lean_object* v___x_1890_, lean_object* v_e_1891_, lean_object* v___y_1892_, lean_object* v_snd_1893_, lean_object* v_____r_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
uint8_t v___x_108686__boxed_1900_; uint8_t v___y_108690__boxed_1901_; lean_object* v_res_1902_; 
v___x_108686__boxed_1900_ = lean_unbox(v___x_1887_);
v___y_108690__boxed_1901_ = lean_unbox(v___y_1892_);
v_res_1902_ = l_Lean_Meta_rwMatcher___lam__5(v___x_108686__boxed_1900_, v___x_1888_, v_fst_1889_, v___x_1890_, v_e_1891_, v___y_108690__boxed_1901_, v_snd_1893_, v_____r_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec_ref(v_snd_1893_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__8___redArg(lean_object* v_x_1903_){
_start:
{
if (lean_obj_tag(v_x_1903_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
v_a_1905_ = lean_ctor_get(v_x_1903_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v_x_1903_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v_x_1903_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v_x_1903_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
lean_ctor_set_tag(v___x_1907_, 1);
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
v_a_1913_ = lean_ctor_get(v_x_1903_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v_x_1903_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v_x_1903_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v_x_1903_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
lean_ctor_set_tag(v___x_1915_, 0);
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
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
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__8___redArg___boxed(lean_object* v_x_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__8___redArg(v_x_1921_);
return v_res_1923_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__9(lean_object* v_e_1924_){
_start:
{
if (lean_obj_tag(v_e_1924_) == 0)
{
uint8_t v___x_1925_; 
v___x_1925_ = 2;
return v___x_1925_;
}
else
{
uint8_t v___x_1926_; 
v___x_1926_ = 0;
return v___x_1926_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__9___boxed(lean_object* v_e_1927_){
_start:
{
uint8_t v_res_1928_; lean_object* v_r_1929_; 
v_res_1928_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__9(v_e_1927_);
lean_dec_ref(v_e_1927_);
v_r_1929_ = lean_box(v_res_1928_);
return v_r_1929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__7_spec__10(size_t v_sz_1930_, size_t v_i_1931_, lean_object* v_bs_1932_){
_start:
{
uint8_t v___x_1933_; 
v___x_1933_ = lean_usize_dec_lt(v_i_1931_, v_sz_1930_);
if (v___x_1933_ == 0)
{
return v_bs_1932_;
}
else
{
lean_object* v_v_1934_; lean_object* v_msg_1935_; lean_object* v___x_1936_; lean_object* v_bs_x27_1937_; size_t v___x_1938_; size_t v___x_1939_; lean_object* v___x_1940_; 
v_v_1934_ = lean_array_uget_borrowed(v_bs_1932_, v_i_1931_);
v_msg_1935_ = lean_ctor_get(v_v_1934_, 1);
lean_inc_ref(v_msg_1935_);
v___x_1936_ = lean_unsigned_to_nat(0u);
v_bs_x27_1937_ = lean_array_uset(v_bs_1932_, v_i_1931_, v___x_1936_);
v___x_1938_ = ((size_t)1ULL);
v___x_1939_ = lean_usize_add(v_i_1931_, v___x_1938_);
v___x_1940_ = lean_array_uset(v_bs_x27_1937_, v_i_1931_, v_msg_1935_);
v_i_1931_ = v___x_1939_;
v_bs_1932_ = v___x_1940_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__7_spec__10___boxed(lean_object* v_sz_1942_, lean_object* v_i_1943_, lean_object* v_bs_1944_){
_start:
{
size_t v_sz_boxed_1945_; size_t v_i_boxed_1946_; lean_object* v_res_1947_; 
v_sz_boxed_1945_ = lean_unbox_usize(v_sz_1942_);
lean_dec(v_sz_1942_);
v_i_boxed_1946_ = lean_unbox_usize(v_i_1943_);
lean_dec(v_i_1943_);
v_res_1947_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__7_spec__10(v_sz_boxed_1945_, v_i_boxed_1946_, v_bs_1944_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__7(lean_object* v_oldTraces_1948_, lean_object* v_data_1949_, lean_object* v_ref_1950_, lean_object* v_msg_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_fileName_1957_; lean_object* v_fileMap_1958_; lean_object* v_options_1959_; lean_object* v_currRecDepth_1960_; lean_object* v_maxRecDepth_1961_; lean_object* v_ref_1962_; lean_object* v_currNamespace_1963_; lean_object* v_openDecls_1964_; lean_object* v_initHeartbeats_1965_; lean_object* v_maxHeartbeats_1966_; lean_object* v_quotContext_1967_; lean_object* v_currMacroScope_1968_; uint8_t v_diag_1969_; lean_object* v_cancelTk_x3f_1970_; uint8_t v_suppressElabErrors_1971_; lean_object* v_inheritedTraceOptions_1972_; lean_object* v___x_1973_; lean_object* v_traceState_1974_; lean_object* v_traces_1975_; lean_object* v_ref_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; size_t v_sz_1979_; size_t v___x_1980_; lean_object* v___x_1981_; lean_object* v_msg_1982_; lean_object* v___x_1983_; lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_2021_; 
v_fileName_1957_ = lean_ctor_get(v___y_1954_, 0);
v_fileMap_1958_ = lean_ctor_get(v___y_1954_, 1);
v_options_1959_ = lean_ctor_get(v___y_1954_, 2);
v_currRecDepth_1960_ = lean_ctor_get(v___y_1954_, 3);
v_maxRecDepth_1961_ = lean_ctor_get(v___y_1954_, 4);
v_ref_1962_ = lean_ctor_get(v___y_1954_, 5);
v_currNamespace_1963_ = lean_ctor_get(v___y_1954_, 6);
v_openDecls_1964_ = lean_ctor_get(v___y_1954_, 7);
v_initHeartbeats_1965_ = lean_ctor_get(v___y_1954_, 8);
v_maxHeartbeats_1966_ = lean_ctor_get(v___y_1954_, 9);
v_quotContext_1967_ = lean_ctor_get(v___y_1954_, 10);
v_currMacroScope_1968_ = lean_ctor_get(v___y_1954_, 11);
v_diag_1969_ = lean_ctor_get_uint8(v___y_1954_, sizeof(void*)*14);
v_cancelTk_x3f_1970_ = lean_ctor_get(v___y_1954_, 12);
v_suppressElabErrors_1971_ = lean_ctor_get_uint8(v___y_1954_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1972_ = lean_ctor_get(v___y_1954_, 13);
v___x_1973_ = lean_st_ref_get(v___y_1955_);
v_traceState_1974_ = lean_ctor_get(v___x_1973_, 4);
lean_inc_ref(v_traceState_1974_);
lean_dec(v___x_1973_);
v_traces_1975_ = lean_ctor_get(v_traceState_1974_, 0);
lean_inc_ref(v_traces_1975_);
lean_dec_ref(v_traceState_1974_);
v_ref_1976_ = l_Lean_replaceRef(v_ref_1950_, v_ref_1962_);
lean_inc_ref(v_inheritedTraceOptions_1972_);
lean_inc(v_cancelTk_x3f_1970_);
lean_inc(v_currMacroScope_1968_);
lean_inc(v_quotContext_1967_);
lean_inc(v_maxHeartbeats_1966_);
lean_inc(v_initHeartbeats_1965_);
lean_inc(v_openDecls_1964_);
lean_inc(v_currNamespace_1963_);
lean_inc(v_maxRecDepth_1961_);
lean_inc(v_currRecDepth_1960_);
lean_inc_ref(v_options_1959_);
lean_inc_ref(v_fileMap_1958_);
lean_inc_ref(v_fileName_1957_);
v___x_1977_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1977_, 0, v_fileName_1957_);
lean_ctor_set(v___x_1977_, 1, v_fileMap_1958_);
lean_ctor_set(v___x_1977_, 2, v_options_1959_);
lean_ctor_set(v___x_1977_, 3, v_currRecDepth_1960_);
lean_ctor_set(v___x_1977_, 4, v_maxRecDepth_1961_);
lean_ctor_set(v___x_1977_, 5, v_ref_1976_);
lean_ctor_set(v___x_1977_, 6, v_currNamespace_1963_);
lean_ctor_set(v___x_1977_, 7, v_openDecls_1964_);
lean_ctor_set(v___x_1977_, 8, v_initHeartbeats_1965_);
lean_ctor_set(v___x_1977_, 9, v_maxHeartbeats_1966_);
lean_ctor_set(v___x_1977_, 10, v_quotContext_1967_);
lean_ctor_set(v___x_1977_, 11, v_currMacroScope_1968_);
lean_ctor_set(v___x_1977_, 12, v_cancelTk_x3f_1970_);
lean_ctor_set(v___x_1977_, 13, v_inheritedTraceOptions_1972_);
lean_ctor_set_uint8(v___x_1977_, sizeof(void*)*14, v_diag_1969_);
lean_ctor_set_uint8(v___x_1977_, sizeof(void*)*14 + 1, v_suppressElabErrors_1971_);
v___x_1978_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1975_);
lean_dec_ref(v_traces_1975_);
v_sz_1979_ = lean_array_size(v___x_1978_);
v___x_1980_ = ((size_t)0ULL);
v___x_1981_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__7_spec__10(v_sz_1979_, v___x_1980_, v___x_1978_);
v_msg_1982_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1982_, 0, v_data_1949_);
lean_ctor_set(v_msg_1982_, 1, v_msg_1951_);
lean_ctor_set(v_msg_1982_, 2, v___x_1981_);
v___x_1983_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_1982_, v___y_1952_, v___y_1953_, v___x_1977_, v___y_1955_);
lean_dec_ref_known(v___x_1977_, 14);
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_1986_ = v___x_1983_;
v_isShared_1987_ = v_isSharedCheck_2021_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1983_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_2021_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1988_; lean_object* v_traceState_1989_; lean_object* v_env_1990_; lean_object* v_nextMacroScope_1991_; lean_object* v_ngen_1992_; lean_object* v_auxDeclNGen_1993_; lean_object* v_cache_1994_; lean_object* v_messages_1995_; lean_object* v_infoState_1996_; lean_object* v_snapshotTasks_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2020_; 
v___x_1988_ = lean_st_ref_take(v___y_1955_);
v_traceState_1989_ = lean_ctor_get(v___x_1988_, 4);
v_env_1990_ = lean_ctor_get(v___x_1988_, 0);
v_nextMacroScope_1991_ = lean_ctor_get(v___x_1988_, 1);
v_ngen_1992_ = lean_ctor_get(v___x_1988_, 2);
v_auxDeclNGen_1993_ = lean_ctor_get(v___x_1988_, 3);
v_cache_1994_ = lean_ctor_get(v___x_1988_, 5);
v_messages_1995_ = lean_ctor_get(v___x_1988_, 6);
v_infoState_1996_ = lean_ctor_get(v___x_1988_, 7);
v_snapshotTasks_1997_ = lean_ctor_get(v___x_1988_, 8);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_1999_ = v___x_1988_;
v_isShared_2000_ = v_isSharedCheck_2020_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_snapshotTasks_1997_);
lean_inc(v_infoState_1996_);
lean_inc(v_messages_1995_);
lean_inc(v_cache_1994_);
lean_inc(v_traceState_1989_);
lean_inc(v_auxDeclNGen_1993_);
lean_inc(v_ngen_1992_);
lean_inc(v_nextMacroScope_1991_);
lean_inc(v_env_1990_);
lean_dec(v___x_1988_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2020_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
uint64_t v_tid_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2018_; 
v_tid_2001_ = lean_ctor_get_uint64(v_traceState_1989_, sizeof(void*)*1);
v_isSharedCheck_2018_ = !lean_is_exclusive(v_traceState_1989_);
if (v_isSharedCheck_2018_ == 0)
{
lean_object* v_unused_2019_; 
v_unused_2019_ = lean_ctor_get(v_traceState_1989_, 0);
lean_dec(v_unused_2019_);
v___x_2003_ = v_traceState_1989_;
v_isShared_2004_ = v_isSharedCheck_2018_;
goto v_resetjp_2002_;
}
else
{
lean_dec(v_traceState_1989_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2018_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2008_; 
v___x_2005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2005_, 0, v_ref_1950_);
lean_ctor_set(v___x_2005_, 1, v_a_1984_);
v___x_2006_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1948_, v___x_2005_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2006_);
v___x_2008_ = v___x_2003_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2006_);
lean_ctor_set_uint64(v_reuseFailAlloc_2017_, sizeof(void*)*1, v_tid_2001_);
v___x_2008_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
lean_object* v___x_2010_; 
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 4, v___x_2008_);
v___x_2010_ = v___x_1999_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_env_1990_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_nextMacroScope_1991_);
lean_ctor_set(v_reuseFailAlloc_2016_, 2, v_ngen_1992_);
lean_ctor_set(v_reuseFailAlloc_2016_, 3, v_auxDeclNGen_1993_);
lean_ctor_set(v_reuseFailAlloc_2016_, 4, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2016_, 5, v_cache_1994_);
lean_ctor_set(v_reuseFailAlloc_2016_, 6, v_messages_1995_);
lean_ctor_set(v_reuseFailAlloc_2016_, 7, v_infoState_1996_);
lean_ctor_set(v_reuseFailAlloc_2016_, 8, v_snapshotTasks_1997_);
v___x_2010_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2014_; 
v___x_2011_ = lean_st_ref_set(v___y_1955_, v___x_2010_);
v___x_2012_ = lean_box(0);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v___x_2012_);
v___x_2014_ = v___x_1986_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2012_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__7___boxed(lean_object* v_oldTraces_2022_, lean_object* v_data_2023_, lean_object* v_ref_2024_, lean_object* v_msg_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__7(v_oldTraces_2022_, v_data_2023_, v_ref_2024_, v_msg_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__10(lean_object* v_opts_2032_, lean_object* v_opt_2033_){
_start:
{
lean_object* v_name_2034_; lean_object* v_defValue_2035_; lean_object* v_map_2036_; lean_object* v___x_2037_; 
v_name_2034_ = lean_ctor_get(v_opt_2033_, 0);
v_defValue_2035_ = lean_ctor_get(v_opt_2033_, 1);
v_map_2036_ = lean_ctor_get(v_opts_2032_, 0);
v___x_2037_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2036_, v_name_2034_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_inc(v_defValue_2035_);
return v_defValue_2035_;
}
else
{
lean_object* v_val_2038_; 
v_val_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_val_2038_);
lean_dec_ref_known(v___x_2037_, 1);
if (lean_obj_tag(v_val_2038_) == 3)
{
lean_object* v_v_2039_; 
v_v_2039_ = lean_ctor_get(v_val_2038_, 0);
lean_inc(v_v_2039_);
lean_dec_ref_known(v_val_2038_, 1);
return v_v_2039_;
}
else
{
lean_dec(v_val_2038_);
lean_inc(v_defValue_2035_);
return v_defValue_2035_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__10___boxed(lean_object* v_opts_2040_, lean_object* v_opt_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__10(v_opts_2040_, v_opt_2041_);
lean_dec_ref(v_opt_2041_);
lean_dec_ref(v_opts_2040_);
return v_res_2042_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2043_; double v___x_2044_; 
v___x_2043_ = lean_unsigned_to_nat(0u);
v___x_2044_ = lean_float_of_nat(v___x_2043_);
return v___x_2044_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___closed__2(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___closed__1));
v___x_2047_ = l_Lean_stringToMessageData(v___x_2046_);
return v___x_2047_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___closed__3(void){
_start:
{
lean_object* v___x_2048_; double v___x_2049_; 
v___x_2048_ = lean_unsigned_to_nat(1000u);
v___x_2049_ = lean_float_of_nat(v___x_2048_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5(lean_object* v_cls_2050_, uint8_t v_collapsed_2051_, lean_object* v_tag_2052_, lean_object* v_opts_2053_, uint8_t v_clsEnabled_2054_, lean_object* v_oldTraces_2055_, lean_object* v_msg_2056_, lean_object* v_resStartStop_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v_fst_2063_; lean_object* v_snd_2064_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v_data_2068_; lean_object* v_fst_2079_; lean_object* v_snd_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; lean_object* v___y_2084_; lean_object* v_a_2085_; uint8_t v___y_2100_; double v___y_2131_; 
v_fst_2063_ = lean_ctor_get(v_resStartStop_2057_, 0);
lean_inc(v_fst_2063_);
v_snd_2064_ = lean_ctor_get(v_resStartStop_2057_, 1);
lean_inc(v_snd_2064_);
lean_dec_ref(v_resStartStop_2057_);
v_fst_2079_ = lean_ctor_get(v_snd_2064_, 0);
lean_inc(v_fst_2079_);
v_snd_2080_ = lean_ctor_get(v_snd_2064_, 1);
lean_inc(v_snd_2080_);
lean_dec(v_snd_2064_);
v___x_2081_ = l_Lean_trace_profiler;
v___x_2082_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__4(v_opts_2053_, v___x_2081_);
if (v___x_2082_ == 0)
{
v___y_2100_ = v___x_2082_;
goto v___jp_2099_;
}
else
{
lean_object* v___x_2136_; uint8_t v___x_2137_; 
v___x_2136_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2137_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__4(v_opts_2053_, v___x_2136_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2138_; lean_object* v___x_2139_; double v___x_2140_; double v___x_2141_; double v___x_2142_; 
v___x_2138_ = l_Lean_trace_profiler_threshold;
v___x_2139_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__10(v_opts_2053_, v___x_2138_);
v___x_2140_ = lean_float_of_nat(v___x_2139_);
v___x_2141_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___closed__3);
v___x_2142_ = lean_float_div(v___x_2140_, v___x_2141_);
v___y_2131_ = v___x_2142_;
goto v___jp_2130_;
}
else
{
lean_object* v___x_2143_; lean_object* v___x_2144_; double v___x_2145_; 
v___x_2143_ = l_Lean_trace_profiler_threshold;
v___x_2144_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__10(v_opts_2053_, v___x_2143_);
v___x_2145_ = lean_float_of_nat(v___x_2144_);
v___y_2131_ = v___x_2145_;
goto v___jp_2130_;
}
}
v___jp_2065_:
{
lean_object* v___x_2069_; 
lean_inc(v___y_2067_);
v___x_2069_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__7(v_oldTraces_2055_, v_data_2068_, v___y_2067_, v___y_2066_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v___x_2070_; 
lean_dec_ref_known(v___x_2069_, 1);
v___x_2070_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__8___redArg(v_fst_2063_);
return v___x_2070_;
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_dec(v_fst_2063_);
v_a_2071_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2069_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2069_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
v___jp_2083_:
{
uint8_t v_result_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; double v___x_2089_; lean_object* v_data_2090_; 
v_result_2086_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__9(v_fst_2063_);
v___x_2087_ = lean_box(v_result_2086_);
v___x_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
v___x_2089_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___closed__0);
lean_inc_ref(v_tag_2052_);
lean_inc_ref(v___x_2088_);
lean_inc(v_cls_2050_);
v_data_2090_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2090_, 0, v_cls_2050_);
lean_ctor_set(v_data_2090_, 1, v___x_2088_);
lean_ctor_set(v_data_2090_, 2, v_tag_2052_);
lean_ctor_set_float(v_data_2090_, sizeof(void*)*3, v___x_2089_);
lean_ctor_set_float(v_data_2090_, sizeof(void*)*3 + 8, v___x_2089_);
lean_ctor_set_uint8(v_data_2090_, sizeof(void*)*3 + 16, v_collapsed_2051_);
if (v___x_2082_ == 0)
{
lean_dec_ref_known(v___x_2088_, 1);
lean_dec(v_snd_2080_);
lean_dec(v_fst_2079_);
lean_dec_ref(v_tag_2052_);
lean_dec(v_cls_2050_);
v___y_2066_ = v_a_2085_;
v___y_2067_ = v___y_2084_;
v_data_2068_ = v_data_2090_;
goto v___jp_2065_;
}
else
{
lean_object* v_data_2091_; double v___x_2092_; double v___x_2093_; 
lean_dec_ref_known(v_data_2090_, 3);
v_data_2091_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2091_, 0, v_cls_2050_);
lean_ctor_set(v_data_2091_, 1, v___x_2088_);
lean_ctor_set(v_data_2091_, 2, v_tag_2052_);
v___x_2092_ = lean_unbox_float(v_fst_2079_);
lean_dec(v_fst_2079_);
lean_ctor_set_float(v_data_2091_, sizeof(void*)*3, v___x_2092_);
v___x_2093_ = lean_unbox_float(v_snd_2080_);
lean_dec(v_snd_2080_);
lean_ctor_set_float(v_data_2091_, sizeof(void*)*3 + 8, v___x_2093_);
lean_ctor_set_uint8(v_data_2091_, sizeof(void*)*3 + 16, v_collapsed_2051_);
v___y_2066_ = v_a_2085_;
v___y_2067_ = v___y_2084_;
v_data_2068_ = v_data_2091_;
goto v___jp_2065_;
}
}
v___jp_2094_:
{
lean_object* v_ref_2095_; lean_object* v___x_2096_; 
v_ref_2095_ = lean_ctor_get(v___y_2060_, 5);
lean_inc(v___y_2061_);
lean_inc_ref(v___y_2060_);
lean_inc(v___y_2059_);
lean_inc_ref(v___y_2058_);
lean_inc(v_fst_2063_);
v___x_2096_ = lean_apply_6(v_msg_2056_, v_fst_2063_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, lean_box(0));
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref_known(v___x_2096_, 1);
v___y_2084_ = v_ref_2095_;
v_a_2085_ = v_a_2097_;
goto v___jp_2083_;
}
else
{
lean_object* v___x_2098_; 
lean_dec_ref_known(v___x_2096_, 1);
v___x_2098_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___closed__2);
v___y_2084_ = v_ref_2095_;
v_a_2085_ = v___x_2098_;
goto v___jp_2083_;
}
}
v___jp_2099_:
{
if (v_clsEnabled_2054_ == 0)
{
if (v___y_2100_ == 0)
{
lean_object* v___x_2101_; lean_object* v_traceState_2102_; lean_object* v_env_2103_; lean_object* v_nextMacroScope_2104_; lean_object* v_ngen_2105_; lean_object* v_auxDeclNGen_2106_; lean_object* v_cache_2107_; lean_object* v_messages_2108_; lean_object* v_infoState_2109_; lean_object* v_snapshotTasks_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2129_; 
lean_dec(v_snd_2080_);
lean_dec(v_fst_2079_);
lean_dec_ref(v_msg_2056_);
lean_dec_ref(v_tag_2052_);
lean_dec(v_cls_2050_);
v___x_2101_ = lean_st_ref_take(v___y_2061_);
v_traceState_2102_ = lean_ctor_get(v___x_2101_, 4);
v_env_2103_ = lean_ctor_get(v___x_2101_, 0);
v_nextMacroScope_2104_ = lean_ctor_get(v___x_2101_, 1);
v_ngen_2105_ = lean_ctor_get(v___x_2101_, 2);
v_auxDeclNGen_2106_ = lean_ctor_get(v___x_2101_, 3);
v_cache_2107_ = lean_ctor_get(v___x_2101_, 5);
v_messages_2108_ = lean_ctor_get(v___x_2101_, 6);
v_infoState_2109_ = lean_ctor_get(v___x_2101_, 7);
v_snapshotTasks_2110_ = lean_ctor_get(v___x_2101_, 8);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2112_ = v___x_2101_;
v_isShared_2113_ = v_isSharedCheck_2129_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_snapshotTasks_2110_);
lean_inc(v_infoState_2109_);
lean_inc(v_messages_2108_);
lean_inc(v_cache_2107_);
lean_inc(v_traceState_2102_);
lean_inc(v_auxDeclNGen_2106_);
lean_inc(v_ngen_2105_);
lean_inc(v_nextMacroScope_2104_);
lean_inc(v_env_2103_);
lean_dec(v___x_2101_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2129_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
uint64_t v_tid_2114_; lean_object* v_traces_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2128_; 
v_tid_2114_ = lean_ctor_get_uint64(v_traceState_2102_, sizeof(void*)*1);
v_traces_2115_ = lean_ctor_get(v_traceState_2102_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v_traceState_2102_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2117_ = v_traceState_2102_;
v_isShared_2118_ = v_isSharedCheck_2128_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_traces_2115_);
lean_dec(v_traceState_2102_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2128_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2119_; lean_object* v___x_2121_; 
v___x_2119_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2055_, v_traces_2115_);
lean_dec_ref(v_traces_2115_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 0, v___x_2119_);
v___x_2121_ = v___x_2117_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2119_);
lean_ctor_set_uint64(v_reuseFailAlloc_2127_, sizeof(void*)*1, v_tid_2114_);
v___x_2121_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_object* v___x_2123_; 
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 4, v___x_2121_);
v___x_2123_ = v___x_2112_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_env_2103_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v_nextMacroScope_2104_);
lean_ctor_set(v_reuseFailAlloc_2126_, 2, v_ngen_2105_);
lean_ctor_set(v_reuseFailAlloc_2126_, 3, v_auxDeclNGen_2106_);
lean_ctor_set(v_reuseFailAlloc_2126_, 4, v___x_2121_);
lean_ctor_set(v_reuseFailAlloc_2126_, 5, v_cache_2107_);
lean_ctor_set(v_reuseFailAlloc_2126_, 6, v_messages_2108_);
lean_ctor_set(v_reuseFailAlloc_2126_, 7, v_infoState_2109_);
lean_ctor_set(v_reuseFailAlloc_2126_, 8, v_snapshotTasks_2110_);
v___x_2123_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = lean_st_ref_set(v___y_2061_, v___x_2123_);
v___x_2125_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__8___redArg(v_fst_2063_);
return v___x_2125_;
}
}
}
}
}
else
{
goto v___jp_2094_;
}
}
else
{
goto v___jp_2094_;
}
}
v___jp_2130_:
{
double v___x_2132_; double v___x_2133_; double v___x_2134_; uint8_t v___x_2135_; 
v___x_2132_ = lean_unbox_float(v_snd_2080_);
v___x_2133_ = lean_unbox_float(v_fst_2079_);
v___x_2134_ = lean_float_sub(v___x_2132_, v___x_2133_);
v___x_2135_ = lean_float_decLt(v___y_2131_, v___x_2134_);
v___y_2100_ = v___x_2135_;
goto v___jp_2099_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___boxed(lean_object* v_cls_2146_, lean_object* v_collapsed_2147_, lean_object* v_tag_2148_, lean_object* v_opts_2149_, lean_object* v_clsEnabled_2150_, lean_object* v_oldTraces_2151_, lean_object* v_msg_2152_, lean_object* v_resStartStop_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
uint8_t v_collapsed_boxed_2159_; uint8_t v_clsEnabled_boxed_2160_; lean_object* v_res_2161_; 
v_collapsed_boxed_2159_ = lean_unbox(v_collapsed_2147_);
v_clsEnabled_boxed_2160_ = lean_unbox(v_clsEnabled_2150_);
v_res_2161_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5(v_cls_2146_, v_collapsed_boxed_2159_, v_tag_2148_, v_opts_2149_, v_clsEnabled_boxed_2160_, v_oldTraces_2151_, v_msg_2152_, v_resStartStop_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec_ref(v_opts_2149_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(lean_object* v_cls_2165_, lean_object* v_msg_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v_ref_2172_; lean_object* v___x_2173_; lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2218_; 
v_ref_2172_ = lean_ctor_get(v___y_2169_, 5);
v___x_2173_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2176_ = v___x_2173_;
v_isShared_2177_ = v_isSharedCheck_2218_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2173_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2218_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2178_; lean_object* v_traceState_2179_; lean_object* v_env_2180_; lean_object* v_nextMacroScope_2181_; lean_object* v_ngen_2182_; lean_object* v_auxDeclNGen_2183_; lean_object* v_cache_2184_; lean_object* v_messages_2185_; lean_object* v_infoState_2186_; lean_object* v_snapshotTasks_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2217_; 
v___x_2178_ = lean_st_ref_take(v___y_2170_);
v_traceState_2179_ = lean_ctor_get(v___x_2178_, 4);
v_env_2180_ = lean_ctor_get(v___x_2178_, 0);
v_nextMacroScope_2181_ = lean_ctor_get(v___x_2178_, 1);
v_ngen_2182_ = lean_ctor_get(v___x_2178_, 2);
v_auxDeclNGen_2183_ = lean_ctor_get(v___x_2178_, 3);
v_cache_2184_ = lean_ctor_get(v___x_2178_, 5);
v_messages_2185_ = lean_ctor_get(v___x_2178_, 6);
v_infoState_2186_ = lean_ctor_get(v___x_2178_, 7);
v_snapshotTasks_2187_ = lean_ctor_get(v___x_2178_, 8);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2189_ = v___x_2178_;
v_isShared_2190_ = v_isSharedCheck_2217_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_snapshotTasks_2187_);
lean_inc(v_infoState_2186_);
lean_inc(v_messages_2185_);
lean_inc(v_cache_2184_);
lean_inc(v_traceState_2179_);
lean_inc(v_auxDeclNGen_2183_);
lean_inc(v_ngen_2182_);
lean_inc(v_nextMacroScope_2181_);
lean_inc(v_env_2180_);
lean_dec(v___x_2178_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2217_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
uint64_t v_tid_2191_; lean_object* v_traces_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2216_; 
v_tid_2191_ = lean_ctor_get_uint64(v_traceState_2179_, sizeof(void*)*1);
v_traces_2192_ = lean_ctor_get(v_traceState_2179_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v_traceState_2179_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2194_ = v_traceState_2179_;
v_isShared_2195_ = v_isSharedCheck_2216_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_traces_2192_);
lean_dec(v_traceState_2179_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2216_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2196_; double v___x_2197_; uint8_t v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2206_; 
v___x_2196_ = lean_box(0);
v___x_2197_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5___closed__0);
v___x_2198_ = 0;
v___x_2199_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0));
v___x_2200_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2200_, 0, v_cls_2165_);
lean_ctor_set(v___x_2200_, 1, v___x_2196_);
lean_ctor_set(v___x_2200_, 2, v___x_2199_);
lean_ctor_set_float(v___x_2200_, sizeof(void*)*3, v___x_2197_);
lean_ctor_set_float(v___x_2200_, sizeof(void*)*3 + 8, v___x_2197_);
lean_ctor_set_uint8(v___x_2200_, sizeof(void*)*3 + 16, v___x_2198_);
v___x_2201_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1));
v___x_2202_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2200_);
lean_ctor_set(v___x_2202_, 1, v_a_2174_);
lean_ctor_set(v___x_2202_, 2, v___x_2201_);
lean_inc(v_ref_2172_);
v___x_2203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2203_, 0, v_ref_2172_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
v___x_2204_ = l_Lean_PersistentArray_push___redArg(v_traces_2192_, v___x_2203_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v___x_2204_);
v___x_2206_ = v___x_2194_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2204_);
lean_ctor_set_uint64(v_reuseFailAlloc_2215_, sizeof(void*)*1, v_tid_2191_);
v___x_2206_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
lean_object* v___x_2208_; 
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 4, v___x_2206_);
v___x_2208_ = v___x_2189_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_env_2180_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v_nextMacroScope_2181_);
lean_ctor_set(v_reuseFailAlloc_2214_, 2, v_ngen_2182_);
lean_ctor_set(v_reuseFailAlloc_2214_, 3, v_auxDeclNGen_2183_);
lean_ctor_set(v_reuseFailAlloc_2214_, 4, v___x_2206_);
lean_ctor_set(v_reuseFailAlloc_2214_, 5, v_cache_2184_);
lean_ctor_set(v_reuseFailAlloc_2214_, 6, v_messages_2185_);
lean_ctor_set(v_reuseFailAlloc_2214_, 7, v_infoState_2186_);
lean_ctor_set(v_reuseFailAlloc_2214_, 8, v_snapshotTasks_2187_);
v___x_2208_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2212_; 
v___x_2209_ = lean_st_ref_set(v___y_2170_, v___x_2208_);
v___x_2210_ = lean_box(0);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 0, v___x_2210_);
v___x_2212_ = v___x_2176_;
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___boxed(lean_object* v_cls_2219_, lean_object* v_msg_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v_cls_2219_, v_msg_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(lean_object* v_a_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Lean_Meta_reduceRecMatcher_x3f(v_a_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2248_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2236_ = v___x_2233_;
v_isShared_2237_ = v_isSharedCheck_2248_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2233_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2248_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
if (lean_obj_tag(v_a_2234_) == 1)
{
lean_object* v_val_2238_; lean_object* v___x_2239_; 
lean_del_object(v___x_2236_);
lean_dec_ref(v_a_2227_);
v_val_2238_ = lean_ctor_get(v_a_2234_, 0);
lean_inc(v_val_2238_);
lean_dec_ref_known(v_a_2234_, 1);
v___x_2239_ = l_Lean_Expr_headBeta(v_val_2238_);
v_a_2227_ = v___x_2239_;
goto _start;
}
else
{
lean_object* v___x_2241_; uint8_t v___x_2242_; uint8_t v___x_2243_; 
lean_dec(v_a_2234_);
lean_inc_ref(v_a_2227_);
v___x_2241_ = l_Lean_Expr_headBeta(v_a_2227_);
v___x_2242_ = lean_expr_eqv(v_a_2227_, v___x_2241_);
v___x_2243_ = lean_bool_not(v___x_2242_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2245_; 
lean_dec_ref(v___x_2241_);
if (v_isShared_2237_ == 0)
{
lean_ctor_set(v___x_2236_, 0, v_a_2227_);
v___x_2245_ = v___x_2236_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2227_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
else
{
lean_del_object(v___x_2236_);
lean_dec_ref(v_a_2227_);
v_a_2227_ = v___x_2241_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
lean_dec_ref(v_a_2227_);
v_a_2249_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2233_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2233_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2249_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg___boxed(lean_object* v_a_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(v_a_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
return v_res_2263_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__3(void){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2268_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__2));
v___x_2269_ = l_Lean_stringToMessageData(v___x_2268_);
return v___x_2269_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__5(void){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__4));
v___x_2272_ = l_Lean_stringToMessageData(v___x_2271_);
return v___x_2272_;
}
}
static double _init_l_Lean_Meta_rwMatcher___closed__6(void){
_start:
{
lean_object* v___x_2273_; double v___x_2274_; 
v___x_2273_ = lean_unsigned_to_nat(1000000000u);
v___x_2274_ = lean_float_of_nat(v___x_2273_);
return v___x_2274_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__8(void){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__7));
v___x_2277_ = l_Lean_stringToMessageData(v___x_2276_);
return v___x_2277_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__13(void){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2285_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2286_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
v___x_2287_ = l_Lean_Name_append(v___x_2286_, v___x_2285_);
return v___x_2287_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__15(void){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2289_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__14));
v___x_2290_ = l_Lean_stringToMessageData(v___x_2289_);
return v___x_2290_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__17(void){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__16));
v___x_2293_ = l_Lean_stringToMessageData(v___x_2292_);
return v___x_2293_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__19(void){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__18));
v___x_2296_ = l_Lean_stringToMessageData(v___x_2295_);
return v___x_2296_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__21(void){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__20));
v___x_2299_ = l_Lean_stringToMessageData(v___x_2298_);
return v___x_2299_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__22(void){
_start:
{
lean_object* v___x_2300_; lean_object* v_dummy_2301_; 
v___x_2300_ = lean_box(0);
v_dummy_2301_ = l_Lean_Expr_sort___override(v___x_2300_);
return v_dummy_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher(lean_object* v_altIdx_2311_, lean_object* v_e_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_){
_start:
{
lean_object* v___y_2319_; lean_object* v___y_2338_; lean_object* v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; uint8_t v___y_2346_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v_a_2377_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2394_; uint8_t v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; uint8_t v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v_a_2404_; lean_object* v___y_2414_; uint8_t v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; uint8_t v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v_a_2424_; lean_object* v___y_2427_; uint8_t v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; uint8_t v___y_2434_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2448_; uint8_t v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; uint8_t v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2462_; uint8_t v___y_2463_; lean_object* v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; uint8_t v___y_2470_; lean_object* v___y_2471_; lean_object* v_a_2472_; lean_object* v___y_2485_; uint8_t v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; uint8_t v___y_2493_; lean_object* v___y_2494_; lean_object* v_a_2495_; lean_object* v___y_2498_; uint8_t v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; uint8_t v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2519_; uint8_t v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; uint8_t v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; uint8_t v___y_2540_; uint8_t v___y_2545_; uint8_t v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; uint8_t v___y_2553_; uint8_t v___y_2554_; lean_object* v___y_2555_; uint8_t v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; uint8_t v___y_2563_; lean_object* v___y_2564_; uint8_t v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; uint8_t v___y_2636_; uint8_t v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; uint8_t v___y_2644_; lean_object* v___y_2645_; uint8_t v_a_2646_; uint8_t v___y_2680_; lean_object* v___x_2824_; uint8_t v___x_2825_; 
v___x_2824_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__25));
v___x_2825_ = l_Lean_Expr_isAppOf(v_e_2312_, v___x_2824_);
if (v___x_2825_ == 0)
{
lean_object* v___x_2826_; uint8_t v___x_2827_; 
v___x_2826_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__27));
v___x_2827_ = l_Lean_Expr_isAppOf(v_e_2312_, v___x_2826_);
v___y_2680_ = v___x_2827_;
goto v___jp_2679_;
}
else
{
v___y_2680_ = v___x_2825_;
goto v___jp_2679_;
}
v___jp_2318_:
{
if (lean_obj_tag(v___y_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2328_; 
v_a_2320_ = lean_ctor_get(v___y_2319_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___y_2319_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2322_ = v___y_2319_;
v_isShared_2323_ = v_isSharedCheck_2328_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___y_2319_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2328_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v_a_2324_; lean_object* v___x_2326_; 
v_a_2324_ = lean_ctor_get(v_a_2320_, 0);
lean_inc(v_a_2324_);
lean_dec(v_a_2320_);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 0, v_a_2324_);
v___x_2326_ = v___x_2322_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2324_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
else
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2336_; 
v_a_2329_ = lean_ctor_get(v___y_2319_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___y_2319_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2331_ = v___y_2319_;
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___y_2319_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2334_; 
if (v_isShared_2332_ == 0)
{
v___x_2334_ = v___x_2331_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_a_2329_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
v___jp_2337_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = lean_box(0);
lean_inc(v_a_2316_);
lean_inc_ref(v_a_2315_);
lean_inc(v_a_2314_);
lean_inc_ref(v_a_2313_);
v___x_2340_ = lean_apply_6(v___y_2338_, v___x_2339_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, lean_box(0));
v___y_2319_ = v___x_2340_;
goto v___jp_2318_;
}
v___jp_2341_:
{
if (v___y_2346_ == 0)
{
lean_object* v_options_2347_; uint8_t v_hasTrace_2348_; 
v_options_2347_ = lean_ctor_get(v_a_2315_, 2);
v_hasTrace_2348_ = lean_ctor_get_uint8(v_options_2347_, sizeof(void*)*1);
if (v_hasTrace_2348_ == 0)
{
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec(v___y_2342_);
v___y_2338_ = v___y_2345_;
goto v___jp_2337_;
}
else
{
lean_object* v_inheritedTraceOptions_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; uint8_t v___x_2352_; 
v_inheritedTraceOptions_2349_ = lean_ctor_get(v_a_2315_, 13);
v___x_2350_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2343_);
v___x_2351_ = l_Lean_Name_append(v___x_2350_, v___y_2343_);
v___x_2352_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2349_, v_options_2347_, v___x_2351_);
lean_dec(v___x_2351_);
if (v___x_2352_ == 0)
{
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec(v___y_2342_);
v___y_2338_ = v___y_2345_;
goto v___jp_2337_;
}
else
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2353_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__3, &l_Lean_Meta_rwMatcher___closed__3_once, _init_l_Lean_Meta_rwMatcher___closed__3);
v___x_2354_ = l_Lean_MessageData_ofConstName(v___y_2342_, v___y_2346_);
v___x_2355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2353_);
lean_ctor_set(v___x_2355_, 1, v___x_2354_);
v___x_2356_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__5, &l_Lean_Meta_rwMatcher___closed__5_once, _init_l_Lean_Meta_rwMatcher___closed__5);
v___x_2357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2355_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
v___x_2358_ = l_Lean_Exception_toMessageData(v___y_2344_);
v___x_2359_ = l_Lean_indentD(v___x_2358_);
v___x_2360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2357_);
lean_ctor_set(v___x_2360_, 1, v___x_2359_);
v___x_2361_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2343_, v___x_2360_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2363_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2361_, 1);
lean_inc(v_a_2316_);
lean_inc_ref(v_a_2315_);
lean_inc(v_a_2314_);
lean_inc_ref(v_a_2313_);
v___x_2363_ = lean_apply_6(v___y_2345_, v_a_2362_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, lean_box(0));
v___y_2319_ = v___x_2363_;
goto v___jp_2318_;
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_dec_ref(v___y_2345_);
v_a_2364_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2361_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2361_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
}
}
else
{
lean_object* v___x_2372_; 
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2343_);
lean_dec(v___y_2342_);
v___x_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2372_, 0, v___y_2344_);
return v___x_2372_;
}
}
v___jp_2373_:
{
uint8_t v___x_2378_; 
v___x_2378_ = l_Lean_Exception_isInterrupt(v_a_2377_);
if (v___x_2378_ == 0)
{
uint8_t v___x_2379_; 
lean_inc_ref(v_a_2377_);
v___x_2379_ = l_Lean_Exception_isRuntime(v_a_2377_);
v___y_2342_ = v___y_2374_;
v___y_2343_ = v___y_2375_;
v___y_2344_ = v_a_2377_;
v___y_2345_ = v___y_2376_;
v___y_2346_ = v___x_2379_;
goto v___jp_2341_;
}
else
{
v___y_2342_ = v___y_2374_;
v___y_2343_ = v___y_2375_;
v___y_2344_ = v_a_2377_;
v___y_2345_ = v___y_2376_;
v___y_2346_ = v___x_2378_;
goto v___jp_2341_;
}
}
v___jp_2380_:
{
if (lean_obj_tag(v___y_2384_) == 0)
{
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec(v___y_2381_);
return v___y_2384_;
}
else
{
lean_object* v_a_2385_; 
v_a_2385_ = lean_ctor_get(v___y_2384_, 0);
lean_inc(v_a_2385_);
lean_dec_ref_known(v___y_2384_, 1);
v___y_2374_ = v___y_2381_;
v___y_2375_ = v___y_2382_;
v___y_2376_ = v___y_2383_;
v_a_2377_ = v_a_2385_;
goto v___jp_2373_;
}
}
v___jp_2386_:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2391_ = lean_box(0);
lean_inc(v_a_2316_);
lean_inc_ref(v_a_2315_);
lean_inc(v_a_2314_);
lean_inc_ref(v_a_2313_);
v___x_2392_ = lean_apply_6(v___y_2388_, v___x_2391_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, lean_box(0));
v___y_2381_ = v___y_2387_;
v___y_2382_ = v___y_2389_;
v___y_2383_ = v___y_2390_;
v___y_2384_ = v___x_2392_;
goto v___jp_2380_;
}
v___jp_2393_:
{
lean_object* v___x_2405_; double v___x_2406_; double v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2405_ = lean_io_get_num_heartbeats();
v___x_2406_ = lean_float_of_nat(v___y_2403_);
v___x_2407_ = lean_float_of_nat(v___x_2405_);
v___x_2408_ = lean_box_float(v___x_2406_);
v___x_2409_ = lean_box_float(v___x_2407_);
v___x_2410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2408_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2411_, 0, v_a_2404_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
lean_inc_ref(v___y_2397_);
lean_inc(v___y_2400_);
v___x_2412_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5(v___y_2400_, v___y_2401_, v___y_2397_, v___y_2398_, v___y_2395_, v___y_2399_, v___y_2394_, v___x_2411_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
v___y_2381_ = v___y_2396_;
v___y_2382_ = v___y_2400_;
v___y_2383_ = v___y_2402_;
v___y_2384_ = v___x_2412_;
goto v___jp_2380_;
}
v___jp_2413_:
{
lean_object* v___x_2425_; 
v___x_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2425_, 0, v_a_2424_);
v___y_2394_ = v___y_2414_;
v___y_2395_ = v___y_2415_;
v___y_2396_ = v___y_2416_;
v___y_2397_ = v___y_2417_;
v___y_2398_ = v___y_2418_;
v___y_2399_ = v___y_2419_;
v___y_2400_ = v___y_2420_;
v___y_2401_ = v___y_2421_;
v___y_2402_ = v___y_2423_;
v___y_2403_ = v___y_2422_;
v_a_2404_ = v___x_2425_;
goto v___jp_2393_;
}
v___jp_2426_:
{
if (lean_obj_tag(v___y_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2445_; 
v_a_2438_ = lean_ctor_get(v___y_2437_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___y_2437_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2440_ = v___y_2437_;
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___y_2437_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2443_; 
if (v_isShared_2441_ == 0)
{
lean_ctor_set_tag(v___x_2440_, 1);
v___x_2443_ = v___x_2440_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_a_2438_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
v___y_2394_ = v___y_2427_;
v___y_2395_ = v___y_2428_;
v___y_2396_ = v___y_2429_;
v___y_2397_ = v___y_2430_;
v___y_2398_ = v___y_2431_;
v___y_2399_ = v___y_2432_;
v___y_2400_ = v___y_2433_;
v___y_2401_ = v___y_2434_;
v___y_2402_ = v___y_2436_;
v___y_2403_ = v___y_2435_;
v_a_2404_ = v___x_2443_;
goto v___jp_2393_;
}
}
}
else
{
lean_object* v_a_2446_; 
v_a_2446_ = lean_ctor_get(v___y_2437_, 0);
lean_inc(v_a_2446_);
lean_dec_ref_known(v___y_2437_, 1);
v___y_2414_ = v___y_2427_;
v___y_2415_ = v___y_2428_;
v___y_2416_ = v___y_2429_;
v___y_2417_ = v___y_2430_;
v___y_2418_ = v___y_2431_;
v___y_2419_ = v___y_2432_;
v___y_2420_ = v___y_2433_;
v___y_2421_ = v___y_2434_;
v___y_2422_ = v___y_2435_;
v___y_2423_ = v___y_2436_;
v_a_2424_ = v_a_2446_;
goto v___jp_2413_;
}
}
v___jp_2447_:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = lean_box(0);
lean_inc(v_a_2316_);
lean_inc_ref(v_a_2315_);
lean_inc(v_a_2314_);
lean_inc_ref(v_a_2313_);
v___x_2460_ = lean_apply_6(v___y_2454_, v___x_2459_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, lean_box(0));
v___y_2427_ = v___y_2448_;
v___y_2428_ = v___y_2449_;
v___y_2429_ = v___y_2450_;
v___y_2430_ = v___y_2451_;
v___y_2431_ = v___y_2452_;
v___y_2432_ = v___y_2453_;
v___y_2433_ = v___y_2455_;
v___y_2434_ = v___y_2456_;
v___y_2435_ = v___y_2458_;
v___y_2436_ = v___y_2457_;
v___y_2437_ = v___x_2460_;
goto v___jp_2426_;
}
v___jp_2461_:
{
lean_object* v___x_2473_; double v___x_2474_; double v___x_2475_; double v___x_2476_; double v___x_2477_; double v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2473_ = lean_io_mono_nanos_now();
v___x_2474_ = lean_float_of_nat(v___y_2466_);
v___x_2475_ = lean_float_once(&l_Lean_Meta_rwMatcher___closed__6, &l_Lean_Meta_rwMatcher___closed__6_once, _init_l_Lean_Meta_rwMatcher___closed__6);
v___x_2476_ = lean_float_div(v___x_2474_, v___x_2475_);
v___x_2477_ = lean_float_of_nat(v___x_2473_);
v___x_2478_ = lean_float_div(v___x_2477_, v___x_2475_);
v___x_2479_ = lean_box_float(v___x_2476_);
v___x_2480_ = lean_box_float(v___x_2478_);
v___x_2481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2479_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
v___x_2482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2482_, 0, v_a_2472_);
lean_ctor_set(v___x_2482_, 1, v___x_2481_);
lean_inc_ref(v___y_2465_);
lean_inc(v___y_2469_);
v___x_2483_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5(v___y_2469_, v___y_2470_, v___y_2465_, v___y_2467_, v___y_2463_, v___y_2468_, v___y_2462_, v___x_2482_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
v___y_2381_ = v___y_2464_;
v___y_2382_ = v___y_2469_;
v___y_2383_ = v___y_2471_;
v___y_2384_ = v___x_2483_;
goto v___jp_2380_;
}
v___jp_2484_:
{
lean_object* v___x_2496_; 
v___x_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2496_, 0, v_a_2495_);
v___y_2462_ = v___y_2485_;
v___y_2463_ = v___y_2486_;
v___y_2464_ = v___y_2487_;
v___y_2465_ = v___y_2489_;
v___y_2466_ = v___y_2488_;
v___y_2467_ = v___y_2490_;
v___y_2468_ = v___y_2491_;
v___y_2469_ = v___y_2492_;
v___y_2470_ = v___y_2493_;
v___y_2471_ = v___y_2494_;
v_a_2472_ = v___x_2496_;
goto v___jp_2461_;
}
v___jp_2497_:
{
if (lean_obj_tag(v___y_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
v_a_2509_ = lean_ctor_get(v___y_2508_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___y_2508_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___y_2508_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___y_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
lean_ctor_set_tag(v___x_2511_, 1);
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
v___y_2462_ = v___y_2498_;
v___y_2463_ = v___y_2499_;
v___y_2464_ = v___y_2500_;
v___y_2465_ = v___y_2502_;
v___y_2466_ = v___y_2501_;
v___y_2467_ = v___y_2503_;
v___y_2468_ = v___y_2504_;
v___y_2469_ = v___y_2505_;
v___y_2470_ = v___y_2506_;
v___y_2471_ = v___y_2507_;
v_a_2472_ = v___x_2514_;
goto v___jp_2461_;
}
}
}
else
{
lean_object* v_a_2517_; 
v_a_2517_ = lean_ctor_get(v___y_2508_, 0);
lean_inc(v_a_2517_);
lean_dec_ref_known(v___y_2508_, 1);
v___y_2485_ = v___y_2498_;
v___y_2486_ = v___y_2499_;
v___y_2487_ = v___y_2500_;
v___y_2488_ = v___y_2501_;
v___y_2489_ = v___y_2502_;
v___y_2490_ = v___y_2503_;
v___y_2491_ = v___y_2504_;
v___y_2492_ = v___y_2505_;
v___y_2493_ = v___y_2506_;
v___y_2494_ = v___y_2507_;
v_a_2495_ = v_a_2517_;
goto v___jp_2484_;
}
}
v___jp_2518_:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = lean_box(0);
lean_inc(v_a_2316_);
lean_inc_ref(v_a_2315_);
lean_inc(v_a_2314_);
lean_inc_ref(v_a_2313_);
v___x_2531_ = lean_apply_6(v___y_2521_, v___x_2530_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, lean_box(0));
v___y_2498_ = v___y_2519_;
v___y_2499_ = v___y_2520_;
v___y_2500_ = v___y_2522_;
v___y_2501_ = v___y_2524_;
v___y_2502_ = v___y_2523_;
v___y_2503_ = v___y_2525_;
v___y_2504_ = v___y_2526_;
v___y_2505_ = v___y_2527_;
v___y_2506_ = v___y_2528_;
v___y_2507_ = v___y_2529_;
v___y_2508_ = v___x_2531_;
goto v___jp_2497_;
}
v___jp_2532_:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = lean_box(0);
lean_inc(v_a_2316_);
lean_inc_ref(v_a_2315_);
lean_inc(v_a_2314_);
lean_inc_ref(v_a_2313_);
v___x_2538_ = lean_apply_6(v___y_2536_, v___x_2537_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, lean_box(0));
v___y_2381_ = v___y_2533_;
v___y_2382_ = v___y_2534_;
v___y_2383_ = v___y_2535_;
v___y_2384_ = v___x_2538_;
goto v___jp_2380_;
}
v___jp_2539_:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2541_ = lean_box(0);
v___x_2542_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2542_, 0, v_e_2312_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
lean_ctor_set_uint8(v___x_2542_, sizeof(void*)*2, v___y_2540_);
v___x_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
return v___x_2543_;
}
v___jp_2544_:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2546_ = lean_box(0);
v___x_2547_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2547_, 0, v_e_2312_);
lean_ctor_set(v___x_2547_, 1, v___x_2546_);
lean_ctor_set_uint8(v___x_2547_, sizeof(void*)*2, v___y_2545_);
v___x_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2547_);
return v___x_2548_;
}
v___jp_2549_:
{
lean_object* v___x_2565_; lean_object* v_a_2566_; lean_object* v___x_2567_; uint8_t v___x_2568_; 
v___x_2565_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__3___redArg(v_a_2316_);
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec_ref(v___x_2565_);
v___x_2567_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2568_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__4(v___y_2559_, v___x_2567_);
if (v___x_2568_ == 0)
{
lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2569_ = lean_io_mono_nanos_now();
lean_inc(v_a_2316_);
lean_inc_ref(v_a_2315_);
lean_inc(v_a_2314_);
lean_inc_ref(v_a_2313_);
v___x_2570_ = lean_infer_type(v___y_2560_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v_a_2571_; uint8_t v___x_2572_; lean_object* v___x_2573_; 
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
lean_inc(v_a_2571_);
lean_dec_ref_known(v___x_2570_, 1);
v___x_2572_ = 0;
v___x_2573_ = l_Lean_Meta_forallMetaTelescope(v_a_2571_, v___x_2572_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; lean_object* v_snd_2575_; lean_object* v_fst_2576_; lean_object* v_snd_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2596_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_a_2574_);
lean_dec_ref_known(v___x_2573_, 1);
v_snd_2575_ = lean_ctor_get(v_a_2574_, 1);
lean_inc(v_snd_2575_);
v_fst_2576_ = lean_ctor_get(v_a_2574_, 0);
lean_inc(v_fst_2576_);
lean_dec(v_a_2574_);
v_snd_2577_ = lean_ctor_get(v_snd_2575_, 1);
v_isSharedCheck_2596_ = !lean_is_exclusive(v_snd_2575_);
if (v_isSharedCheck_2596_ == 0)
{
lean_object* v_unused_2597_; 
v_unused_2597_ = lean_ctor_get(v_snd_2575_, 0);
lean_dec(v_unused_2597_);
v___x_2579_ = v_snd_2575_;
v_isShared_2580_ = v_isSharedCheck_2596_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_snd_2577_);
lean_dec(v_snd_2575_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2596_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___f_2583_; 
v___x_2581_ = lean_box(v___y_2553_);
v___x_2582_ = lean_box(v___x_2568_);
lean_inc(v_snd_2577_);
lean_inc_ref(v_e_2312_);
lean_inc(v___y_2551_);
lean_inc(v_fst_2576_);
lean_inc_ref(v___y_2552_);
v___f_2583_ = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__2___boxed), 13, 7);
lean_closure_set(v___f_2583_, 0, v___x_2581_);
lean_closure_set(v___f_2583_, 1, v___y_2552_);
lean_closure_set(v___f_2583_, 2, v_fst_2576_);
lean_closure_set(v___f_2583_, 3, v___y_2551_);
lean_closure_set(v___f_2583_, 4, v___x_2582_);
lean_closure_set(v___f_2583_, 5, v_e_2312_);
lean_closure_set(v___f_2583_, 6, v_snd_2577_);
if (v___y_2554_ == 0)
{
lean_del_object(v___x_2579_);
lean_dec(v_snd_2577_);
lean_dec(v_fst_2576_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v_e_2312_);
v___y_2519_ = v___y_2555_;
v___y_2520_ = v___y_2556_;
v___y_2521_ = v___f_2583_;
v___y_2522_ = v___y_2557_;
v___y_2523_ = v___y_2558_;
v___y_2524_ = v___x_2569_;
v___y_2525_ = v___y_2559_;
v___y_2526_ = v_a_2566_;
v___y_2527_ = v___y_2562_;
v___y_2528_ = v___y_2563_;
v___y_2529_ = v___y_2564_;
goto v___jp_2518_;
}
else
{
lean_object* v___x_2584_; lean_object* v___x_2585_; uint8_t v___x_2586_; 
v___x_2584_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2562_);
v___x_2585_ = l_Lean_Name_append(v___x_2584_, v___y_2562_);
v___x_2586_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2561_, v___y_2559_, v___x_2585_);
lean_dec(v___x_2585_);
if (v___x_2586_ == 0)
{
lean_del_object(v___x_2579_);
lean_dec(v_snd_2577_);
lean_dec(v_fst_2576_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v_e_2312_);
v___y_2519_ = v___y_2555_;
v___y_2520_ = v___y_2556_;
v___y_2521_ = v___f_2583_;
v___y_2522_ = v___y_2557_;
v___y_2523_ = v___y_2558_;
v___y_2524_ = v___x_2569_;
v___y_2525_ = v___y_2559_;
v___y_2526_ = v_a_2566_;
v___y_2527_ = v___y_2562_;
v___y_2528_ = v___y_2563_;
v___y_2529_ = v___y_2564_;
goto v___jp_2518_;
}
else
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2590_; 
lean_dec_ref(v___f_2583_);
v___x_2587_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2577_);
v___x_2588_ = l_Lean_indentExpr(v_snd_2577_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set_tag(v___x_2579_, 7);
lean_ctor_set(v___x_2579_, 1, v___x_2588_);
lean_ctor_set(v___x_2579_, 0, v___x_2587_);
v___x_2590_ = v___x_2579_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2587_);
lean_ctor_set(v_reuseFailAlloc_2595_, 1, v___x_2588_);
v___x_2590_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
lean_object* v___x_2591_; 
lean_inc(v___y_2562_);
v___x_2591_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2562_, v___x_2590_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___x_2593_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref_known(v___x_2591_, 1);
v___x_2593_ = l_Lean_Meta_rwMatcher___lam__2(v___y_2553_, v___y_2552_, v_fst_2576_, v___y_2551_, v___x_2568_, v_e_2312_, v_snd_2577_, v_a_2592_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
lean_dec(v_snd_2577_);
v___y_2498_ = v___y_2555_;
v___y_2499_ = v___y_2556_;
v___y_2500_ = v___y_2557_;
v___y_2501_ = v___x_2569_;
v___y_2502_ = v___y_2558_;
v___y_2503_ = v___y_2559_;
v___y_2504_ = v_a_2566_;
v___y_2505_ = v___y_2562_;
v___y_2506_ = v___y_2563_;
v___y_2507_ = v___y_2564_;
v___y_2508_ = v___x_2593_;
goto v___jp_2497_;
}
else
{
lean_object* v_a_2594_; 
lean_dec(v_snd_2577_);
lean_dec(v_fst_2576_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v_e_2312_);
v_a_2594_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___x_2591_, 1);
v___y_2485_ = v___y_2555_;
v___y_2486_ = v___y_2556_;
v___y_2487_ = v___y_2557_;
v___y_2488_ = v___x_2569_;
v___y_2489_ = v___y_2558_;
v___y_2490_ = v___y_2559_;
v___y_2491_ = v_a_2566_;
v___y_2492_ = v___y_2562_;
v___y_2493_ = v___y_2563_;
v___y_2494_ = v___y_2564_;
v_a_2495_ = v_a_2594_;
goto v___jp_2484_;
}
}
}
}
}
}
else
{
lean_object* v_a_2598_; 
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v_e_2312_);
v_a_2598_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_a_2598_);
lean_dec_ref_known(v___x_2573_, 1);
v___y_2485_ = v___y_2555_;
v___y_2486_ = v___y_2556_;
v___y_2487_ = v___y_2557_;
v___y_2488_ = v___x_2569_;
v___y_2489_ = v___y_2558_;
v___y_2490_ = v___y_2559_;
v___y_2491_ = v_a_2566_;
v___y_2492_ = v___y_2562_;
v___y_2493_ = v___y_2563_;
v___y_2494_ = v___y_2564_;
v_a_2495_ = v_a_2598_;
goto v___jp_2484_;
}
}
else
{
lean_object* v_a_2599_; 
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v_e_2312_);
v_a_2599_ = lean_ctor_get(v___x_2570_, 0);
lean_inc(v_a_2599_);
lean_dec_ref_known(v___x_2570_, 1);
v___y_2485_ = v___y_2555_;
v___y_2486_ = v___y_2556_;
v___y_2487_ = v___y_2557_;
v___y_2488_ = v___x_2569_;
v___y_2489_ = v___y_2558_;
v___y_2490_ = v___y_2559_;
v___y_2491_ = v_a_2566_;
v___y_2492_ = v___y_2562_;
v___y_2493_ = v___y_2563_;
v___y_2494_ = v___y_2564_;
v_a_2495_ = v_a_2599_;
goto v___jp_2484_;
}
}
else
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2600_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2316_);
lean_inc_ref(v_a_2315_);
lean_inc(v_a_2314_);
lean_inc_ref(v_a_2313_);
v___x_2601_ = lean_infer_type(v___y_2560_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; uint8_t v___x_2603_; lean_object* v___x_2604_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_a_2602_);
lean_dec_ref_known(v___x_2601_, 1);
v___x_2603_ = 0;
v___x_2604_ = l_Lean_Meta_forallMetaTelescope(v_a_2602_, v___x_2603_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v_snd_2606_; lean_object* v_fst_2607_; lean_object* v_snd_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2627_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2605_);
lean_dec_ref_known(v___x_2604_, 1);
v_snd_2606_ = lean_ctor_get(v_a_2605_, 1);
lean_inc(v_snd_2606_);
v_fst_2607_ = lean_ctor_get(v_a_2605_, 0);
lean_inc(v_fst_2607_);
lean_dec(v_a_2605_);
v_snd_2608_ = lean_ctor_get(v_snd_2606_, 1);
v_isSharedCheck_2627_ = !lean_is_exclusive(v_snd_2606_);
if (v_isSharedCheck_2627_ == 0)
{
lean_object* v_unused_2628_; 
v_unused_2628_ = lean_ctor_get(v_snd_2606_, 0);
lean_dec(v_unused_2628_);
v___x_2610_ = v_snd_2606_;
v_isShared_2611_ = v_isSharedCheck_2627_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_snd_2608_);
lean_dec(v_snd_2606_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2627_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___f_2614_; 
v___x_2612_ = lean_box(v___y_2553_);
v___x_2613_ = lean_box(v___y_2550_);
lean_inc(v_snd_2608_);
lean_inc_ref(v_e_2312_);
lean_inc(v___y_2551_);
lean_inc(v_fst_2607_);
lean_inc_ref(v___y_2552_);
v___f_2614_ = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__3___boxed), 13, 7);
lean_closure_set(v___f_2614_, 0, v___x_2612_);
lean_closure_set(v___f_2614_, 1, v___y_2552_);
lean_closure_set(v___f_2614_, 2, v_fst_2607_);
lean_closure_set(v___f_2614_, 3, v___y_2551_);
lean_closure_set(v___f_2614_, 4, v___x_2613_);
lean_closure_set(v___f_2614_, 5, v_e_2312_);
lean_closure_set(v___f_2614_, 6, v_snd_2608_);
if (v___y_2554_ == 0)
{
lean_del_object(v___x_2610_);
lean_dec(v_snd_2608_);
lean_dec(v_fst_2607_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v_e_2312_);
v___y_2448_ = v___y_2555_;
v___y_2449_ = v___y_2556_;
v___y_2450_ = v___y_2557_;
v___y_2451_ = v___y_2558_;
v___y_2452_ = v___y_2559_;
v___y_2453_ = v_a_2566_;
v___y_2454_ = v___f_2614_;
v___y_2455_ = v___y_2562_;
v___y_2456_ = v___y_2563_;
v___y_2457_ = v___y_2564_;
v___y_2458_ = v___x_2600_;
goto v___jp_2447_;
}
else
{
lean_object* v___x_2615_; lean_object* v___x_2616_; uint8_t v___x_2617_; 
v___x_2615_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2562_);
v___x_2616_ = l_Lean_Name_append(v___x_2615_, v___y_2562_);
v___x_2617_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2561_, v___y_2559_, v___x_2616_);
lean_dec(v___x_2616_);
if (v___x_2617_ == 0)
{
lean_del_object(v___x_2610_);
lean_dec(v_snd_2608_);
lean_dec(v_fst_2607_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v_e_2312_);
v___y_2448_ = v___y_2555_;
v___y_2449_ = v___y_2556_;
v___y_2450_ = v___y_2557_;
v___y_2451_ = v___y_2558_;
v___y_2452_ = v___y_2559_;
v___y_2453_ = v_a_2566_;
v___y_2454_ = v___f_2614_;
v___y_2455_ = v___y_2562_;
v___y_2456_ = v___y_2563_;
v___y_2457_ = v___y_2564_;
v___y_2458_ = v___x_2600_;
goto v___jp_2447_;
}
else
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2621_; 
lean_dec_ref(v___f_2614_);
v___x_2618_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2608_);
v___x_2619_ = l_Lean_indentExpr(v_snd_2608_);
if (v_isShared_2611_ == 0)
{
lean_ctor_set_tag(v___x_2610_, 7);
lean_ctor_set(v___x_2610_, 1, v___x_2619_);
lean_ctor_set(v___x_2610_, 0, v___x_2618_);
v___x_2621_ = v___x_2610_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2618_);
lean_ctor_set(v_reuseFailAlloc_2626_, 1, v___x_2619_);
v___x_2621_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
lean_object* v___x_2622_; 
lean_inc(v___y_2562_);
v___x_2622_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2562_, v___x_2621_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2623_; lean_object* v___x_2624_; 
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
lean_inc(v_a_2623_);
lean_dec_ref_known(v___x_2622_, 1);
v___x_2624_ = l_Lean_Meta_rwMatcher___lam__3(v___y_2553_, v___y_2552_, v_fst_2607_, v___y_2551_, v___y_2550_, v_e_2312_, v_snd_2608_, v_a_2623_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
lean_dec(v_snd_2608_);
v___y_2427_ = v___y_2555_;
v___y_2428_ = v___y_2556_;
v___y_2429_ = v___y_2557_;
v___y_2430_ = v___y_2558_;
v___y_2431_ = v___y_2559_;
v___y_2432_ = v_a_2566_;
v___y_2433_ = v___y_2562_;
v___y_2434_ = v___y_2563_;
v___y_2435_ = v___x_2600_;
v___y_2436_ = v___y_2564_;
v___y_2437_ = v___x_2624_;
goto v___jp_2426_;
}
else
{
lean_object* v_a_2625_; 
lean_dec(v_snd_2608_);
lean_dec(v_fst_2607_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v_e_2312_);
v_a_2625_ = lean_ctor_get(v___x_2622_, 0);
lean_inc(v_a_2625_);
lean_dec_ref_known(v___x_2622_, 1);
v___y_2414_ = v___y_2555_;
v___y_2415_ = v___y_2556_;
v___y_2416_ = v___y_2557_;
v___y_2417_ = v___y_2558_;
v___y_2418_ = v___y_2559_;
v___y_2419_ = v_a_2566_;
v___y_2420_ = v___y_2562_;
v___y_2421_ = v___y_2563_;
v___y_2422_ = v___x_2600_;
v___y_2423_ = v___y_2564_;
v_a_2424_ = v_a_2625_;
goto v___jp_2413_;
}
}
}
}
}
}
else
{
lean_object* v_a_2629_; 
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v_e_2312_);
v_a_2629_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2629_);
lean_dec_ref_known(v___x_2604_, 1);
v___y_2414_ = v___y_2555_;
v___y_2415_ = v___y_2556_;
v___y_2416_ = v___y_2557_;
v___y_2417_ = v___y_2558_;
v___y_2418_ = v___y_2559_;
v___y_2419_ = v_a_2566_;
v___y_2420_ = v___y_2562_;
v___y_2421_ = v___y_2563_;
v___y_2422_ = v___x_2600_;
v___y_2423_ = v___y_2564_;
v_a_2424_ = v_a_2629_;
goto v___jp_2413_;
}
}
else
{
lean_object* v_a_2630_; 
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v_e_2312_);
v_a_2630_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_a_2630_);
lean_dec_ref_known(v___x_2601_, 1);
v___y_2414_ = v___y_2555_;
v___y_2415_ = v___y_2556_;
v___y_2416_ = v___y_2557_;
v___y_2417_ = v___y_2558_;
v___y_2418_ = v___y_2559_;
v___y_2419_ = v_a_2566_;
v___y_2420_ = v___y_2562_;
v___y_2421_ = v___y_2563_;
v___y_2422_ = v___x_2600_;
v___y_2423_ = v___y_2564_;
v_a_2424_ = v_a_2630_;
goto v___jp_2413_;
}
}
}
v___jp_2631_:
{
lean_object* v___x_2647_; uint8_t v___x_2648_; 
v___x_2647_ = l_Lean_trace_profiler;
v___x_2648_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__4(v___y_2640_, v___x_2647_);
if (v___x_2648_ == 0)
{
lean_object* v___x_2649_; 
lean_dec_ref(v___y_2633_);
lean_inc(v_a_2316_);
lean_inc_ref(v_a_2315_);
lean_inc(v_a_2314_);
lean_inc_ref(v_a_2313_);
v___x_2649_ = lean_infer_type(v___y_2641_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; uint8_t v___x_2651_; lean_object* v___x_2652_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2650_);
lean_dec_ref_known(v___x_2649_, 1);
v___x_2651_ = 0;
v___x_2652_ = l_Lean_Meta_forallMetaTelescope(v_a_2650_, v___x_2651_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v_snd_2654_; lean_object* v_fst_2655_; lean_object* v_snd_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2675_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
lean_dec_ref_known(v___x_2652_, 1);
v_snd_2654_ = lean_ctor_get(v_a_2653_, 1);
lean_inc(v_snd_2654_);
v_fst_2655_ = lean_ctor_get(v_a_2653_, 0);
lean_inc(v_fst_2655_);
lean_dec(v_a_2653_);
v_snd_2656_ = lean_ctor_get(v_snd_2654_, 1);
v_isSharedCheck_2675_ = !lean_is_exclusive(v_snd_2654_);
if (v_isSharedCheck_2675_ == 0)
{
lean_object* v_unused_2676_; 
v_unused_2676_ = lean_ctor_get(v_snd_2654_, 0);
lean_dec(v_unused_2676_);
v___x_2658_ = v_snd_2654_;
v_isShared_2659_ = v_isSharedCheck_2675_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_snd_2656_);
lean_dec(v_snd_2654_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2675_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___f_2662_; 
v___x_2660_ = lean_box(v___y_2636_);
v___x_2661_ = lean_box(v___x_2648_);
lean_inc(v_snd_2656_);
lean_inc_ref(v_e_2312_);
lean_inc(v___y_2634_);
lean_inc(v_fst_2655_);
lean_inc_ref(v___y_2635_);
v___f_2662_ = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__4___boxed), 13, 7);
lean_closure_set(v___f_2662_, 0, v___x_2660_);
lean_closure_set(v___f_2662_, 1, v___y_2635_);
lean_closure_set(v___f_2662_, 2, v_fst_2655_);
lean_closure_set(v___f_2662_, 3, v___y_2634_);
lean_closure_set(v___f_2662_, 4, v___x_2661_);
lean_closure_set(v___f_2662_, 5, v_e_2312_);
lean_closure_set(v___f_2662_, 6, v_snd_2656_);
if (v___y_2637_ == 0)
{
lean_del_object(v___x_2658_);
lean_dec(v_snd_2656_);
lean_dec(v_fst_2655_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v_e_2312_);
v___y_2533_ = v___y_2638_;
v___y_2534_ = v___y_2642_;
v___y_2535_ = v___y_2645_;
v___y_2536_ = v___f_2662_;
goto v___jp_2532_;
}
else
{
lean_object* v___x_2663_; lean_object* v___x_2664_; uint8_t v___x_2665_; 
v___x_2663_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2642_);
v___x_2664_ = l_Lean_Name_append(v___x_2663_, v___y_2642_);
v___x_2665_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2643_, v___y_2640_, v___x_2664_);
lean_dec(v___x_2664_);
if (v___x_2665_ == 0)
{
lean_del_object(v___x_2658_);
lean_dec(v_snd_2656_);
lean_dec(v_fst_2655_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v_e_2312_);
v___y_2533_ = v___y_2638_;
v___y_2534_ = v___y_2642_;
v___y_2535_ = v___y_2645_;
v___y_2536_ = v___f_2662_;
goto v___jp_2532_;
}
else
{
lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2669_; 
lean_dec_ref(v___f_2662_);
v___x_2666_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2656_);
v___x_2667_ = l_Lean_indentExpr(v_snd_2656_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set_tag(v___x_2658_, 7);
lean_ctor_set(v___x_2658_, 1, v___x_2667_);
lean_ctor_set(v___x_2658_, 0, v___x_2666_);
v___x_2669_ = v___x_2658_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2666_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v___x_2667_);
v___x_2669_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
lean_object* v___x_2670_; 
lean_inc(v___y_2642_);
v___x_2670_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2642_, v___x_2669_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; lean_object* v___x_2672_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2671_);
lean_dec_ref_known(v___x_2670_, 1);
v___x_2672_ = l_Lean_Meta_rwMatcher___lam__4(v___y_2636_, v___y_2635_, v_fst_2655_, v___y_2634_, v___x_2648_, v_e_2312_, v_snd_2656_, v_a_2671_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
lean_dec(v_snd_2656_);
v___y_2381_ = v___y_2638_;
v___y_2382_ = v___y_2642_;
v___y_2383_ = v___y_2645_;
v___y_2384_ = v___x_2672_;
goto v___jp_2380_;
}
else
{
lean_object* v_a_2673_; 
lean_dec(v_snd_2656_);
lean_dec(v_fst_2655_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v_e_2312_);
v_a_2673_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2673_);
lean_dec_ref_known(v___x_2670_, 1);
v___y_2374_ = v___y_2638_;
v___y_2375_ = v___y_2642_;
v___y_2376_ = v___y_2645_;
v_a_2377_ = v_a_2673_;
goto v___jp_2373_;
}
}
}
}
}
}
else
{
lean_object* v_a_2677_; 
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v_e_2312_);
v_a_2677_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v___x_2652_, 1);
v___y_2374_ = v___y_2638_;
v___y_2375_ = v___y_2642_;
v___y_2376_ = v___y_2645_;
v_a_2377_ = v_a_2677_;
goto v___jp_2373_;
}
}
else
{
lean_object* v_a_2678_; 
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v_e_2312_);
v_a_2678_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2678_);
lean_dec_ref_known(v___x_2649_, 1);
v___y_2374_ = v___y_2638_;
v___y_2375_ = v___y_2642_;
v___y_2376_ = v___y_2645_;
v_a_2377_ = v_a_2678_;
goto v___jp_2373_;
}
}
else
{
v___y_2550_ = v___y_2632_;
v___y_2551_ = v___y_2634_;
v___y_2552_ = v___y_2635_;
v___y_2553_ = v___y_2636_;
v___y_2554_ = v___y_2637_;
v___y_2555_ = v___y_2633_;
v___y_2556_ = v_a_2646_;
v___y_2557_ = v___y_2638_;
v___y_2558_ = v___y_2639_;
v___y_2559_ = v___y_2640_;
v___y_2560_ = v___y_2641_;
v___y_2561_ = v___y_2643_;
v___y_2562_ = v___y_2642_;
v___y_2563_ = v___y_2644_;
v___y_2564_ = v___y_2645_;
goto v___jp_2549_;
}
}
v___jp_2679_:
{
uint8_t v___x_2681_; 
v___x_2681_ = 1;
if (v___y_2680_ == 0)
{
lean_object* v___x_2682_; lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2804_; 
v___x_2682_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(v_e_2312_, v_a_2316_);
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2685_ = v___x_2682_;
v_isShared_2686_ = v_isSharedCheck_2804_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2682_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2804_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
uint8_t v___x_2687_; 
v___x_2687_ = lean_unbox(v_a_2683_);
lean_dec(v_a_2683_);
if (v___x_2687_ == 0)
{
lean_object* v_options_2688_; uint8_t v_hasTrace_2689_; 
lean_del_object(v___x_2685_);
lean_dec(v_altIdx_2311_);
v_options_2688_ = lean_ctor_get(v_a_2315_, 2);
v_hasTrace_2689_ = lean_ctor_get_uint8(v_options_2688_, sizeof(void*)*1);
if (v_hasTrace_2689_ == 0)
{
v___y_2545_ = v___x_2681_;
goto v___jp_2544_;
}
else
{
lean_object* v_inheritedTraceOptions_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; uint8_t v___x_2693_; 
v_inheritedTraceOptions_2690_ = lean_ctor_get(v_a_2315_, 13);
v___x_2691_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2692_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2693_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2690_, v_options_2688_, v___x_2692_);
if (v___x_2693_ == 0)
{
v___y_2545_ = v___x_2681_;
goto v___jp_2544_;
}
else
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2694_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__15, &l_Lean_Meta_rwMatcher___closed__15_once, _init_l_Lean_Meta_rwMatcher___closed__15);
lean_inc_ref(v_e_2312_);
v___x_2695_ = l_Lean_indentExpr(v_e_2312_);
v___x_2696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2694_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
v___x_2697_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2691_, v___x_2696_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_dec_ref_known(v___x_2697_, 1);
v___y_2545_ = v___x_2681_;
goto v___jp_2544_;
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
lean_dec_ref(v_e_2312_);
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2697_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2697_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2701_ == 0)
{
v___x_2703_ = v___x_2700_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
}
}
else
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2706_ = l_Lean_Expr_getAppFn(v_e_2312_);
v___x_2707_ = l_Lean_Expr_constName_x21(v___x_2706_);
lean_inc(v_a_2316_);
lean_inc_ref(v_a_2315_);
lean_inc(v_a_2314_);
lean_inc_ref(v_a_2313_);
lean_inc(v___x_2707_);
v___x_2708_ = lean_get_congr_match_equations_for(v___x_2707_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v_a_2709_; lean_object* v___x_2710_; uint8_t v___x_2711_; 
v_a_2709_ = lean_ctor_get(v___x_2708_, 0);
lean_inc(v_a_2709_);
lean_dec_ref_known(v___x_2708_, 1);
v___x_2710_ = lean_array_get_size(v_a_2709_);
v___x_2711_ = lean_nat_dec_lt(v_altIdx_2311_, v___x_2710_);
if (v___x_2711_ == 0)
{
lean_object* v_options_2712_; uint8_t v_hasTrace_2713_; 
lean_dec(v_a_2709_);
lean_dec_ref(v___x_2706_);
v_options_2712_ = lean_ctor_get(v_a_2315_, 2);
v_hasTrace_2713_ = lean_ctor_get_uint8(v_options_2712_, sizeof(void*)*1);
if (v_hasTrace_2713_ == 0)
{
lean_dec(v___x_2707_);
lean_del_object(v___x_2685_);
lean_dec(v_altIdx_2311_);
v___y_2540_ = v___x_2681_;
goto v___jp_2539_;
}
else
{
lean_object* v_inheritedTraceOptions_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; uint8_t v___x_2717_; 
v_inheritedTraceOptions_2714_ = lean_ctor_get(v_a_2315_, 13);
v___x_2715_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2716_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2717_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2714_, v_options_2712_, v___x_2716_);
if (v___x_2717_ == 0)
{
lean_dec(v___x_2707_);
lean_del_object(v___x_2685_);
lean_dec(v_altIdx_2311_);
v___y_2540_ = v___x_2681_;
goto v___jp_2539_;
}
else
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2721_; 
v___x_2718_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__17, &l_Lean_Meta_rwMatcher___closed__17_once, _init_l_Lean_Meta_rwMatcher___closed__17);
v___x_2719_ = l_Nat_reprFast(v_altIdx_2311_);
if (v_isShared_2686_ == 0)
{
lean_ctor_set_tag(v___x_2685_, 3);
lean_ctor_set(v___x_2685_, 0, v___x_2719_);
v___x_2721_ = v___x_2685_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2719_);
v___x_2721_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2722_ = l_Lean_MessageData_ofFormat(v___x_2721_);
v___x_2723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2718_);
lean_ctor_set(v___x_2723_, 1, v___x_2722_);
v___x_2724_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__19, &l_Lean_Meta_rwMatcher___closed__19_once, _init_l_Lean_Meta_rwMatcher___closed__19);
v___x_2725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2723_);
lean_ctor_set(v___x_2725_, 1, v___x_2724_);
v___x_2726_ = l_Nat_reprFast(v___x_2710_);
v___x_2727_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2726_);
v___x_2728_ = l_Lean_MessageData_ofFormat(v___x_2727_);
v___x_2729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2725_);
lean_ctor_set(v___x_2729_, 1, v___x_2728_);
v___x_2730_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__21, &l_Lean_Meta_rwMatcher___closed__21_once, _init_l_Lean_Meta_rwMatcher___closed__21);
v___x_2731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2729_);
lean_ctor_set(v___x_2731_, 1, v___x_2730_);
v___x_2732_ = l_Lean_MessageData_ofConstName(v___x_2707_, v___y_2680_);
v___x_2733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2731_);
lean_ctor_set(v___x_2733_, 1, v___x_2732_);
v___x_2734_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2715_, v___x_2733_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_dec_ref_known(v___x_2734_, 1);
v___y_2540_ = v___x_2681_;
goto v___jp_2539_;
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
lean_dec_ref(v_e_2312_);
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___x_2734_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2734_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2735_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
}
}
}
else
{
lean_object* v_options_2744_; lean_object* v_inheritedTraceOptions_2745_; uint8_t v_hasTrace_2746_; lean_object* v_nargs_2747_; lean_object* v___x_2748_; lean_object* v___f_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v_dummy_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; uint8_t v___x_2761_; 
lean_dec(v___x_2707_);
lean_del_object(v___x_2685_);
v_options_2744_ = lean_ctor_get(v_a_2315_, 2);
v_inheritedTraceOptions_2745_ = lean_ctor_get(v_a_2315_, 13);
v_hasTrace_2746_ = lean_ctor_get_uint8(v_options_2744_, sizeof(void*)*1);
v_nargs_2747_ = l_Lean_Expr_getAppNumArgs(v_e_2312_);
v___x_2748_ = lean_box(v___x_2681_);
lean_inc_ref_n(v_e_2312_, 2);
v___f_2749_ = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2749_, 0, v_e_2312_);
lean_closure_set(v___f_2749_, 1, v___x_2748_);
v___x_2750_ = lean_box(0);
v___x_2751_ = lean_array_get(v___x_2750_, v_a_2709_, v_altIdx_2311_);
lean_dec(v_altIdx_2311_);
lean_dec(v_a_2709_);
v___x_2752_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2753_ = l_Lean_Expr_constLevels_x21(v___x_2706_);
lean_dec_ref(v___x_2706_);
lean_inc(v___x_2751_);
v___x_2754_ = l_Lean_mkConst(v___x_2751_, v___x_2753_);
v_dummy_2755_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__22, &l_Lean_Meta_rwMatcher___closed__22_once, _init_l_Lean_Meta_rwMatcher___closed__22);
lean_inc(v_nargs_2747_);
v___x_2756_ = lean_mk_array(v_nargs_2747_, v_dummy_2755_);
v___x_2757_ = lean_unsigned_to_nat(1u);
v___x_2758_ = lean_nat_sub(v_nargs_2747_, v___x_2757_);
lean_dec(v_nargs_2747_);
v___x_2759_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2312_, v___x_2756_, v___x_2758_);
v___x_2760_ = l_Lean_mkAppN(v___x_2754_, v___x_2759_);
lean_dec_ref(v___x_2759_);
v___x_2761_ = lean_bool_not(v_hasTrace_2746_);
if (v___x_2761_ == 0)
{
lean_object* v___x_2762_; lean_object* v___f_2763_; lean_object* v___x_2764_; 
v___x_2762_ = lean_box(v___y_2680_);
lean_inc_ref(v_e_2312_);
lean_inc(v___x_2751_);
v___f_2763_ = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__1___boxed), 9, 3);
lean_closure_set(v___f_2763_, 0, v___x_2751_);
lean_closure_set(v___f_2763_, 1, v___x_2762_);
lean_closure_set(v___f_2763_, 2, v_e_2312_);
v___x_2764_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0));
if (v_hasTrace_2746_ == 0)
{
lean_inc_ref(v___x_2760_);
lean_inc(v___x_2751_);
v___y_2632_ = v___x_2761_;
v___y_2633_ = v___f_2763_;
v___y_2634_ = v___x_2751_;
v___y_2635_ = v___x_2760_;
v___y_2636_ = v___x_2681_;
v___y_2637_ = v_hasTrace_2746_;
v___y_2638_ = v___x_2751_;
v___y_2639_ = v___x_2764_;
v___y_2640_ = v_options_2744_;
v___y_2641_ = v___x_2760_;
v___y_2642_ = v___x_2752_;
v___y_2643_ = v_inheritedTraceOptions_2745_;
v___y_2644_ = v___x_2681_;
v___y_2645_ = v___f_2749_;
v_a_2646_ = v_hasTrace_2746_;
goto v___jp_2631_;
}
else
{
lean_object* v___x_2765_; uint8_t v___x_2766_; 
v___x_2765_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2766_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2745_, v_options_2744_, v___x_2765_);
if (v___x_2766_ == 0)
{
lean_inc_ref(v___x_2760_);
lean_inc(v___x_2751_);
v___y_2632_ = v___x_2761_;
v___y_2633_ = v___f_2763_;
v___y_2634_ = v___x_2751_;
v___y_2635_ = v___x_2760_;
v___y_2636_ = v___x_2681_;
v___y_2637_ = v_hasTrace_2746_;
v___y_2638_ = v___x_2751_;
v___y_2639_ = v___x_2764_;
v___y_2640_ = v_options_2744_;
v___y_2641_ = v___x_2760_;
v___y_2642_ = v___x_2752_;
v___y_2643_ = v_inheritedTraceOptions_2745_;
v___y_2644_ = v___x_2681_;
v___y_2645_ = v___f_2749_;
v_a_2646_ = v___x_2766_;
goto v___jp_2631_;
}
else
{
lean_inc_ref(v___x_2760_);
lean_inc(v___x_2751_);
v___y_2550_ = v___x_2761_;
v___y_2551_ = v___x_2751_;
v___y_2552_ = v___x_2760_;
v___y_2553_ = v___x_2681_;
v___y_2554_ = v_hasTrace_2746_;
v___y_2555_ = v___f_2763_;
v___y_2556_ = v___x_2766_;
v___y_2557_ = v___x_2751_;
v___y_2558_ = v___x_2764_;
v___y_2559_ = v_options_2744_;
v___y_2560_ = v___x_2760_;
v___y_2561_ = v_inheritedTraceOptions_2745_;
v___y_2562_ = v___x_2752_;
v___y_2563_ = v___x_2681_;
v___y_2564_ = v___f_2749_;
goto v___jp_2549_;
}
}
}
else
{
lean_object* v___x_2767_; 
lean_inc(v_a_2316_);
lean_inc_ref(v_a_2315_);
lean_inc(v_a_2314_);
lean_inc_ref(v_a_2313_);
lean_inc_ref(v___x_2760_);
v___x_2767_ = lean_infer_type(v___x_2760_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; uint8_t v___x_2769_; lean_object* v___x_2770_; 
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2768_);
lean_dec_ref_known(v___x_2767_, 1);
v___x_2769_ = 0;
v___x_2770_ = l_Lean_Meta_forallMetaTelescope(v_a_2768_, v___x_2769_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_a_2771_; lean_object* v_snd_2772_; lean_object* v_fst_2773_; lean_object* v_snd_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2792_; 
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
lean_inc(v_a_2771_);
lean_dec_ref_known(v___x_2770_, 1);
v_snd_2772_ = lean_ctor_get(v_a_2771_, 1);
lean_inc(v_snd_2772_);
v_fst_2773_ = lean_ctor_get(v_a_2771_, 0);
lean_inc(v_fst_2773_);
lean_dec(v_a_2771_);
v_snd_2774_ = lean_ctor_get(v_snd_2772_, 1);
v_isSharedCheck_2792_ = !lean_is_exclusive(v_snd_2772_);
if (v_isSharedCheck_2792_ == 0)
{
lean_object* v_unused_2793_; 
v_unused_2793_ = lean_ctor_get(v_snd_2772_, 0);
lean_dec(v_unused_2793_);
v___x_2776_ = v_snd_2772_;
v_isShared_2777_ = v_isSharedCheck_2792_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_snd_2774_);
lean_dec(v_snd_2772_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2792_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___f_2780_; 
v___x_2778_ = lean_box(v___x_2681_);
v___x_2779_ = lean_box(v___y_2680_);
lean_inc(v_snd_2774_);
lean_inc_ref(v_e_2312_);
lean_inc(v___x_2751_);
lean_inc(v_fst_2773_);
lean_inc_ref(v___x_2760_);
v___f_2780_ = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__5___boxed), 13, 7);
lean_closure_set(v___f_2780_, 0, v___x_2778_);
lean_closure_set(v___f_2780_, 1, v___x_2760_);
lean_closure_set(v___f_2780_, 2, v_fst_2773_);
lean_closure_set(v___f_2780_, 3, v___x_2751_);
lean_closure_set(v___f_2780_, 4, v_e_2312_);
lean_closure_set(v___f_2780_, 5, v___x_2779_);
lean_closure_set(v___f_2780_, 6, v_snd_2774_);
if (v_hasTrace_2746_ == 0)
{
lean_del_object(v___x_2776_);
lean_dec(v_snd_2774_);
lean_dec(v_fst_2773_);
lean_dec_ref(v___x_2760_);
lean_dec_ref(v_e_2312_);
v___y_2387_ = v___x_2751_;
v___y_2388_ = v___f_2780_;
v___y_2389_ = v___x_2752_;
v___y_2390_ = v___f_2749_;
goto v___jp_2386_;
}
else
{
lean_object* v___x_2781_; uint8_t v___x_2782_; 
v___x_2781_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2782_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2745_, v_options_2744_, v___x_2781_);
if (v___x_2782_ == 0)
{
lean_del_object(v___x_2776_);
lean_dec(v_snd_2774_);
lean_dec(v_fst_2773_);
lean_dec_ref(v___x_2760_);
lean_dec_ref(v_e_2312_);
v___y_2387_ = v___x_2751_;
v___y_2388_ = v___f_2780_;
v___y_2389_ = v___x_2752_;
v___y_2390_ = v___f_2749_;
goto v___jp_2386_;
}
else
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2786_; 
lean_dec_ref(v___f_2780_);
v___x_2783_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2774_);
v___x_2784_ = l_Lean_indentExpr(v_snd_2774_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set_tag(v___x_2776_, 7);
lean_ctor_set(v___x_2776_, 1, v___x_2784_);
lean_ctor_set(v___x_2776_, 0, v___x_2783_);
v___x_2786_ = v___x_2776_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v___x_2783_);
lean_ctor_set(v_reuseFailAlloc_2791_, 1, v___x_2784_);
v___x_2786_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
lean_object* v___x_2787_; 
v___x_2787_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2752_, v___x_2786_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2789_; 
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_a_2788_);
lean_dec_ref_known(v___x_2787_, 1);
lean_inc(v___x_2751_);
v___x_2789_ = l_Lean_Meta_rwMatcher___lam__5(v___x_2681_, v___x_2760_, v_fst_2773_, v___x_2751_, v_e_2312_, v___y_2680_, v_snd_2774_, v_a_2788_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
lean_dec(v_snd_2774_);
v___y_2381_ = v___x_2751_;
v___y_2382_ = v___x_2752_;
v___y_2383_ = v___f_2749_;
v___y_2384_ = v___x_2789_;
goto v___jp_2380_;
}
else
{
lean_object* v_a_2790_; 
lean_dec(v_snd_2774_);
lean_dec(v_fst_2773_);
lean_dec_ref(v___x_2760_);
lean_dec_ref(v_e_2312_);
v_a_2790_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v___x_2787_, 1);
v___y_2374_ = v___x_2751_;
v___y_2375_ = v___x_2752_;
v___y_2376_ = v___f_2749_;
v_a_2377_ = v_a_2790_;
goto v___jp_2373_;
}
}
}
}
}
}
else
{
lean_object* v_a_2794_; 
lean_dec_ref(v___x_2760_);
lean_dec_ref(v_e_2312_);
v_a_2794_ = lean_ctor_get(v___x_2770_, 0);
lean_inc(v_a_2794_);
lean_dec_ref_known(v___x_2770_, 1);
v___y_2374_ = v___x_2751_;
v___y_2375_ = v___x_2752_;
v___y_2376_ = v___f_2749_;
v_a_2377_ = v_a_2794_;
goto v___jp_2373_;
}
}
else
{
lean_object* v_a_2795_; 
lean_dec_ref(v___x_2760_);
lean_dec_ref(v_e_2312_);
v_a_2795_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2795_);
lean_dec_ref_known(v___x_2767_, 1);
v___y_2374_ = v___x_2751_;
v___y_2375_ = v___x_2752_;
v___y_2376_ = v___f_2749_;
v_a_2377_ = v_a_2795_;
goto v___jp_2373_;
}
}
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec(v___x_2707_);
lean_dec_ref(v___x_2706_);
lean_del_object(v___x_2685_);
lean_dec_ref(v_e_2312_);
lean_dec(v_altIdx_2311_);
v_a_2796_ = lean_ctor_get(v___x_2708_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2708_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2708_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
}
}
else
{
lean_object* v___x_2805_; 
lean_dec(v_altIdx_2311_);
v___x_2805_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(v_e_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2815_; 
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2808_ = v___x_2805_;
v_isShared_2809_ = v_isSharedCheck_2815_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2805_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2815_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2813_; 
v___x_2810_ = lean_box(0);
v___x_2811_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2811_, 0, v_a_2806_);
lean_ctor_set(v___x_2811_, 1, v___x_2810_);
lean_ctor_set_uint8(v___x_2811_, sizeof(void*)*2, v___x_2681_);
if (v_isShared_2809_ == 0)
{
lean_ctor_set(v___x_2808_, 0, v___x_2811_);
v___x_2813_ = v___x_2808_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v___x_2811_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
v_a_2816_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2805_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2805_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___boxed(lean_object* v_altIdx_2828_, lean_object* v_e_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l_Lean_Meta_rwMatcher(v_altIdx_2828_, v_e_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
lean_dec(v_a_2831_);
lean_dec_ref(v_a_2830_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(lean_object* v_mvarId_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
lean_object* v___x_2842_; 
v___x_2842_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_mvarId_2836_, v___y_2838_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___boxed(lean_object* v_mvarId_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(v_mvarId_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v_mvarId_2843_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__8(lean_object* v_00_u03b1_2850_, lean_object* v_x_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v___x_2857_; 
v___x_2857_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__8___redArg(v_x_2851_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__8___boxed(lean_object* v_00_u03b1_2858_, lean_object* v_x_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__5_spec__8(v_00_u03b1_2858_, v_x_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8(lean_object* v_00_u03b1_2866_, lean_object* v_msg_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v___x_2873_; 
v___x_2873_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___redArg(v_msg_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8___boxed(lean_object* v_00_u03b1_2874_, lean_object* v_msg_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__8(v_00_u03b1_2874_, v_msg_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12(lean_object* v_inst_2882_, lean_object* v_a_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v___x_2889_; 
v___x_2889_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(v_a_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___boxed(lean_object* v_inst_2890_, lean_object* v_a_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12(v_inst_2890_, v_a_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
return v_res_2897_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(lean_object* v_00_u03b2_2898_, lean_object* v_x_2899_, lean_object* v_x_2900_){
_start:
{
uint8_t v___x_2901_; 
v___x_2901_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_x_2899_, v_x_2900_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2902_, lean_object* v_x_2903_, lean_object* v_x_2904_){
_start:
{
uint8_t v_res_2905_; lean_object* v_r_2906_; 
v_res_2905_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(v_00_u03b2_2902_, v_x_2903_, v_x_2904_);
lean_dec(v_x_2904_);
lean_dec_ref(v_x_2903_);
v_r_2906_ = lean_box(v_res_2905_);
return v_r_2906_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5(lean_object* v_00_u03b2_2907_, lean_object* v_x_2908_, size_t v_x_2909_, lean_object* v_x_2910_){
_start:
{
uint8_t v___x_2911_; 
v___x_2911_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_2908_, v_x_2909_, v_x_2910_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b2_2912_, lean_object* v_x_2913_, lean_object* v_x_2914_, lean_object* v_x_2915_){
_start:
{
size_t v_x_110900__boxed_2916_; uint8_t v_res_2917_; lean_object* v_r_2918_; 
v_x_110900__boxed_2916_ = lean_unbox_usize(v_x_2914_);
lean_dec(v_x_2914_);
v_res_2917_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5(v_00_u03b2_2912_, v_x_2913_, v_x_110900__boxed_2916_, v_x_2915_);
lean_dec(v_x_2915_);
lean_dec_ref(v_x_2913_);
v_r_2918_ = lean_box(v_res_2917_);
return v_r_2918_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18(lean_object* v_00_u03b2_2919_, lean_object* v_keys_2920_, lean_object* v_vals_2921_, lean_object* v_heq_2922_, lean_object* v_i_2923_, lean_object* v_k_2924_){
_start:
{
uint8_t v___x_2925_; 
v___x_2925_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(v_keys_2920_, v_i_2923_, v_k_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___boxed(lean_object* v_00_u03b2_2926_, lean_object* v_keys_2927_, lean_object* v_vals_2928_, lean_object* v_heq_2929_, lean_object* v_i_2930_, lean_object* v_k_2931_){
_start:
{
uint8_t v_res_2932_; lean_object* v_r_2933_; 
v_res_2932_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18(v_00_u03b2_2926_, v_keys_2927_, v_vals_2928_, v_heq_2929_, v_i_2930_, v_k_2931_);
lean_dec(v_k_2931_);
lean_dec_ref(v_vals_2928_);
lean_dec_ref(v_keys_2927_);
v_r_2933_ = lean_box(v_res_2932_);
return v_r_2933_;
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
res = runtime_initialize_Lean_Meta_Tactic_Simp_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
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
res = initialize_Lean_Meta_Tactic_Simp_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Match_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Match_Rewrite(builtin);
}
#ifdef __cplusplus
}
#endif
