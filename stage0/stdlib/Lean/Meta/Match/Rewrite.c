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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Meta_isMatcherAppCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_io_mono_nanos_now();
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
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
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6_spec__21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Failed to resolve `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__0_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_rwMatcher___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "rewriting with "};
static const lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__1;
static const lean_string_object l_Lean_Meta_rwMatcher___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " in"};
static const lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__2 = (const lean_object*)&l_Lean_Meta_rwMatcher___lam__2___closed__2_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___lam__2___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__5(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_rwMatcher_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_rwMatcher_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__17___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15_spec__17(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_rwMatcher___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "eqProof has type"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__5 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__5_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__6;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__7 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__7_value;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Match"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__8 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__8_value;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__9 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__9_value;
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwMatcher___closed__7_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_rwMatcher___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_rwMatcher___closed__8_value),LEAN_SCALAR_PTR_LITERAL(250, 1, 225, 180, 135, 246, 184, 244)}};
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_rwMatcher___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_rwMatcher___closed__9_value),LEAN_SCALAR_PTR_LITERAL(253, 56, 25, 25, 156, 146, 62, 130)}};
static const lean_object* l_Lean_Meta_rwMatcher___closed__10 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__10_value;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Not a matcher application:"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__11 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__11_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__12;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "When trying to reduce arm "};
static const lean_object* l_Lean_Meta_rwMatcher___closed__13 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__13_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__14;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ", only "};
static const lean_object* l_Lean_Meta_rwMatcher___closed__15 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__15_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__16;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " equations for "};
static const lean_object* l_Lean_Meta_rwMatcher___closed__17 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__17_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__18;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__19;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "PSum"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__20 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__20_value;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "casesOn"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__21 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__21_value;
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwMatcher___closed__20_value),LEAN_SCALAR_PTR_LITERAL(147, 224, 206, 173, 168, 27, 198, 53)}};
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_rwMatcher___closed__22_value_aux_0),((lean_object*)&l_Lean_Meta_rwMatcher___closed__21_value),LEAN_SCALAR_PTR_LITERAL(166, 115, 173, 38, 27, 113, 160, 8)}};
static const lean_object* l_Lean_Meta_rwMatcher___closed__22 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__22_value;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "PSigma"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__23 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__23_value;
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwMatcher___closed__23_value),LEAN_SCALAR_PTR_LITERAL(0, 171, 149, 177, 120, 131, 37, 223)}};
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_rwMatcher___closed__24_value_aux_0),((lean_object*)&l_Lean_Meta_rwMatcher___closed__21_value),LEAN_SCALAR_PTR_LITERAL(225, 129, 3, 119, 45, 252, 168, 83)}};
static const lean_object* l_Lean_Meta_rwMatcher___closed__24 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__24_value;
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_57_);
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
lean_dec_ref(v___x_81_);
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
lean_dec_ref(v___x_90_);
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
lean_dec_ref(v___x_165_);
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
lean_dec_ref(v___x_174_);
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
lean_dec_ref(v___x_257_);
v___x_259_ = lean_obj_once(&l_Lean_Meta_rwIfWith___closed__17, &l_Lean_Meta_rwIfWith___closed__17_once, _init_l_Lean_Meta_rwIfWith___closed__17);
lean_inc_ref(v_arg_67_);
v___x_260_ = l_Lean_Meta_mkEq(v_arg_67_, v___x_259_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; lean_object* v___x_262_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_a_261_);
lean_dec_ref(v___x_260_);
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
lean_dec_ref(v___x_269_);
v___x_271_ = lean_obj_once(&l_Lean_Meta_rwIfWith___closed__20, &l_Lean_Meta_rwIfWith___closed__20_once, _init_l_Lean_Meta_rwIfWith___closed__20);
lean_inc_ref(v_arg_67_);
v___x_272_ = l_Lean_Meta_mkEq(v_arg_67_, v___x_271_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v_a_273_; lean_object* v___x_274_; 
v_a_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_a_273_);
lean_dec_ref(v___x_272_);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg(lean_object* v_cls_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_options_408_; uint8_t v_hasTrace_409_; 
v_options_408_ = lean_ctor_get(v___y_406_, 2);
v_hasTrace_409_ = lean_ctor_get_uint8(v_options_408_, sizeof(void*)*1);
if (v_hasTrace_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; 
lean_dec(v_cls_405_);
v___x_410_ = lean_box(v_hasTrace_409_);
v___x_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
return v___x_411_;
}
else
{
lean_object* v_inheritedTraceOptions_412_; lean_object* v___x_413_; lean_object* v___x_414_; uint8_t v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v_inheritedTraceOptions_412_ = lean_ctor_get(v___y_406_, 13);
v___x_413_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg___closed__1));
v___x_414_ = l_Lean_Name_append(v___x_413_, v_cls_405_);
v___x_415_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_412_, v_options_408_, v___x_414_);
lean_dec(v___x_414_);
v___x_416_ = lean_box(v___x_415_);
v___x_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
return v___x_417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg___boxed(lean_object* v_cls_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg(v_cls_418_, v___y_419_);
lean_dec_ref(v___y_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2(lean_object* v_cls_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg(v_cls_422_, v___y_425_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___boxed(lean_object* v_cls_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2(v_cls_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(lean_object* v_e_436_, lean_object* v___y_437_){
_start:
{
uint8_t v___x_439_; 
v___x_439_ = l_Lean_Expr_hasMVar(v_e_436_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; 
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v_e_436_);
return v___x_440_;
}
else
{
lean_object* v___x_441_; lean_object* v_mctx_442_; lean_object* v___x_443_; lean_object* v_fst_444_; lean_object* v_snd_445_; lean_object* v___x_446_; lean_object* v_cache_447_; lean_object* v_zetaDeltaFVarIds_448_; lean_object* v_postponed_449_; lean_object* v_diag_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_459_; 
v___x_441_ = lean_st_ref_get(v___y_437_);
v_mctx_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc_ref(v_mctx_442_);
lean_dec(v___x_441_);
v___x_443_ = l_Lean_instantiateMVarsCore(v_mctx_442_, v_e_436_);
v_fst_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_fst_444_);
v_snd_445_ = lean_ctor_get(v___x_443_, 1);
lean_inc(v_snd_445_);
lean_dec_ref(v___x_443_);
v___x_446_ = lean_st_ref_take(v___y_437_);
v_cache_447_ = lean_ctor_get(v___x_446_, 1);
v_zetaDeltaFVarIds_448_ = lean_ctor_get(v___x_446_, 2);
v_postponed_449_ = lean_ctor_get(v___x_446_, 3);
v_diag_450_ = lean_ctor_get(v___x_446_, 4);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_459_ == 0)
{
lean_object* v_unused_460_; 
v_unused_460_ = lean_ctor_get(v___x_446_, 0);
lean_dec(v_unused_460_);
v___x_452_ = v___x_446_;
v_isShared_453_ = v_isSharedCheck_459_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_diag_450_);
lean_inc(v_postponed_449_);
lean_inc(v_zetaDeltaFVarIds_448_);
lean_inc(v_cache_447_);
lean_dec(v___x_446_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_459_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v_snd_445_);
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_snd_445_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_cache_447_);
lean_ctor_set(v_reuseFailAlloc_458_, 2, v_zetaDeltaFVarIds_448_);
lean_ctor_set(v_reuseFailAlloc_458_, 3, v_postponed_449_);
lean_ctor_set(v_reuseFailAlloc_458_, 4, v_diag_450_);
v___x_455_ = v_reuseFailAlloc_458_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_st_ref_set(v___y_437_, v___x_455_);
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v_fst_444_);
return v___x_457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg___boxed(lean_object* v_e_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v_e_461_, v___y_462_);
lean_dec(v___y_462_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5(lean_object* v_e_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v_e_465_, v___y_467_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___boxed(lean_object* v_e_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5(v_e_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
return v_res_478_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = lean_unsigned_to_nat(32u);
v___x_480_ = lean_mk_empty_array_with_capacity(v___x_479_);
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
return v___x_481_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__1(void){
_start:
{
size_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_482_ = ((size_t)5ULL);
v___x_483_ = lean_unsigned_to_nat(0u);
v___x_484_ = lean_unsigned_to_nat(32u);
v___x_485_ = lean_mk_empty_array_with_capacity(v___x_484_);
v___x_486_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__0);
v___x_487_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v___x_485_);
lean_ctor_set(v___x_487_, 2, v___x_483_);
lean_ctor_set(v___x_487_, 3, v___x_483_);
lean_ctor_set_usize(v___x_487_, 4, v___x_482_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg(lean_object* v___y_488_){
_start:
{
lean_object* v___x_490_; lean_object* v_traceState_491_; lean_object* v_traces_492_; lean_object* v___x_493_; lean_object* v_traceState_494_; lean_object* v_env_495_; lean_object* v_nextMacroScope_496_; lean_object* v_ngen_497_; lean_object* v_auxDeclNGen_498_; lean_object* v_cache_499_; lean_object* v_messages_500_; lean_object* v_infoState_501_; lean_object* v_snapshotTasks_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_521_; 
v___x_490_ = lean_st_ref_get(v___y_488_);
v_traceState_491_ = lean_ctor_get(v___x_490_, 4);
lean_inc_ref(v_traceState_491_);
lean_dec(v___x_490_);
v_traces_492_ = lean_ctor_get(v_traceState_491_, 0);
lean_inc_ref(v_traces_492_);
lean_dec_ref(v_traceState_491_);
v___x_493_ = lean_st_ref_take(v___y_488_);
v_traceState_494_ = lean_ctor_get(v___x_493_, 4);
v_env_495_ = lean_ctor_get(v___x_493_, 0);
v_nextMacroScope_496_ = lean_ctor_get(v___x_493_, 1);
v_ngen_497_ = lean_ctor_get(v___x_493_, 2);
v_auxDeclNGen_498_ = lean_ctor_get(v___x_493_, 3);
v_cache_499_ = lean_ctor_get(v___x_493_, 5);
v_messages_500_ = lean_ctor_get(v___x_493_, 6);
v_infoState_501_ = lean_ctor_get(v___x_493_, 7);
v_snapshotTasks_502_ = lean_ctor_get(v___x_493_, 8);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_521_ == 0)
{
v___x_504_ = v___x_493_;
v_isShared_505_ = v_isSharedCheck_521_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_snapshotTasks_502_);
lean_inc(v_infoState_501_);
lean_inc(v_messages_500_);
lean_inc(v_cache_499_);
lean_inc(v_traceState_494_);
lean_inc(v_auxDeclNGen_498_);
lean_inc(v_ngen_497_);
lean_inc(v_nextMacroScope_496_);
lean_inc(v_env_495_);
lean_dec(v___x_493_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_521_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
uint64_t v_tid_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_519_; 
v_tid_506_ = lean_ctor_get_uint64(v_traceState_494_, sizeof(void*)*1);
v_isSharedCheck_519_ = !lean_is_exclusive(v_traceState_494_);
if (v_isSharedCheck_519_ == 0)
{
lean_object* v_unused_520_; 
v_unused_520_ = lean_ctor_get(v_traceState_494_, 0);
lean_dec(v_unused_520_);
v___x_508_ = v_traceState_494_;
v_isShared_509_ = v_isSharedCheck_519_;
goto v_resetjp_507_;
}
else
{
lean_dec(v_traceState_494_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_519_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_512_; 
v___x_510_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__1);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_510_);
v___x_512_ = v___x_508_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_510_);
lean_ctor_set_uint64(v_reuseFailAlloc_518_, sizeof(void*)*1, v_tid_506_);
v___x_512_ = v_reuseFailAlloc_518_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_514_; 
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 4, v___x_512_);
v___x_514_ = v___x_504_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_env_495_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_nextMacroScope_496_);
lean_ctor_set(v_reuseFailAlloc_517_, 2, v_ngen_497_);
lean_ctor_set(v_reuseFailAlloc_517_, 3, v_auxDeclNGen_498_);
lean_ctor_set(v_reuseFailAlloc_517_, 4, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_517_, 5, v_cache_499_);
lean_ctor_set(v_reuseFailAlloc_517_, 6, v_messages_500_);
lean_ctor_set(v_reuseFailAlloc_517_, 7, v_infoState_501_);
lean_ctor_set(v_reuseFailAlloc_517_, 8, v_snapshotTasks_502_);
v___x_514_ = v_reuseFailAlloc_517_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_st_ref_set(v___y_488_, v___x_514_);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v_traces_492_);
return v___x_516_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___boxed(lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg(v___y_522_);
lean_dec(v___y_522_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10(lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg(v___y_528_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___boxed(lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10(v___y_531_, v___y_532_, v___y_533_, v___y_534_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
return v_res_536_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11(lean_object* v_opts_537_, lean_object* v_opt_538_){
_start:
{
lean_object* v_name_539_; lean_object* v_defValue_540_; lean_object* v_map_541_; lean_object* v___x_542_; 
v_name_539_ = lean_ctor_get(v_opt_538_, 0);
v_defValue_540_ = lean_ctor_get(v_opt_538_, 1);
v_map_541_ = lean_ctor_get(v_opts_537_, 0);
v___x_542_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_541_, v_name_539_);
if (lean_obj_tag(v___x_542_) == 0)
{
uint8_t v___x_543_; 
v___x_543_ = lean_unbox(v_defValue_540_);
return v___x_543_;
}
else
{
lean_object* v_val_544_; 
v_val_544_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_val_544_);
lean_dec_ref(v___x_542_);
if (lean_obj_tag(v_val_544_) == 1)
{
uint8_t v_v_545_; 
v_v_545_ = lean_ctor_get_uint8(v_val_544_, 0);
lean_dec_ref(v_val_544_);
return v_v_545_;
}
else
{
uint8_t v___x_546_; 
lean_dec(v_val_544_);
v___x_546_ = lean_unbox(v_defValue_540_);
return v___x_546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11___boxed(lean_object* v_opts_547_, lean_object* v_opt_548_){
_start:
{
uint8_t v_res_549_; lean_object* v_r_550_; 
v_res_549_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11(v_opts_547_, v_opt_548_);
lean_dec_ref(v_opt_548_);
lean_dec_ref(v_opts_547_);
v_r_550_ = lean_box(v_res_549_);
return v_r_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__0(lean_object* v_e_551_, uint8_t v___x_552_, lean_object* v_____r_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_559_ = lean_box(0);
v___x_560_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_560_, 0, v_e_551_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
lean_ctor_set_uint8(v___x_560_, sizeof(void*)*2, v___x_552_);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__0___boxed(lean_object* v_e_563_, lean_object* v___x_564_, lean_object* v_____r_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
uint8_t v___x_98790__boxed_571_; lean_object* v_res_572_; 
v___x_98790__boxed_571_ = lean_unbox(v___x_564_);
v_res_572_ = l_Lean_Meta_rwMatcher___lam__0(v_e_563_, v___x_98790__boxed_571_, v_____r_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3_spec__4(lean_object* v_msgData_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v___x_579_; lean_object* v_env_580_; lean_object* v___x_581_; lean_object* v_mctx_582_; lean_object* v_lctx_583_; lean_object* v_options_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_579_ = lean_st_ref_get(v___y_577_);
v_env_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc_ref(v_env_580_);
lean_dec(v___x_579_);
v___x_581_ = lean_st_ref_get(v___y_575_);
v_mctx_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc_ref(v_mctx_582_);
lean_dec(v___x_581_);
v_lctx_583_ = lean_ctor_get(v___y_574_, 2);
v_options_584_ = lean_ctor_get(v___y_576_, 2);
lean_inc_ref(v_options_584_);
lean_inc_ref(v_lctx_583_);
v___x_585_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_585_, 0, v_env_580_);
lean_ctor_set(v___x_585_, 1, v_mctx_582_);
lean_ctor_set(v___x_585_, 2, v_lctx_583_);
lean_ctor_set(v___x_585_, 3, v_options_584_);
v___x_586_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v_msgData_573_);
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3_spec__4___boxed(lean_object* v_msgData_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3_spec__4(v_msgData_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(lean_object* v_msg_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v_ref_601_; lean_object* v___x_602_; lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_611_; 
v_ref_601_ = lean_ctor_get(v___y_598_, 5);
v___x_602_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3_spec__4(v_msg_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
v_a_603_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_611_ == 0)
{
v___x_605_ = v___x_602_;
v_isShared_606_ = v_isSharedCheck_611_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_602_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_611_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; lean_object* v___x_609_; 
lean_inc(v_ref_601_);
v___x_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_607_, 0, v_ref_601_);
lean_ctor_set(v___x_607_, 1, v_a_603_);
if (v_isShared_606_ == 0)
{
lean_ctor_set_tag(v___x_605_, 1);
lean_ctor_set(v___x_605_, 0, v___x_607_);
v___x_609_ = v___x_605_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg___boxed(lean_object* v_msg_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v_msg_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
return v_res_618_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6_spec__21___redArg(lean_object* v_keys_619_, lean_object* v_i_620_, lean_object* v_k_621_){
_start:
{
lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_622_ = lean_array_get_size(v_keys_619_);
v___x_623_ = lean_nat_dec_lt(v_i_620_, v___x_622_);
if (v___x_623_ == 0)
{
lean_dec(v_i_620_);
return v___x_623_;
}
else
{
lean_object* v_k_x27_624_; uint8_t v___x_625_; 
v_k_x27_624_ = lean_array_fget_borrowed(v_keys_619_, v_i_620_);
v___x_625_ = l_Lean_instBEqMVarId_beq(v_k_621_, v_k_x27_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = lean_nat_add(v_i_620_, v___x_626_);
lean_dec(v_i_620_);
v_i_620_ = v___x_627_;
goto _start;
}
else
{
lean_dec(v_i_620_);
return v___x_625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6_spec__21___redArg___boxed(lean_object* v_keys_629_, lean_object* v_i_630_, lean_object* v_k_631_){
_start:
{
uint8_t v_res_632_; lean_object* v_r_633_; 
v_res_632_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6_spec__21___redArg(v_keys_629_, v_i_630_, v_k_631_);
lean_dec(v_k_631_);
lean_dec_ref(v_keys_629_);
v_r_633_ = lean_box(v_res_632_);
return v_r_633_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___closed__0(void){
_start:
{
size_t v___x_634_; size_t v___x_635_; size_t v___x_636_; 
v___x_634_ = ((size_t)5ULL);
v___x_635_ = ((size_t)1ULL);
v___x_636_ = lean_usize_shift_left(v___x_635_, v___x_634_);
return v___x_636_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___closed__1(void){
_start:
{
size_t v___x_637_; size_t v___x_638_; size_t v___x_639_; 
v___x_637_ = ((size_t)1ULL);
v___x_638_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___closed__0);
v___x_639_ = lean_usize_sub(v___x_638_, v___x_637_);
return v___x_639_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg(lean_object* v_x_640_, size_t v_x_641_, lean_object* v_x_642_){
_start:
{
if (lean_obj_tag(v_x_640_) == 0)
{
lean_object* v_es_643_; lean_object* v___x_644_; size_t v___x_645_; size_t v___x_646_; size_t v___x_647_; lean_object* v_j_648_; lean_object* v___x_649_; 
v_es_643_ = lean_ctor_get(v_x_640_, 0);
lean_inc_ref(v_es_643_);
lean_dec_ref(v_x_640_);
v___x_644_ = lean_box(2);
v___x_645_ = ((size_t)5ULL);
v___x_646_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___closed__1);
v___x_647_ = lean_usize_land(v_x_641_, v___x_646_);
v_j_648_ = lean_usize_to_nat(v___x_647_);
v___x_649_ = lean_array_get(v___x_644_, v_es_643_, v_j_648_);
lean_dec(v_j_648_);
lean_dec_ref(v_es_643_);
switch(lean_obj_tag(v___x_649_))
{
case 0:
{
lean_object* v_key_650_; uint8_t v___x_651_; 
v_key_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_key_650_);
lean_dec_ref(v___x_649_);
v___x_651_ = l_Lean_instBEqMVarId_beq(v_x_642_, v_key_650_);
lean_dec(v_key_650_);
return v___x_651_;
}
case 1:
{
lean_object* v_node_652_; size_t v___x_653_; 
v_node_652_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_node_652_);
lean_dec_ref(v___x_649_);
v___x_653_ = lean_usize_shift_right(v_x_641_, v___x_645_);
v_x_640_ = v_node_652_;
v_x_641_ = v___x_653_;
goto _start;
}
default: 
{
uint8_t v___x_655_; 
v___x_655_ = 0;
return v___x_655_;
}
}
}
else
{
lean_object* v_ks_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v_ks_656_ = lean_ctor_get(v_x_640_, 0);
lean_inc_ref(v_ks_656_);
lean_dec_ref(v_x_640_);
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6_spec__21___redArg(v_ks_656_, v___x_657_, v_x_642_);
lean_dec_ref(v_ks_656_);
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg___boxed(lean_object* v_x_659_, lean_object* v_x_660_, lean_object* v_x_661_){
_start:
{
size_t v_x_98905__boxed_662_; uint8_t v_res_663_; lean_object* v_r_664_; 
v_x_98905__boxed_662_ = lean_unbox_usize(v_x_660_);
lean_dec(v_x_660_);
v_res_663_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg(v_x_659_, v_x_98905__boxed_662_, v_x_661_);
lean_dec(v_x_661_);
v_r_664_ = lean_box(v_res_663_);
return v_r_664_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(lean_object* v_x_665_, lean_object* v_x_666_){
_start:
{
uint64_t v___x_667_; size_t v___x_668_; uint8_t v___x_669_; 
v___x_667_ = l_Lean_instHashableMVarId_hash(v_x_666_);
v___x_668_ = lean_uint64_to_usize(v___x_667_);
v___x_669_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg(v_x_665_, v___x_668_, v_x_666_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg___boxed(lean_object* v_x_670_, lean_object* v_x_671_){
_start:
{
uint8_t v_res_672_; lean_object* v_r_673_; 
v_res_672_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_x_670_, v_x_671_);
lean_dec(v_x_671_);
v_r_673_ = lean_box(v_res_672_);
return v_r_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(lean_object* v_mvarId_674_, lean_object* v___y_675_){
_start:
{
lean_object* v___x_677_; lean_object* v_mctx_678_; lean_object* v_eAssignment_679_; uint8_t v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_677_ = lean_st_ref_get(v___y_675_);
v_mctx_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc_ref(v_mctx_678_);
lean_dec(v___x_677_);
v_eAssignment_679_ = lean_ctor_get(v_mctx_678_, 7);
lean_inc_ref(v_eAssignment_679_);
lean_dec_ref(v_mctx_678_);
v___x_680_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_eAssignment_679_, v_mvarId_674_);
v___x_681_ = lean_box(v___x_680_);
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg___boxed(lean_object* v_mvarId_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_mvarId_683_, v___y_684_);
lean_dec(v___y_684_);
lean_dec(v_mvarId_683_);
return v_res_686_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__0));
v___x_689_ = l_Lean_stringToMessageData(v___x_688_);
return v___x_689_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__2));
v___x_692_ = l_Lean_stringToMessageData(v___x_691_);
return v___x_692_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__5(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__4));
v___x_695_ = l_Lean_stringToMessageData(v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8(lean_object* v_as_696_, size_t v_sz_697_, size_t v_i_698_, lean_object* v_b_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_a_706_; uint8_t v___x_710_; 
v___x_710_ = lean_usize_dec_lt(v_i_698_, v_sz_697_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; 
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v_b_699_);
return v___x_711_;
}
else
{
lean_object* v_a_712_; lean_object* v___x_713_; 
v_a_712_ = lean_array_uget_borrowed(v_as_696_, v_i_698_);
v___x_713_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_a_712_, v___y_701_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_715_; lean_object* v___y_717_; lean_object* v___y_719_; lean_object* v___y_720_; uint8_t v___y_721_; lean_object* v___y_737_; lean_object* v___y_739_; lean_object* v___y_740_; uint8_t v___y_741_; lean_object* v___y_757_; uint8_t v___x_758_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_a_714_);
lean_dec_ref(v___x_713_);
v___x_715_ = lean_box(0);
v___x_758_ = lean_unbox(v_a_714_);
lean_dec(v_a_714_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; 
lean_inc(v_a_712_);
v___x_759_ = l_Lean_MVarId_getType(v_a_712_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; uint8_t v___x_761_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref(v___x_759_);
lean_inc(v_a_760_);
v___x_761_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_a_760_);
if (v___x_761_ == 0)
{
uint8_t v___x_762_; 
v___x_762_ = l_Lean_Expr_isEq(v_a_760_);
if (v___x_762_ == 0)
{
uint8_t v___x_763_; 
v___x_763_ = l_Lean_Expr_isHEq(v_a_760_);
lean_dec(v_a_760_);
if (v___x_763_ == 0)
{
v_a_706_ = v___x_715_;
goto v___jp_705_;
}
else
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_Meta_saveState___redArg(v___y_701_, v___y_703_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v___x_766_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
lean_dec_ref(v___x_764_);
lean_inc(v_a_712_);
v___x_766_ = l_Lean_MVarId_assumption(v_a_712_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_dec(v_a_765_);
v___y_737_ = v___x_766_;
goto v___jp_736_;
}
else
{
lean_object* v_a_767_; uint8_t v___y_769_; uint8_t v___x_785_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
v___x_785_ = l_Lean_Exception_isInterrupt(v_a_767_);
if (v___x_785_ == 0)
{
uint8_t v___x_786_; 
v___x_786_ = l_Lean_Exception_isRuntime(v_a_767_);
v___y_769_ = v___x_786_;
goto v___jp_768_;
}
else
{
lean_dec(v_a_767_);
v___y_769_ = v___x_785_;
goto v___jp_768_;
}
v___jp_768_:
{
if (v___y_769_ == 0)
{
lean_object* v___x_770_; 
lean_dec_ref(v___x_766_);
v___x_770_ = l_Lean_Meta_SavedState_restore___redArg(v_a_765_, v___y_701_, v___y_703_);
lean_dec(v_a_765_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v___x_771_; 
lean_dec_ref(v___x_770_);
v___x_771_ = l_Lean_Meta_saveState___redArg(v___y_701_, v___y_703_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v___x_773_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_a_772_);
lean_dec_ref(v___x_771_);
lean_inc(v_a_712_);
v___x_773_ = l_Lean_MVarId_hrefl(v_a_712_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_dec(v_a_772_);
v___y_737_ = v___x_773_;
goto v___jp_736_;
}
else
{
lean_object* v_a_774_; uint8_t v___x_775_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_774_);
v___x_775_ = l_Lean_Exception_isInterrupt(v_a_774_);
if (v___x_775_ == 0)
{
uint8_t v___x_776_; 
v___x_776_ = l_Lean_Exception_isRuntime(v_a_774_);
v___y_739_ = v_a_772_;
v___y_740_ = v___x_773_;
v___y_741_ = v___x_776_;
goto v___jp_738_;
}
else
{
lean_dec(v_a_774_);
v___y_739_ = v_a_772_;
v___y_740_ = v___x_773_;
v___y_741_ = v___x_775_;
goto v___jp_738_;
}
}
}
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
v_a_777_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_784_ == 0)
{
v___x_779_ = v___x_771_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_771_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
else
{
v___y_737_ = v___x_770_;
goto v___jp_736_;
}
}
else
{
lean_dec(v_a_765_);
v___y_737_ = v___x_766_;
goto v___jp_736_;
}
}
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
v_a_787_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_764_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_764_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
else
{
lean_object* v___x_795_; 
lean_dec(v_a_760_);
v___x_795_ = l_Lean_Meta_saveState___redArg(v___y_701_, v___y_703_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_797_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_a_796_);
lean_dec_ref(v___x_795_);
lean_inc(v_a_712_);
v___x_797_ = l_Lean_MVarId_assumption(v_a_712_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_dec(v_a_796_);
v___y_717_ = v___x_797_;
goto v___jp_716_;
}
else
{
lean_object* v_a_798_; uint8_t v___y_800_; uint8_t v___x_816_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
v___x_816_ = l_Lean_Exception_isInterrupt(v_a_798_);
if (v___x_816_ == 0)
{
uint8_t v___x_817_; 
v___x_817_ = l_Lean_Exception_isRuntime(v_a_798_);
v___y_800_ = v___x_817_;
goto v___jp_799_;
}
else
{
lean_dec(v_a_798_);
v___y_800_ = v___x_816_;
goto v___jp_799_;
}
v___jp_799_:
{
if (v___y_800_ == 0)
{
lean_object* v___x_801_; 
lean_dec_ref(v___x_797_);
v___x_801_ = l_Lean_Meta_SavedState_restore___redArg(v_a_796_, v___y_701_, v___y_703_);
lean_dec(v_a_796_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v___x_802_; 
lean_dec_ref(v___x_801_);
v___x_802_ = l_Lean_Meta_saveState___redArg(v___y_701_, v___y_703_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_804_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_803_);
lean_dec_ref(v___x_802_);
lean_inc(v_a_712_);
v___x_804_ = l_Lean_MVarId_refl(v_a_712_, v___x_762_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_dec(v_a_803_);
v___y_717_ = v___x_804_;
goto v___jp_716_;
}
else
{
lean_object* v_a_805_; uint8_t v___x_806_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_a_805_);
v___x_806_ = l_Lean_Exception_isInterrupt(v_a_805_);
if (v___x_806_ == 0)
{
uint8_t v___x_807_; 
v___x_807_ = l_Lean_Exception_isRuntime(v_a_805_);
v___y_719_ = v___x_804_;
v___y_720_ = v_a_803_;
v___y_721_ = v___x_807_;
goto v___jp_718_;
}
else
{
lean_dec(v_a_805_);
v___y_719_ = v___x_804_;
v___y_720_ = v_a_803_;
v___y_721_ = v___x_806_;
goto v___jp_718_;
}
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
v_a_808_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_802_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_802_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
else
{
v___y_717_ = v___x_801_;
goto v___jp_716_;
}
}
else
{
lean_dec(v_a_796_);
v___y_717_ = v___x_797_;
goto v___jp_716_;
}
}
}
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
v_a_818_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_795_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_795_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
else
{
lean_object* v___x_826_; 
lean_dec(v_a_760_);
v___x_826_ = l_Lean_Meta_saveState___redArg(v___y_701_, v___y_703_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v___x_828_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_a_827_);
lean_dec_ref(v___x_826_);
lean_inc(v_a_712_);
v___x_828_ = l_Lean_MVarId_assumption(v_a_712_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_dec(v_a_827_);
v___y_757_ = v___x_828_;
goto v___jp_756_;
}
else
{
lean_object* v_a_829_; uint8_t v___y_831_; uint8_t v___x_846_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_a_829_);
v___x_846_ = l_Lean_Exception_isInterrupt(v_a_829_);
if (v___x_846_ == 0)
{
uint8_t v___x_847_; 
v___x_847_ = l_Lean_Exception_isRuntime(v_a_829_);
v___y_831_ = v___x_847_;
goto v___jp_830_;
}
else
{
lean_dec(v_a_829_);
v___y_831_ = v___x_846_;
goto v___jp_830_;
}
v___jp_830_:
{
if (v___y_831_ == 0)
{
lean_object* v___x_832_; 
lean_dec_ref(v___x_828_);
v___x_832_ = l_Lean_Meta_SavedState_restore___redArg(v_a_827_, v___y_701_, v___y_703_);
lean_dec(v_a_827_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_844_; 
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_844_ == 0)
{
lean_object* v_unused_845_; 
v_unused_845_ = lean_ctor_get(v___x_832_, 0);
lean_dec(v_unused_845_);
v___x_834_ = v___x_832_;
v_isShared_835_ = v_isSharedCheck_844_;
goto v_resetjp_833_;
}
else
{
lean_dec(v___x_832_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_844_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_836_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__5);
lean_inc(v_a_712_);
if (v_isShared_835_ == 0)
{
lean_ctor_set_tag(v___x_834_, 1);
lean_ctor_set(v___x_834_, 0, v_a_712_);
v___x_838_ = v___x_834_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_712_);
v___x_838_ = v_reuseFailAlloc_843_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_836_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
v___x_841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_839_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_841_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
v___y_757_ = v___x_842_;
goto v___jp_756_;
}
}
}
else
{
v___y_757_ = v___x_832_;
goto v___jp_756_;
}
}
else
{
lean_dec(v_a_827_);
v___y_757_ = v___x_828_;
goto v___jp_756_;
}
}
}
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
v_a_848_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_826_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_826_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
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
}
else
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
v_a_856_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_759_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_759_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_856_);
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
v_a_706_ = v___x_715_;
goto v___jp_705_;
}
v___jp_716_:
{
if (lean_obj_tag(v___y_717_) == 0)
{
lean_dec_ref(v___y_717_);
v_a_706_ = v___x_715_;
goto v___jp_705_;
}
else
{
return v___y_717_;
}
}
v___jp_718_:
{
if (v___y_721_ == 0)
{
lean_object* v___x_722_; 
lean_dec_ref(v___y_719_);
v___x_722_ = l_Lean_Meta_SavedState_restore___redArg(v___y_720_, v___y_701_, v___y_703_);
lean_dec_ref(v___y_720_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_734_; 
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_734_ == 0)
{
lean_object* v_unused_735_; 
v_unused_735_ = lean_ctor_get(v___x_722_, 0);
lean_dec(v_unused_735_);
v___x_724_ = v___x_722_;
v_isShared_725_ = v_isSharedCheck_734_;
goto v_resetjp_723_;
}
else
{
lean_dec(v___x_722_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_734_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_726_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1);
lean_inc(v_a_712_);
if (v_isShared_725_ == 0)
{
lean_ctor_set_tag(v___x_724_, 1);
lean_ctor_set(v___x_724_, 0, v_a_712_);
v___x_728_ = v___x_724_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_712_);
v___x_728_ = v_reuseFailAlloc_733_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_726_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
v___x_731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_729_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_731_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
v___y_717_ = v___x_732_;
goto v___jp_716_;
}
}
}
else
{
v___y_717_ = v___x_722_;
goto v___jp_716_;
}
}
else
{
lean_dec_ref(v___y_720_);
v___y_717_ = v___y_719_;
goto v___jp_716_;
}
}
v___jp_736_:
{
if (lean_obj_tag(v___y_737_) == 0)
{
lean_dec_ref(v___y_737_);
v_a_706_ = v___x_715_;
goto v___jp_705_;
}
else
{
return v___y_737_;
}
}
v___jp_738_:
{
if (v___y_741_ == 0)
{
lean_object* v___x_742_; 
lean_dec_ref(v___y_740_);
v___x_742_ = l_Lean_Meta_SavedState_restore___redArg(v___y_739_, v___y_701_, v___y_703_);
lean_dec_ref(v___y_739_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_754_; 
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; 
v_unused_755_ = lean_ctor_get(v___x_742_, 0);
lean_dec(v_unused_755_);
v___x_744_ = v___x_742_;
v_isShared_745_ = v_isSharedCheck_754_;
goto v_resetjp_743_;
}
else
{
lean_dec(v___x_742_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_754_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_746_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1);
lean_inc(v_a_712_);
if (v_isShared_745_ == 0)
{
lean_ctor_set_tag(v___x_744_, 1);
lean_ctor_set(v___x_744_, 0, v_a_712_);
v___x_748_ = v___x_744_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_712_);
v___x_748_ = v_reuseFailAlloc_753_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_746_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
v___x_751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_749_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_751_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
v___y_737_ = v___x_752_;
goto v___jp_736_;
}
}
}
else
{
v___y_737_ = v___x_742_;
goto v___jp_736_;
}
}
else
{
lean_dec_ref(v___y_739_);
v___y_737_ = v___y_740_;
goto v___jp_736_;
}
}
v___jp_756_:
{
if (lean_obj_tag(v___y_757_) == 0)
{
lean_dec_ref(v___y_757_);
v_a_706_ = v___x_715_;
goto v___jp_705_;
}
else
{
return v___y_757_;
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
v_a_864_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_713_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_713_);
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
v___jp_705_:
{
size_t v___x_707_; size_t v___x_708_; 
v___x_707_ = ((size_t)1ULL);
v___x_708_ = lean_usize_add(v_i_698_, v___x_707_);
v_i_698_ = v___x_708_;
v_b_699_ = v_a_706_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___boxed(lean_object* v_as_872_, lean_object* v_sz_873_, lean_object* v_i_874_, lean_object* v_b_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
size_t v_sz_boxed_881_; size_t v_i_boxed_882_; lean_object* v_res_883_; 
v_sz_boxed_881_ = lean_unbox_usize(v_sz_873_);
lean_dec(v_sz_873_);
v_i_boxed_882_ = lean_unbox_usize(v_i_874_);
lean_dec(v_i_874_);
v_res_883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8(v_as_872_, v_sz_boxed_881_, v_i_boxed_882_, v_b_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec_ref(v_as_872_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9(lean_object* v_as_884_, size_t v_i_885_, size_t v_stop_886_, lean_object* v_b_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_a_894_; uint8_t v___x_898_; 
v___x_898_ = lean_usize_dec_eq(v_i_885_, v_stop_886_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; lean_object* v___x_902_; 
v___x_899_ = lean_array_uget_borrowed(v_as_884_, v_i_885_);
v___x_902_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v___x_899_, v___y_889_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; uint8_t v___x_904_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref(v___x_902_);
v___x_904_ = lean_unbox(v_a_903_);
lean_dec(v_a_903_);
if (v___x_904_ == 0)
{
goto v___jp_900_;
}
else
{
v_a_894_ = v_b_887_;
goto v___jp_893_;
}
}
else
{
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_905_; uint8_t v___x_906_; 
v_a_905_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_905_);
lean_dec_ref(v___x_902_);
v___x_906_ = lean_unbox(v_a_905_);
lean_dec(v_a_905_);
if (v___x_906_ == 0)
{
v_a_894_ = v_b_887_;
goto v___jp_893_;
}
else
{
goto v___jp_900_;
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_dec_ref(v_b_887_);
v_a_907_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_902_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_902_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
v___jp_900_:
{
lean_object* v___x_901_; 
lean_inc(v___x_899_);
v___x_901_ = lean_array_push(v_b_887_, v___x_899_);
v_a_894_ = v___x_901_;
goto v___jp_893_;
}
}
else
{
lean_object* v___x_915_; 
v___x_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_915_, 0, v_b_887_);
return v___x_915_;
}
v___jp_893_:
{
size_t v___x_895_; size_t v___x_896_; 
v___x_895_ = ((size_t)1ULL);
v___x_896_ = lean_usize_add(v_i_885_, v___x_895_);
v_i_885_ = v___x_896_;
v_b_887_ = v_a_894_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9___boxed(lean_object* v_as_916_, lean_object* v_i_917_, lean_object* v_stop_918_, lean_object* v_b_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
size_t v_i_boxed_925_; size_t v_stop_boxed_926_; lean_object* v_res_927_; 
v_i_boxed_925_ = lean_unbox_usize(v_i_917_);
lean_dec(v_i_917_);
v_stop_boxed_926_ = lean_unbox_usize(v_stop_918_);
lean_dec(v_stop_918_);
v_res_927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9(v_as_916_, v_i_boxed_925_, v_stop_boxed_926_, v_b_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec_ref(v_as_916_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4(size_t v_sz_928_, size_t v_i_929_, lean_object* v_bs_930_){
_start:
{
uint8_t v___x_931_; 
v___x_931_ = lean_usize_dec_lt(v_i_929_, v_sz_928_);
if (v___x_931_ == 0)
{
return v_bs_930_;
}
else
{
lean_object* v_v_932_; lean_object* v___x_933_; lean_object* v_bs_x27_934_; lean_object* v___x_935_; size_t v___x_936_; size_t v___x_937_; lean_object* v___x_938_; 
v_v_932_ = lean_array_uget(v_bs_930_, v_i_929_);
v___x_933_ = lean_unsigned_to_nat(0u);
v_bs_x27_934_ = lean_array_uset(v_bs_930_, v_i_929_, v___x_933_);
v___x_935_ = l_Lean_Expr_mvarId_x21(v_v_932_);
lean_dec(v_v_932_);
v___x_936_ = ((size_t)1ULL);
v___x_937_ = lean_usize_add(v_i_929_, v___x_936_);
v___x_938_ = lean_array_uset(v_bs_x27_934_, v_i_929_, v___x_935_);
v_i_929_ = v___x_937_;
v_bs_930_ = v___x_938_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4___boxed(lean_object* v_sz_940_, lean_object* v_i_941_, lean_object* v_bs_942_){
_start:
{
size_t v_sz_boxed_943_; size_t v_i_boxed_944_; lean_object* v_res_945_; 
v_sz_boxed_943_ = lean_unbox_usize(v_sz_940_);
lean_dec(v_sz_940_);
v_i_boxed_944_ = lean_unbox_usize(v_i_941_);
lean_dec(v_i_941_);
v_res_945_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4(v_sz_boxed_943_, v_i_boxed_944_, v_bs_942_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__7(lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
if (lean_obj_tag(v_a_946_) == 0)
{
lean_object* v___x_948_; 
v___x_948_ = l_List_reverse___redArg(v_a_947_);
return v___x_948_;
}
else
{
lean_object* v_head_949_; lean_object* v_tail_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_959_; 
v_head_949_ = lean_ctor_get(v_a_946_, 0);
v_tail_950_ = lean_ctor_get(v_a_946_, 1);
v_isSharedCheck_959_ = !lean_is_exclusive(v_a_946_);
if (v_isSharedCheck_959_ == 0)
{
v___x_952_ = v_a_946_;
v_isShared_953_ = v_isSharedCheck_959_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_tail_950_);
lean_inc(v_head_949_);
lean_dec(v_a_946_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_959_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_954_; lean_object* v___x_956_; 
v___x_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_954_, 0, v_head_949_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 1, v_a_947_);
lean_ctor_set(v___x_952_, 0, v___x_954_);
v___x_956_ = v___x_952_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_954_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_a_947_);
v___x_956_ = v_reuseFailAlloc_958_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
v_a_946_ = v_tail_950_;
v_a_947_ = v___x_956_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__1(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__0));
v___x_962_ = l_Lean_stringToMessageData(v___x_961_);
return v___x_962_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__3(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__2));
v___x_965_ = l_Lean_stringToMessageData(v___x_964_);
return v___x_965_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__5(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__4));
v___x_968_ = l_Lean_stringToMessageData(v___x_967_);
return v___x_968_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__7(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__6));
v___x_971_ = l_Lean_stringToMessageData(v___x_970_);
return v___x_971_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__9(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__8));
v___x_974_ = l_Lean_stringToMessageData(v___x_973_);
return v___x_974_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__12(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__11));
v___x_979_ = l_Lean_stringToMessageData(v___x_978_);
return v___x_979_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__14(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__13));
v___x_982_ = l_Lean_stringToMessageData(v___x_981_);
return v___x_982_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__16(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__15));
v___x_985_ = l_Lean_stringToMessageData(v___x_984_);
return v___x_985_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__22(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__21));
v___x_994_ = l_Lean_stringToMessageData(v___x_993_);
return v___x_994_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__24(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__23));
v___x_997_ = l_Lean_stringToMessageData(v___x_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__1(uint8_t v___x_998_, lean_object* v___x_999_, lean_object* v_fst_1000_, lean_object* v___x_1001_, uint8_t v_hasTrace_1002_, lean_object* v_e_1003_, lean_object* v_snd_1004_, lean_object* v_____r_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v___y_1012_; lean_object* v_proof_1013_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; uint8_t v___y_1038_; lean_object* v___x_1050_; lean_object* v___y_1052_; uint8_t v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; uint8_t v___y_1073_; lean_object* v_a_1074_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; uint8_t v___y_1103_; lean_object* v___y_1104_; size_t v_sz_1114_; size_t v___x_1115_; lean_object* v___x_1116_; lean_object* v___y_1118_; uint8_t v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; uint8_t v_fst_1145_; lean_object* v_fst_1146_; lean_object* v_snd_1147_; lean_object* v___x_1181_; lean_object* v___x_1182_; uint8_t v___x_1183_; 
v___x_1050_ = l_Lean_mkAppN(v___x_999_, v_fst_1000_);
v_sz_1114_ = lean_array_size(v_fst_1000_);
v___x_1115_ = ((size_t)0ULL);
v___x_1116_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4(v_sz_1114_, v___x_1115_, v_fst_1000_);
v___x_1181_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__18));
v___x_1182_ = lean_unsigned_to_nat(4u);
v___x_1183_ = l_Lean_Expr_isAppOfArity(v_snd_1004_, v___x_1181_, v___x_1182_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; 
v___x_1184_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__20));
v___x_1185_ = lean_unsigned_to_nat(3u);
v___x_1186_ = l_Lean_Expr_isAppOfArity(v_snd_1004_, v___x_1184_, v___x_1185_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec_ref(v___x_1116_);
lean_dec_ref(v___x_1050_);
lean_dec_ref(v_e_1003_);
v___x_1187_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__22, &l_Lean_Meta_rwMatcher___lam__1___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__22);
v___x_1188_ = l_Lean_MessageData_ofConstName(v___x_1001_, v_hasTrace_1002_);
v___x_1189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__24, &l_Lean_Meta_rwMatcher___lam__1___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__24);
v___x_1191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
v___x_1192_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1191_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
else
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1201_ = l_Lean_Expr_appFn_x21(v_snd_1004_);
v___x_1202_ = l_Lean_Expr_appArg_x21(v___x_1201_);
lean_dec_ref(v___x_1201_);
v___x_1203_ = l_Lean_Expr_appArg_x21(v_snd_1004_);
v_fst_1145_ = v_hasTrace_1002_;
v_fst_1146_ = v___x_1202_;
v_snd_1147_ = v___x_1203_;
goto v___jp_1144_;
}
}
else
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1204_ = l_Lean_Expr_appFn_x21(v_snd_1004_);
v___x_1205_ = l_Lean_Expr_appFn_x21(v___x_1204_);
lean_dec_ref(v___x_1204_);
v___x_1206_ = l_Lean_Expr_appArg_x21(v___x_1205_);
lean_dec_ref(v___x_1205_);
v___x_1207_ = l_Lean_Expr_appArg_x21(v_snd_1004_);
v_fst_1145_ = v___x_998_;
v_fst_1146_ = v___x_1206_;
v_snd_1147_ = v___x_1207_;
goto v___jp_1144_;
}
v___jp_1011_:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1014_, 0, v_proof_1013_);
v___x_1015_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1015_, 0, v___y_1012_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
lean_ctor_set_uint8(v___x_1015_, sizeof(void*)*2, v___x_998_);
v___x_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
return v___x_1016_;
}
v___jp_1017_:
{
if (lean_obj_tag(v___y_1019_) == 0)
{
lean_object* v_a_1020_; 
v_a_1020_ = lean_ctor_get(v___y_1019_, 0);
lean_inc(v_a_1020_);
lean_dec_ref(v___y_1019_);
v___y_1012_ = v___y_1018_;
v_proof_1013_ = v_a_1020_;
goto v___jp_1011_;
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_dec_ref(v___y_1018_);
v_a_1021_ = lean_ctor_get(v___y_1019_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___y_1019_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___y_1019_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___y_1019_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
v___jp_1029_:
{
if (v___y_1038_ == 0)
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
lean_dec_ref(v___y_1033_);
v___x_1039_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__1, &l_Lean_Meta_rwMatcher___lam__1___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__1);
v___x_1040_ = l_Lean_MessageData_ofExpr(v___y_1034_);
v___x_1041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1039_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__3, &l_Lean_Meta_rwMatcher___lam__1___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__3);
v___x_1043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1041_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = l_Lean_Exception_toMessageData(v___y_1036_);
v___x_1045_ = l_Lean_indentD(v___x_1044_);
v___x_1046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1043_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__5, &l_Lean_Meta_rwMatcher___lam__1___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__5);
v___x_1048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1046_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1048_, v___y_1030_, v___y_1035_, v___y_1032_, v___y_1037_);
v___y_1018_ = v___y_1031_;
v___y_1019_ = v___x_1049_;
goto v___jp_1017_;
}
else
{
lean_dec_ref(v___y_1036_);
lean_dec_ref(v___y_1034_);
v___y_1018_ = v___y_1031_;
v___y_1019_ = v___y_1033_;
goto v___jp_1017_;
}
}
v___jp_1051_:
{
lean_object* v___x_1058_; lean_object* v_a_1059_; lean_object* v___x_1060_; 
v___x_1058_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___y_1052_, v___y_1055_);
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_a_1059_);
lean_dec_ref(v___x_1058_);
v___x_1060_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1050_, v___y_1055_);
if (v___y_1053_ == 0)
{
lean_object* v_a_1061_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_a_1061_);
lean_dec_ref(v___x_1060_);
v___y_1012_ = v_a_1059_;
v_proof_1013_ = v_a_1061_;
goto v___jp_1011_;
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1063_; 
v_a_1062_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_a_1062_);
lean_dec_ref(v___x_1060_);
lean_inc(v_a_1062_);
v___x_1063_ = l_Lean_Meta_mkEqOfHEq(v_a_1062_, v___x_998_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_dec(v_a_1062_);
v___y_1018_ = v_a_1059_;
v___y_1019_ = v___x_1063_;
goto v___jp_1017_;
}
else
{
lean_object* v_a_1064_; uint8_t v___x_1065_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1064_);
v___x_1065_ = l_Lean_Exception_isInterrupt(v_a_1064_);
if (v___x_1065_ == 0)
{
uint8_t v___x_1066_; 
lean_inc(v_a_1064_);
v___x_1066_ = l_Lean_Exception_isRuntime(v_a_1064_);
v___y_1030_ = v___y_1054_;
v___y_1031_ = v_a_1059_;
v___y_1032_ = v___y_1056_;
v___y_1033_ = v___x_1063_;
v___y_1034_ = v_a_1062_;
v___y_1035_ = v___y_1055_;
v___y_1036_ = v_a_1064_;
v___y_1037_ = v___y_1057_;
v___y_1038_ = v___x_1066_;
goto v___jp_1029_;
}
else
{
v___y_1030_ = v___y_1054_;
v___y_1031_ = v_a_1059_;
v___y_1032_ = v___y_1056_;
v___y_1033_ = v___x_1063_;
v___y_1034_ = v_a_1062_;
v___y_1035_ = v___y_1055_;
v___y_1036_ = v_a_1064_;
v___y_1037_ = v___y_1057_;
v___y_1038_ = v___x_1065_;
goto v___jp_1029_;
}
}
}
}
v___jp_1067_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v___x_1075_ = lean_array_get_size(v_a_1074_);
v___x_1076_ = lean_unsigned_to_nat(0u);
v___x_1077_ = lean_nat_dec_eq(v___x_1075_, v___x_1076_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec_ref(v___y_1071_);
lean_dec_ref(v___x_1050_);
v___x_1078_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__7, &l_Lean_Meta_rwMatcher___lam__1___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__7);
v___x_1079_ = l_Lean_MessageData_ofConstName(v___x_1001_, v_hasTrace_1002_);
v___x_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__9, &l_Lean_Meta_rwMatcher___lam__1___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__9);
v___x_1082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1080_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = lean_array_to_list(v_a_1074_);
v___x_1084_ = lean_box(0);
v___x_1085_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1083_, v___x_1084_);
v___x_1086_ = l_Lean_MessageData_ofList(v___x_1085_);
v___x_1087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1082_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1087_, v___y_1072_, v___y_1069_, v___y_1068_, v___y_1070_);
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1088_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1088_);
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
else
{
lean_dec_ref(v_a_1074_);
lean_dec(v___x_1001_);
v___y_1052_ = v___y_1071_;
v___y_1053_ = v___y_1073_;
v___y_1054_ = v___y_1072_;
v___y_1055_ = v___y_1069_;
v___y_1056_ = v___y_1068_;
v___y_1057_ = v___y_1070_;
goto v___jp_1051_;
}
}
v___jp_1097_:
{
if (lean_obj_tag(v___y_1104_) == 0)
{
lean_object* v_a_1105_; 
v_a_1105_ = lean_ctor_get(v___y_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref(v___y_1104_);
v___y_1068_ = v___y_1098_;
v___y_1069_ = v___y_1099_;
v___y_1070_ = v___y_1100_;
v___y_1071_ = v___y_1102_;
v___y_1072_ = v___y_1101_;
v___y_1073_ = v___y_1103_;
v_a_1074_ = v_a_1105_;
goto v___jp_1067_;
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec_ref(v___y_1102_);
lean_dec_ref(v___x_1050_);
lean_dec(v___x_1001_);
v_a_1106_ = lean_ctor_get(v___y_1104_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___y_1104_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___y_1104_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___y_1104_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
v___jp_1117_:
{
lean_object* v___x_1124_; size_t v_sz_1125_; lean_object* v___x_1126_; 
v___x_1124_ = lean_box(0);
v_sz_1125_ = lean_array_size(v___x_1116_);
v___x_1126_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8(v___x_1116_, v_sz_1125_, v___x_1115_, v___x_1124_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; 
lean_dec_ref(v___x_1126_);
v___x_1127_ = lean_unsigned_to_nat(0u);
v___x_1128_ = lean_array_get_size(v___x_1116_);
v___x_1129_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__10));
v___x_1130_ = lean_nat_dec_lt(v___x_1127_, v___x_1128_);
if (v___x_1130_ == 0)
{
lean_dec_ref(v___x_1116_);
v___y_1068_ = v___y_1122_;
v___y_1069_ = v___y_1121_;
v___y_1070_ = v___y_1123_;
v___y_1071_ = v___y_1118_;
v___y_1072_ = v___y_1120_;
v___y_1073_ = v___y_1119_;
v_a_1074_ = v___x_1129_;
goto v___jp_1067_;
}
else
{
uint8_t v___x_1131_; 
v___x_1131_ = lean_nat_dec_le(v___x_1128_, v___x_1128_);
if (v___x_1131_ == 0)
{
if (v___x_1130_ == 0)
{
lean_dec_ref(v___x_1116_);
v___y_1068_ = v___y_1122_;
v___y_1069_ = v___y_1121_;
v___y_1070_ = v___y_1123_;
v___y_1071_ = v___y_1118_;
v___y_1072_ = v___y_1120_;
v___y_1073_ = v___y_1119_;
v_a_1074_ = v___x_1129_;
goto v___jp_1067_;
}
else
{
size_t v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = lean_usize_of_nat(v___x_1128_);
v___x_1133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9(v___x_1116_, v___x_1115_, v___x_1132_, v___x_1129_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec_ref(v___x_1116_);
v___y_1098_ = v___y_1122_;
v___y_1099_ = v___y_1121_;
v___y_1100_ = v___y_1123_;
v___y_1101_ = v___y_1120_;
v___y_1102_ = v___y_1118_;
v___y_1103_ = v___y_1119_;
v___y_1104_ = v___x_1133_;
goto v___jp_1097_;
}
}
else
{
size_t v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = lean_usize_of_nat(v___x_1128_);
v___x_1135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9(v___x_1116_, v___x_1115_, v___x_1134_, v___x_1129_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec_ref(v___x_1116_);
v___y_1098_ = v___y_1122_;
v___y_1099_ = v___y_1121_;
v___y_1100_ = v___y_1123_;
v___y_1101_ = v___y_1120_;
v___y_1102_ = v___y_1118_;
v___y_1103_ = v___y_1119_;
v___y_1104_ = v___x_1135_;
goto v___jp_1097_;
}
}
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec_ref(v___y_1118_);
lean_dec_ref(v___x_1116_);
lean_dec_ref(v___x_1050_);
lean_dec(v___x_1001_);
v_a_1136_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1126_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1126_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
v___jp_1144_:
{
lean_object* v___x_1148_; 
lean_inc_ref(v_fst_1146_);
lean_inc_ref(v_e_1003_);
v___x_1148_ = l_Lean_Meta_isExprDefEq(v_e_1003_, v_fst_1146_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; uint8_t v___x_1150_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_a_1149_);
lean_dec_ref(v___x_1148_);
v___x_1150_ = lean_unbox(v_a_1149_);
lean_dec(v_a_1149_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
lean_dec_ref(v_snd_1147_);
lean_dec_ref(v___x_1116_);
lean_dec_ref(v___x_1050_);
v___x_1151_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__12, &l_Lean_Meta_rwMatcher___lam__1___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__12);
v___x_1152_ = l_Lean_MessageData_ofExpr(v_fst_1146_);
v___x_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1151_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__14, &l_Lean_Meta_rwMatcher___lam__1___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__14);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = l_Lean_MessageData_ofConstName(v___x_1001_, v_hasTrace_1002_);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__16, &l_Lean_Meta_rwMatcher___lam__1___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__16);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = l_Lean_MessageData_ofExpr(v_e_1003_);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1159_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v___x_1162_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
v___x_1163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1161_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___x_1164_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1163_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
else
{
lean_dec_ref(v_fst_1146_);
lean_dec_ref(v_e_1003_);
v___y_1118_ = v_snd_1147_;
v___y_1119_ = v_fst_1145_;
v___y_1120_ = v___y_1006_;
v___y_1121_ = v___y_1007_;
v___y_1122_ = v___y_1008_;
v___y_1123_ = v___y_1009_;
goto v___jp_1117_;
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
lean_dec_ref(v_snd_1147_);
lean_dec_ref(v_fst_1146_);
lean_dec_ref(v___x_1116_);
lean_dec_ref(v___x_1050_);
lean_dec_ref(v_e_1003_);
lean_dec(v___x_1001_);
v_a_1173_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1148_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1148_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__1___boxed(lean_object* v___x_1208_, lean_object* v___x_1209_, lean_object* v_fst_1210_, lean_object* v___x_1211_, lean_object* v_hasTrace_1212_, lean_object* v_e_1213_, lean_object* v_snd_1214_, lean_object* v_____r_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
uint8_t v___x_99563__boxed_1221_; uint8_t v_hasTrace_boxed_1222_; lean_object* v_res_1223_; 
v___x_99563__boxed_1221_ = lean_unbox(v___x_1208_);
v_hasTrace_boxed_1222_ = lean_unbox(v_hasTrace_1212_);
v_res_1223_ = l_Lean_Meta_rwMatcher___lam__1(v___x_99563__boxed_1221_, v___x_1209_, v_fst_1210_, v___x_1211_, v_hasTrace_boxed_1222_, v_e_1213_, v_snd_1214_, v_____r_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec_ref(v_snd_1214_);
return v_res_1223_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__0));
v___x_1226_ = l_Lean_stringToMessageData(v___x_1225_);
return v___x_1226_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__2));
v___x_1229_ = l_Lean_stringToMessageData(v___x_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2(lean_object* v___x_1230_, uint8_t v___y_1231_, lean_object* v_e_1232_, lean_object* v_x_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1239_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1240_ = l_Lean_MessageData_ofConstName(v___x_1230_, v___y_1231_);
v___x_1241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1239_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
v___x_1242_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1241_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
v___x_1244_ = l_Lean_indentExpr(v_e_1232_);
v___x_1245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1243_);
lean_ctor_set(v___x_1245_, 1, v___x_1244_);
v___x_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2___boxed(lean_object* v___x_1247_, lean_object* v___y_1248_, lean_object* v_e_1249_, lean_object* v_x_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
uint8_t v___y_100042__boxed_1256_; lean_object* v_res_1257_; 
v___y_100042__boxed_1256_ = lean_unbox(v___y_1248_);
v_res_1257_ = l_Lean_Meta_rwMatcher___lam__2(v___x_1247_, v___y_100042__boxed_1256_, v_e_1249_, v_x_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec_ref(v_x_1250_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(uint8_t v___x_1258_, lean_object* v_as_1259_, size_t v_i_1260_, size_t v_stop_1261_, lean_object* v_b_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_a_1269_; uint8_t v___x_1273_; 
v___x_1273_ = lean_usize_dec_eq(v_i_1260_, v_stop_1261_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; uint8_t v_a_1278_; lean_object* v___x_1279_; 
v___x_1274_ = lean_array_uget_borrowed(v_as_1259_, v_i_1260_);
v___x_1279_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v___x_1274_, v___y_1264_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; uint8_t v___x_1281_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref(v___x_1279_);
v___x_1281_ = lean_unbox(v_a_1280_);
lean_dec(v_a_1280_);
if (v___x_1281_ == 0)
{
goto v___jp_1275_;
}
else
{
v_a_1278_ = v___x_1258_;
goto v___jp_1277_;
}
}
else
{
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1282_; uint8_t v___x_1283_; 
v_a_1282_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1282_);
lean_dec_ref(v___x_1279_);
v___x_1283_ = lean_unbox(v_a_1282_);
lean_dec(v_a_1282_);
v_a_1278_ = v___x_1283_;
goto v___jp_1277_;
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec_ref(v_b_1262_);
v_a_1284_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1279_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1279_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
v___jp_1275_:
{
lean_object* v___x_1276_; 
lean_inc(v___x_1274_);
v___x_1276_ = lean_array_push(v_b_1262_, v___x_1274_);
v_a_1269_ = v___x_1276_;
goto v___jp_1268_;
}
v___jp_1277_:
{
if (v_a_1278_ == 0)
{
v_a_1269_ = v_b_1262_;
goto v___jp_1268_;
}
else
{
goto v___jp_1275_;
}
}
}
else
{
lean_object* v___x_1292_; 
v___x_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1292_, 0, v_b_1262_);
return v___x_1292_;
}
v___jp_1268_:
{
size_t v___x_1270_; size_t v___x_1271_; 
v___x_1270_ = ((size_t)1ULL);
v___x_1271_ = lean_usize_add(v_i_1260_, v___x_1270_);
v_i_1260_ = v___x_1271_;
v_b_1262_ = v_a_1269_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13___boxed(lean_object* v___x_1293_, lean_object* v_as_1294_, lean_object* v_i_1295_, lean_object* v_stop_1296_, lean_object* v_b_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
uint8_t v___x_100087__boxed_1303_; size_t v_i_boxed_1304_; size_t v_stop_boxed_1305_; lean_object* v_res_1306_; 
v___x_100087__boxed_1303_ = lean_unbox(v___x_1293_);
v_i_boxed_1304_ = lean_unbox_usize(v_i_1295_);
lean_dec(v_i_1295_);
v_stop_boxed_1305_ = lean_unbox_usize(v_stop_1296_);
lean_dec(v_stop_1296_);
v_res_1306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(v___x_100087__boxed_1303_, v_as_1294_, v_i_boxed_1304_, v_stop_boxed_1305_, v_b_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec_ref(v_as_1294_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3(uint8_t v___x_1307_, lean_object* v___x_1308_, lean_object* v_fst_1309_, lean_object* v___x_1310_, uint8_t v___x_1311_, lean_object* v_e_1312_, lean_object* v_snd_1313_, lean_object* v_____r_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v___y_1321_; lean_object* v_proof_1322_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; uint8_t v___y_1347_; lean_object* v___x_1359_; lean_object* v___y_1361_; uint8_t v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1377_; lean_object* v___y_1378_; uint8_t v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v_a_1383_; lean_object* v___y_1407_; lean_object* v___y_1408_; uint8_t v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; size_t v_sz_1423_; size_t v___x_1424_; lean_object* v___x_1425_; lean_object* v___y_1427_; uint8_t v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1454_; lean_object* v___y_1455_; uint8_t v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; uint8_t v_fst_1484_; lean_object* v_fst_1485_; lean_object* v_snd_1486_; lean_object* v___x_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; 
v___x_1359_ = l_Lean_mkAppN(v___x_1308_, v_fst_1309_);
v_sz_1423_ = lean_array_size(v_fst_1309_);
v___x_1424_ = ((size_t)0ULL);
v___x_1425_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4(v_sz_1423_, v___x_1424_, v_fst_1309_);
v___x_1498_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__18));
v___x_1499_ = lean_unsigned_to_nat(4u);
v___x_1500_ = l_Lean_Expr_isAppOfArity(v_snd_1313_, v___x_1498_, v___x_1499_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1501_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__20));
v___x_1502_ = lean_unsigned_to_nat(3u);
v___x_1503_ = l_Lean_Expr_isAppOfArity(v_snd_1313_, v___x_1501_, v___x_1502_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec_ref(v___x_1425_);
lean_dec_ref(v___x_1359_);
lean_dec_ref(v_e_1312_);
v___x_1504_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__22, &l_Lean_Meta_rwMatcher___lam__1___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__22);
v___x_1505_ = l_Lean_MessageData_ofConstName(v___x_1310_, v___x_1311_);
v___x_1506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1504_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
v___x_1507_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__24, &l_Lean_Meta_rwMatcher___lam__1___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__24);
v___x_1508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1506_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
v___x_1509_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1508_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1509_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1509_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
else
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1518_ = l_Lean_Expr_appFn_x21(v_snd_1313_);
v___x_1519_ = l_Lean_Expr_appArg_x21(v___x_1518_);
lean_dec_ref(v___x_1518_);
v___x_1520_ = l_Lean_Expr_appArg_x21(v_snd_1313_);
v_fst_1484_ = v___x_1311_;
v_fst_1485_ = v___x_1519_;
v_snd_1486_ = v___x_1520_;
goto v___jp_1483_;
}
}
else
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1521_ = l_Lean_Expr_appFn_x21(v_snd_1313_);
v___x_1522_ = l_Lean_Expr_appFn_x21(v___x_1521_);
lean_dec_ref(v___x_1521_);
v___x_1523_ = l_Lean_Expr_appArg_x21(v___x_1522_);
lean_dec_ref(v___x_1522_);
v___x_1524_ = l_Lean_Expr_appArg_x21(v_snd_1313_);
v_fst_1484_ = v___x_1307_;
v_fst_1485_ = v___x_1523_;
v_snd_1486_ = v___x_1524_;
goto v___jp_1483_;
}
v___jp_1320_:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1323_, 0, v_proof_1322_);
v___x_1324_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1324_, 0, v___y_1321_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
lean_ctor_set_uint8(v___x_1324_, sizeof(void*)*2, v___x_1307_);
v___x_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
return v___x_1325_;
}
v___jp_1326_:
{
if (lean_obj_tag(v___y_1328_) == 0)
{
lean_object* v_a_1329_; 
v_a_1329_ = lean_ctor_get(v___y_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref(v___y_1328_);
v___y_1321_ = v___y_1327_;
v_proof_1322_ = v_a_1329_;
goto v___jp_1320_;
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_dec_ref(v___y_1327_);
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
v___jp_1338_:
{
if (v___y_1347_ == 0)
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
lean_dec_ref(v___y_1340_);
v___x_1348_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__1, &l_Lean_Meta_rwMatcher___lam__1___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__1);
v___x_1349_ = l_Lean_MessageData_ofExpr(v___y_1339_);
v___x_1350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1348_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
v___x_1351_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__3, &l_Lean_Meta_rwMatcher___lam__1___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__3);
v___x_1352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1350_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
v___x_1353_ = l_Lean_Exception_toMessageData(v___y_1341_);
v___x_1354_ = l_Lean_indentD(v___x_1353_);
v___x_1355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1352_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__5, &l_Lean_Meta_rwMatcher___lam__1___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__5);
v___x_1357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1355_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1357_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1343_);
v___y_1327_ = v___y_1342_;
v___y_1328_ = v___x_1358_;
goto v___jp_1326_;
}
else
{
lean_dec_ref(v___y_1341_);
lean_dec_ref(v___y_1339_);
v___y_1327_ = v___y_1342_;
v___y_1328_ = v___y_1340_;
goto v___jp_1326_;
}
}
v___jp_1360_:
{
lean_object* v___x_1367_; lean_object* v_a_1368_; lean_object* v___x_1369_; 
v___x_1367_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___y_1361_, v___y_1364_);
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_a_1368_);
lean_dec_ref(v___x_1367_);
v___x_1369_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1359_, v___y_1364_);
if (v___y_1362_ == 0)
{
lean_object* v_a_1370_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref(v___x_1369_);
v___y_1321_ = v_a_1368_;
v_proof_1322_ = v_a_1370_;
goto v___jp_1320_;
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1372_; 
v_a_1371_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1371_);
lean_dec_ref(v___x_1369_);
lean_inc(v_a_1371_);
v___x_1372_ = l_Lean_Meta_mkEqOfHEq(v_a_1371_, v___x_1307_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_dec(v_a_1371_);
v___y_1327_ = v_a_1368_;
v___y_1328_ = v___x_1372_;
goto v___jp_1326_;
}
else
{
lean_object* v_a_1373_; uint8_t v___x_1374_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1373_);
v___x_1374_ = l_Lean_Exception_isInterrupt(v_a_1373_);
if (v___x_1374_ == 0)
{
uint8_t v___x_1375_; 
lean_inc(v_a_1373_);
v___x_1375_ = l_Lean_Exception_isRuntime(v_a_1373_);
v___y_1339_ = v_a_1371_;
v___y_1340_ = v___x_1372_;
v___y_1341_ = v_a_1373_;
v___y_1342_ = v_a_1368_;
v___y_1343_ = v___y_1366_;
v___y_1344_ = v___y_1363_;
v___y_1345_ = v___y_1364_;
v___y_1346_ = v___y_1365_;
v___y_1347_ = v___x_1375_;
goto v___jp_1338_;
}
else
{
v___y_1339_ = v_a_1371_;
v___y_1340_ = v___x_1372_;
v___y_1341_ = v_a_1373_;
v___y_1342_ = v_a_1368_;
v___y_1343_ = v___y_1366_;
v___y_1344_ = v___y_1363_;
v___y_1345_ = v___y_1364_;
v___y_1346_ = v___y_1365_;
v___y_1347_ = v___x_1374_;
goto v___jp_1338_;
}
}
}
}
v___jp_1376_:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1384_ = lean_array_get_size(v_a_1383_);
v___x_1385_ = lean_unsigned_to_nat(0u);
v___x_1386_ = lean_nat_dec_eq(v___x_1384_, v___x_1385_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_dec_ref(v___y_1378_);
lean_dec_ref(v___x_1359_);
v___x_1387_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__7, &l_Lean_Meta_rwMatcher___lam__1___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__7);
v___x_1388_ = l_Lean_MessageData_ofConstName(v___x_1310_, v___x_1311_);
v___x_1389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1387_);
lean_ctor_set(v___x_1389_, 1, v___x_1388_);
v___x_1390_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__9, &l_Lean_Meta_rwMatcher___lam__1___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__9);
v___x_1391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1389_);
lean_ctor_set(v___x_1391_, 1, v___x_1390_);
v___x_1392_ = lean_array_to_list(v_a_1383_);
v___x_1393_ = lean_box(0);
v___x_1394_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1392_, v___x_1393_);
v___x_1395_ = l_Lean_MessageData_ofList(v___x_1394_);
v___x_1396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1391_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
v___x_1397_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1396_, v___y_1382_, v___y_1381_, v___y_1380_, v___y_1377_);
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1397_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1397_);
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
else
{
lean_dec_ref(v_a_1383_);
lean_dec(v___x_1310_);
v___y_1361_ = v___y_1378_;
v___y_1362_ = v___y_1379_;
v___y_1363_ = v___y_1382_;
v___y_1364_ = v___y_1381_;
v___y_1365_ = v___y_1380_;
v___y_1366_ = v___y_1377_;
goto v___jp_1360_;
}
}
v___jp_1406_:
{
if (lean_obj_tag(v___y_1413_) == 0)
{
lean_object* v_a_1414_; 
v_a_1414_ = lean_ctor_get(v___y_1413_, 0);
lean_inc(v_a_1414_);
lean_dec_ref(v___y_1413_);
v___y_1377_ = v___y_1407_;
v___y_1378_ = v___y_1408_;
v___y_1379_ = v___y_1409_;
v___y_1380_ = v___y_1410_;
v___y_1381_ = v___y_1411_;
v___y_1382_ = v___y_1412_;
v_a_1383_ = v_a_1414_;
goto v___jp_1376_;
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_dec_ref(v___y_1408_);
lean_dec_ref(v___x_1359_);
lean_dec(v___x_1310_);
v_a_1415_ = lean_ctor_get(v___y_1413_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___y_1413_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___y_1413_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___y_1413_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
v___jp_1426_:
{
lean_object* v___x_1433_; size_t v_sz_1434_; lean_object* v___x_1435_; 
v___x_1433_ = lean_box(0);
v_sz_1434_ = lean_array_size(v___x_1425_);
v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8(v___x_1425_, v_sz_1434_, v___x_1424_, v___x_1433_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; 
lean_dec_ref(v___x_1435_);
v___x_1436_ = lean_unsigned_to_nat(0u);
v___x_1437_ = lean_array_get_size(v___x_1425_);
v___x_1438_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__10));
v___x_1439_ = lean_nat_dec_lt(v___x_1436_, v___x_1437_);
if (v___x_1439_ == 0)
{
lean_dec_ref(v___x_1425_);
v___y_1377_ = v___y_1432_;
v___y_1378_ = v___y_1427_;
v___y_1379_ = v___y_1428_;
v___y_1380_ = v___y_1431_;
v___y_1381_ = v___y_1430_;
v___y_1382_ = v___y_1429_;
v_a_1383_ = v___x_1438_;
goto v___jp_1376_;
}
else
{
uint8_t v___x_1440_; 
v___x_1440_ = lean_nat_dec_le(v___x_1437_, v___x_1437_);
if (v___x_1440_ == 0)
{
if (v___x_1439_ == 0)
{
lean_dec_ref(v___x_1425_);
v___y_1377_ = v___y_1432_;
v___y_1378_ = v___y_1427_;
v___y_1379_ = v___y_1428_;
v___y_1380_ = v___y_1431_;
v___y_1381_ = v___y_1430_;
v___y_1382_ = v___y_1429_;
v_a_1383_ = v___x_1438_;
goto v___jp_1376_;
}
else
{
size_t v___x_1441_; lean_object* v___x_1442_; 
v___x_1441_ = lean_usize_of_nat(v___x_1437_);
v___x_1442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(v___x_1311_, v___x_1425_, v___x_1424_, v___x_1441_, v___x_1438_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
lean_dec_ref(v___x_1425_);
v___y_1407_ = v___y_1432_;
v___y_1408_ = v___y_1427_;
v___y_1409_ = v___y_1428_;
v___y_1410_ = v___y_1431_;
v___y_1411_ = v___y_1430_;
v___y_1412_ = v___y_1429_;
v___y_1413_ = v___x_1442_;
goto v___jp_1406_;
}
}
else
{
size_t v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = lean_usize_of_nat(v___x_1437_);
v___x_1444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(v___x_1311_, v___x_1425_, v___x_1424_, v___x_1443_, v___x_1438_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
lean_dec_ref(v___x_1425_);
v___y_1407_ = v___y_1432_;
v___y_1408_ = v___y_1427_;
v___y_1409_ = v___y_1428_;
v___y_1410_ = v___y_1431_;
v___y_1411_ = v___y_1430_;
v___y_1412_ = v___y_1429_;
v___y_1413_ = v___x_1444_;
goto v___jp_1406_;
}
}
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
lean_dec_ref(v___y_1427_);
lean_dec_ref(v___x_1425_);
lean_dec_ref(v___x_1359_);
lean_dec(v___x_1310_);
v_a_1445_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1435_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1435_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
v___jp_1453_:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
lean_dec_ref(v___y_1455_);
v___x_1461_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__12, &l_Lean_Meta_rwMatcher___lam__1___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__12);
v___x_1462_ = l_Lean_MessageData_ofExpr(v___y_1460_);
v___x_1463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1461_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
v___x_1464_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__14, &l_Lean_Meta_rwMatcher___lam__1___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__14);
v___x_1465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1463_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
v___x_1466_ = l_Lean_MessageData_ofConstName(v___x_1310_, v___x_1311_);
v___x_1467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1465_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__16, &l_Lean_Meta_rwMatcher___lam__1___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__16);
v___x_1469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1467_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
v___x_1470_ = l_Lean_MessageData_ofExpr(v_e_1312_);
v___x_1471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1469_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
v___x_1473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1471_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
v___x_1474_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1473_, v___y_1457_, v___y_1454_, v___y_1459_, v___y_1458_);
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1474_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1474_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
v___jp_1483_:
{
lean_object* v___x_1487_; 
lean_inc_ref(v_fst_1485_);
lean_inc_ref(v_e_1312_);
v___x_1487_ = l_Lean_Meta_isExprDefEq(v_e_1312_, v_fst_1485_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; uint8_t v___x_1489_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_a_1488_);
lean_dec_ref(v___x_1487_);
v___x_1489_ = lean_unbox(v_a_1488_);
lean_dec(v_a_1488_);
if (v___x_1489_ == 0)
{
lean_dec_ref(v___x_1425_);
lean_dec_ref(v___x_1359_);
v___y_1454_ = v___y_1316_;
v___y_1455_ = v_snd_1486_;
v___y_1456_ = v_fst_1484_;
v___y_1457_ = v___y_1315_;
v___y_1458_ = v___y_1318_;
v___y_1459_ = v___y_1317_;
v___y_1460_ = v_fst_1485_;
goto v___jp_1453_;
}
else
{
if (v___x_1311_ == 0)
{
lean_dec_ref(v_fst_1485_);
lean_dec_ref(v_e_1312_);
v___y_1427_ = v_snd_1486_;
v___y_1428_ = v_fst_1484_;
v___y_1429_ = v___y_1315_;
v___y_1430_ = v___y_1316_;
v___y_1431_ = v___y_1317_;
v___y_1432_ = v___y_1318_;
goto v___jp_1426_;
}
else
{
lean_dec_ref(v___x_1425_);
lean_dec_ref(v___x_1359_);
v___y_1454_ = v___y_1316_;
v___y_1455_ = v_snd_1486_;
v___y_1456_ = v_fst_1484_;
v___y_1457_ = v___y_1315_;
v___y_1458_ = v___y_1318_;
v___y_1459_ = v___y_1317_;
v___y_1460_ = v_fst_1485_;
goto v___jp_1453_;
}
}
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_dec_ref(v_snd_1486_);
lean_dec_ref(v_fst_1485_);
lean_dec_ref(v___x_1425_);
lean_dec_ref(v___x_1359_);
lean_dec_ref(v_e_1312_);
lean_dec(v___x_1310_);
v_a_1490_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1487_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1487_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3___boxed(lean_object* v___x_1525_, lean_object* v___x_1526_, lean_object* v_fst_1527_, lean_object* v___x_1528_, lean_object* v___x_1529_, lean_object* v_e_1530_, lean_object* v_snd_1531_, lean_object* v_____r_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
uint8_t v___x_100196__boxed_1538_; uint8_t v___x_100200__boxed_1539_; lean_object* v_res_1540_; 
v___x_100196__boxed_1538_ = lean_unbox(v___x_1525_);
v___x_100200__boxed_1539_ = lean_unbox(v___x_1529_);
v_res_1540_ = l_Lean_Meta_rwMatcher___lam__3(v___x_100196__boxed_1538_, v___x_1526_, v_fst_1527_, v___x_1528_, v___x_100200__boxed_1539_, v_e_1530_, v_snd_1531_, v_____r_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec_ref(v_snd_1531_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__14(uint8_t v___x_1541_, lean_object* v_as_1542_, size_t v_i_1543_, size_t v_stop_1544_, lean_object* v_b_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v_a_1552_; uint8_t v___x_1556_; 
v___x_1556_ = lean_usize_dec_eq(v_i_1543_, v_stop_1544_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; uint8_t v_a_1559_; lean_object* v___x_1561_; 
v___x_1557_ = lean_array_uget_borrowed(v_as_1542_, v_i_1543_);
v___x_1561_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v___x_1557_, v___y_1547_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; uint8_t v___x_1563_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref(v___x_1561_);
v___x_1563_ = lean_unbox(v_a_1562_);
lean_dec(v_a_1562_);
if (v___x_1563_ == 0)
{
v_a_1559_ = v___x_1541_;
goto v___jp_1558_;
}
else
{
v_a_1552_ = v_b_1545_;
goto v___jp_1551_;
}
}
else
{
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1564_; uint8_t v___x_1565_; 
v_a_1564_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1564_);
lean_dec_ref(v___x_1561_);
v___x_1565_ = lean_unbox(v_a_1564_);
lean_dec(v_a_1564_);
v_a_1559_ = v___x_1565_;
goto v___jp_1558_;
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec_ref(v_b_1545_);
v_a_1566_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1561_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1561_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
v___jp_1558_:
{
if (v_a_1559_ == 0)
{
v_a_1552_ = v_b_1545_;
goto v___jp_1551_;
}
else
{
lean_object* v___x_1560_; 
lean_inc(v___x_1557_);
v___x_1560_ = lean_array_push(v_b_1545_, v___x_1557_);
v_a_1552_ = v___x_1560_;
goto v___jp_1551_;
}
}
}
else
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1574_, 0, v_b_1545_);
return v___x_1574_;
}
v___jp_1551_:
{
size_t v___x_1553_; size_t v___x_1554_; 
v___x_1553_ = ((size_t)1ULL);
v___x_1554_ = lean_usize_add(v_i_1543_, v___x_1553_);
v_i_1543_ = v___x_1554_;
v_b_1545_ = v_a_1552_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__14___boxed(lean_object* v___x_1575_, lean_object* v_as_1576_, lean_object* v_i_1577_, lean_object* v_stop_1578_, lean_object* v_b_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
uint8_t v___x_100656__boxed_1585_; size_t v_i_boxed_1586_; size_t v_stop_boxed_1587_; lean_object* v_res_1588_; 
v___x_100656__boxed_1585_ = lean_unbox(v___x_1575_);
v_i_boxed_1586_ = lean_unbox_usize(v_i_1577_);
lean_dec(v_i_1577_);
v_stop_boxed_1587_ = lean_unbox_usize(v_stop_1578_);
lean_dec(v_stop_1578_);
v_res_1588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__14(v___x_100656__boxed_1585_, v_as_1576_, v_i_boxed_1586_, v_stop_boxed_1587_, v_b_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec_ref(v_as_1576_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4(uint8_t v___x_1589_, lean_object* v___x_1590_, lean_object* v_fst_1591_, lean_object* v___x_1592_, uint8_t v___x_1593_, lean_object* v_e_1594_, uint8_t v___y_1595_, lean_object* v_snd_1596_, lean_object* v_____r_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v___y_1604_; lean_object* v_proof_1605_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; uint8_t v___y_1630_; lean_object* v___x_1642_; lean_object* v___y_1644_; uint8_t v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; uint8_t v___y_1665_; lean_object* v_a_1666_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; uint8_t v___y_1695_; lean_object* v___y_1696_; size_t v_sz_1706_; size_t v___x_1707_; lean_object* v___x_1708_; lean_object* v___y_1710_; uint8_t v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; uint8_t v_fst_1737_; lean_object* v_fst_1738_; lean_object* v_snd_1739_; lean_object* v___x_1773_; lean_object* v___x_1774_; uint8_t v___x_1775_; 
v___x_1642_ = l_Lean_mkAppN(v___x_1590_, v_fst_1591_);
v_sz_1706_ = lean_array_size(v_fst_1591_);
v___x_1707_ = ((size_t)0ULL);
v___x_1708_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4(v_sz_1706_, v___x_1707_, v_fst_1591_);
v___x_1773_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__18));
v___x_1774_ = lean_unsigned_to_nat(4u);
v___x_1775_ = l_Lean_Expr_isAppOfArity(v_snd_1596_, v___x_1773_, v___x_1774_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___x_1776_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__20));
v___x_1777_ = lean_unsigned_to_nat(3u);
v___x_1778_ = l_Lean_Expr_isAppOfArity(v_snd_1596_, v___x_1776_, v___x_1777_);
if (v___x_1778_ == 0)
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_dec_ref(v___x_1708_);
lean_dec_ref(v___x_1642_);
lean_dec_ref(v_e_1594_);
v___x_1779_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__22, &l_Lean_Meta_rwMatcher___lam__1___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__22);
v___x_1780_ = l_Lean_MessageData_ofConstName(v___x_1592_, v___x_1778_);
v___x_1781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1779_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__24, &l_Lean_Meta_rwMatcher___lam__1___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__24);
v___x_1783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1781_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
v___x_1784_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1783_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1784_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1784_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1793_ = l_Lean_Expr_appFn_x21(v_snd_1596_);
v___x_1794_ = l_Lean_Expr_appArg_x21(v___x_1793_);
lean_dec_ref(v___x_1793_);
v___x_1795_ = l_Lean_Expr_appArg_x21(v_snd_1596_);
v_fst_1737_ = v___x_1775_;
v_fst_1738_ = v___x_1794_;
v_snd_1739_ = v___x_1795_;
goto v___jp_1736_;
}
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1796_ = l_Lean_Expr_appFn_x21(v_snd_1596_);
v___x_1797_ = l_Lean_Expr_appFn_x21(v___x_1796_);
lean_dec_ref(v___x_1796_);
v___x_1798_ = l_Lean_Expr_appArg_x21(v___x_1797_);
lean_dec_ref(v___x_1797_);
v___x_1799_ = l_Lean_Expr_appArg_x21(v_snd_1596_);
v_fst_1737_ = v___x_1589_;
v_fst_1738_ = v___x_1798_;
v_snd_1739_ = v___x_1799_;
goto v___jp_1736_;
}
v___jp_1603_:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1606_, 0, v_proof_1605_);
v___x_1607_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1607_, 0, v___y_1604_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
lean_ctor_set_uint8(v___x_1607_, sizeof(void*)*2, v___x_1589_);
v___x_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
return v___x_1608_;
}
v___jp_1609_:
{
if (lean_obj_tag(v___y_1611_) == 0)
{
lean_object* v_a_1612_; 
v_a_1612_ = lean_ctor_get(v___y_1611_, 0);
lean_inc(v_a_1612_);
lean_dec_ref(v___y_1611_);
v___y_1604_ = v___y_1610_;
v_proof_1605_ = v_a_1612_;
goto v___jp_1603_;
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec_ref(v___y_1610_);
v_a_1613_ = lean_ctor_get(v___y_1611_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___y_1611_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___y_1611_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___y_1611_);
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
v___jp_1621_:
{
if (v___y_1630_ == 0)
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_dec_ref(v___y_1622_);
v___x_1631_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__1, &l_Lean_Meta_rwMatcher___lam__1___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__1);
v___x_1632_ = l_Lean_MessageData_ofExpr(v___y_1629_);
v___x_1633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__3, &l_Lean_Meta_rwMatcher___lam__1___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__3);
v___x_1635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = l_Lean_Exception_toMessageData(v___y_1625_);
v___x_1637_ = l_Lean_indentD(v___x_1636_);
v___x_1638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1635_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
v___x_1639_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__5, &l_Lean_Meta_rwMatcher___lam__1___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__5);
v___x_1640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1638_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1640_, v___y_1623_, v___y_1628_, v___y_1627_, v___y_1626_);
v___y_1610_ = v___y_1624_;
v___y_1611_ = v___x_1641_;
goto v___jp_1609_;
}
else
{
lean_dec_ref(v___y_1629_);
lean_dec_ref(v___y_1625_);
v___y_1610_ = v___y_1624_;
v___y_1611_ = v___y_1622_;
goto v___jp_1609_;
}
}
v___jp_1643_:
{
lean_object* v___x_1650_; lean_object* v_a_1651_; lean_object* v___x_1652_; 
v___x_1650_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___y_1644_, v___y_1647_);
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref(v___x_1650_);
v___x_1652_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1642_, v___y_1647_);
if (v___y_1645_ == 0)
{
lean_object* v_a_1653_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref(v___x_1652_);
v___y_1604_ = v_a_1651_;
v_proof_1605_ = v_a_1653_;
goto v___jp_1603_;
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1655_; 
v_a_1654_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1654_);
lean_dec_ref(v___x_1652_);
lean_inc(v_a_1654_);
v___x_1655_ = l_Lean_Meta_mkEqOfHEq(v_a_1654_, v___x_1589_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_dec(v_a_1654_);
v___y_1610_ = v_a_1651_;
v___y_1611_ = v___x_1655_;
goto v___jp_1609_;
}
else
{
lean_object* v_a_1656_; uint8_t v___x_1657_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_a_1656_);
v___x_1657_ = l_Lean_Exception_isInterrupt(v_a_1656_);
if (v___x_1657_ == 0)
{
uint8_t v___x_1658_; 
lean_inc(v_a_1656_);
v___x_1658_ = l_Lean_Exception_isRuntime(v_a_1656_);
v___y_1622_ = v___x_1655_;
v___y_1623_ = v___y_1646_;
v___y_1624_ = v_a_1651_;
v___y_1625_ = v_a_1656_;
v___y_1626_ = v___y_1649_;
v___y_1627_ = v___y_1648_;
v___y_1628_ = v___y_1647_;
v___y_1629_ = v_a_1654_;
v___y_1630_ = v___x_1658_;
goto v___jp_1621_;
}
else
{
v___y_1622_ = v___x_1655_;
v___y_1623_ = v___y_1646_;
v___y_1624_ = v_a_1651_;
v___y_1625_ = v_a_1656_;
v___y_1626_ = v___y_1649_;
v___y_1627_ = v___y_1648_;
v___y_1628_ = v___y_1647_;
v___y_1629_ = v_a_1654_;
v___y_1630_ = v___x_1657_;
goto v___jp_1621_;
}
}
}
}
v___jp_1659_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; 
v___x_1667_ = lean_array_get_size(v_a_1666_);
v___x_1668_ = lean_unsigned_to_nat(0u);
v___x_1669_ = lean_nat_dec_eq(v___x_1667_, v___x_1668_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_dec_ref(v___y_1663_);
lean_dec_ref(v___x_1642_);
v___x_1670_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__7, &l_Lean_Meta_rwMatcher___lam__1___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__7);
v___x_1671_ = l_Lean_MessageData_ofConstName(v___x_1592_, v___x_1669_);
v___x_1672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1670_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__9, &l_Lean_Meta_rwMatcher___lam__1___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__9);
v___x_1674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1672_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
v___x_1675_ = lean_array_to_list(v_a_1666_);
v___x_1676_ = lean_box(0);
v___x_1677_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1675_, v___x_1676_);
v___x_1678_ = l_Lean_MessageData_ofList(v___x_1677_);
v___x_1679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1674_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1679_, v___y_1662_, v___y_1664_, v___y_1661_, v___y_1660_);
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1680_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1680_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
else
{
lean_dec_ref(v_a_1666_);
lean_dec(v___x_1592_);
v___y_1644_ = v___y_1663_;
v___y_1645_ = v___y_1665_;
v___y_1646_ = v___y_1662_;
v___y_1647_ = v___y_1664_;
v___y_1648_ = v___y_1661_;
v___y_1649_ = v___y_1660_;
goto v___jp_1643_;
}
}
v___jp_1689_:
{
if (lean_obj_tag(v___y_1696_) == 0)
{
lean_object* v_a_1697_; 
v_a_1697_ = lean_ctor_get(v___y_1696_, 0);
lean_inc(v_a_1697_);
lean_dec_ref(v___y_1696_);
v___y_1660_ = v___y_1692_;
v___y_1661_ = v___y_1691_;
v___y_1662_ = v___y_1690_;
v___y_1663_ = v___y_1693_;
v___y_1664_ = v___y_1694_;
v___y_1665_ = v___y_1695_;
v_a_1666_ = v_a_1697_;
goto v___jp_1659_;
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
lean_dec_ref(v___y_1693_);
lean_dec_ref(v___x_1642_);
lean_dec(v___x_1592_);
v_a_1698_ = lean_ctor_get(v___y_1696_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___y_1696_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___y_1696_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___y_1696_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
v___jp_1709_:
{
lean_object* v___x_1716_; size_t v_sz_1717_; lean_object* v___x_1718_; 
v___x_1716_ = lean_box(0);
v_sz_1717_ = lean_array_size(v___x_1708_);
v___x_1718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8(v___x_1708_, v_sz_1717_, v___x_1707_, v___x_1716_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; uint8_t v___x_1722_; 
lean_dec_ref(v___x_1718_);
v___x_1719_ = lean_unsigned_to_nat(0u);
v___x_1720_ = lean_array_get_size(v___x_1708_);
v___x_1721_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__10));
v___x_1722_ = lean_nat_dec_lt(v___x_1719_, v___x_1720_);
if (v___x_1722_ == 0)
{
lean_dec_ref(v___x_1708_);
v___y_1660_ = v___y_1715_;
v___y_1661_ = v___y_1714_;
v___y_1662_ = v___y_1712_;
v___y_1663_ = v___y_1710_;
v___y_1664_ = v___y_1713_;
v___y_1665_ = v___y_1711_;
v_a_1666_ = v___x_1721_;
goto v___jp_1659_;
}
else
{
uint8_t v___x_1723_; 
v___x_1723_ = lean_nat_dec_le(v___x_1720_, v___x_1720_);
if (v___x_1723_ == 0)
{
if (v___x_1722_ == 0)
{
lean_dec_ref(v___x_1708_);
v___y_1660_ = v___y_1715_;
v___y_1661_ = v___y_1714_;
v___y_1662_ = v___y_1712_;
v___y_1663_ = v___y_1710_;
v___y_1664_ = v___y_1713_;
v___y_1665_ = v___y_1711_;
v_a_1666_ = v___x_1721_;
goto v___jp_1659_;
}
else
{
size_t v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = lean_usize_of_nat(v___x_1720_);
v___x_1725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__14(v___x_1593_, v___x_1708_, v___x_1707_, v___x_1724_, v___x_1721_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
lean_dec_ref(v___x_1708_);
v___y_1690_ = v___y_1712_;
v___y_1691_ = v___y_1714_;
v___y_1692_ = v___y_1715_;
v___y_1693_ = v___y_1710_;
v___y_1694_ = v___y_1713_;
v___y_1695_ = v___y_1711_;
v___y_1696_ = v___x_1725_;
goto v___jp_1689_;
}
}
else
{
size_t v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = lean_usize_of_nat(v___x_1720_);
v___x_1727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__14(v___x_1593_, v___x_1708_, v___x_1707_, v___x_1726_, v___x_1721_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
lean_dec_ref(v___x_1708_);
v___y_1690_ = v___y_1712_;
v___y_1691_ = v___y_1714_;
v___y_1692_ = v___y_1715_;
v___y_1693_ = v___y_1710_;
v___y_1694_ = v___y_1713_;
v___y_1695_ = v___y_1711_;
v___y_1696_ = v___x_1727_;
goto v___jp_1689_;
}
}
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
lean_dec_ref(v___y_1710_);
lean_dec_ref(v___x_1708_);
lean_dec_ref(v___x_1642_);
lean_dec(v___x_1592_);
v_a_1728_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1718_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1718_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
v___jp_1736_:
{
lean_object* v___x_1740_; 
lean_inc_ref(v_fst_1738_);
lean_inc_ref(v_e_1594_);
v___x_1740_ = l_Lean_Meta_isExprDefEq(v_e_1594_, v_fst_1738_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; uint8_t v___x_1742_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1741_);
lean_dec_ref(v___x_1740_);
v___x_1742_ = lean_unbox(v_a_1741_);
lean_dec(v_a_1741_);
if (v___x_1742_ == 0)
{
if (v___x_1593_ == 0)
{
lean_dec_ref(v_fst_1738_);
lean_dec_ref(v_e_1594_);
v___y_1710_ = v_snd_1739_;
v___y_1711_ = v_fst_1737_;
v___y_1712_ = v___y_1598_;
v___y_1713_ = v___y_1599_;
v___y_1714_ = v___y_1600_;
v___y_1715_ = v___y_1601_;
goto v___jp_1709_;
}
else
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
lean_dec_ref(v_snd_1739_);
lean_dec_ref(v___x_1708_);
lean_dec_ref(v___x_1642_);
v___x_1743_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__12, &l_Lean_Meta_rwMatcher___lam__1___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__12);
v___x_1744_ = l_Lean_MessageData_ofExpr(v_fst_1738_);
v___x_1745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1743_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
v___x_1746_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__14, &l_Lean_Meta_rwMatcher___lam__1___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__14);
v___x_1747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1745_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
v___x_1748_ = l_Lean_MessageData_ofConstName(v___x_1592_, v___y_1595_);
v___x_1749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1747_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
v___x_1750_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__16, &l_Lean_Meta_rwMatcher___lam__1___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__16);
v___x_1751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1749_);
lean_ctor_set(v___x_1751_, 1, v___x_1750_);
v___x_1752_ = l_Lean_MessageData_ofExpr(v_e_1594_);
v___x_1753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1751_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
v___x_1754_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
v___x_1755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1753_);
lean_ctor_set(v___x_1755_, 1, v___x_1754_);
v___x_1756_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1755_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1756_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1756_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
else
{
lean_dec_ref(v_fst_1738_);
lean_dec_ref(v_e_1594_);
v___y_1710_ = v_snd_1739_;
v___y_1711_ = v_fst_1737_;
v___y_1712_ = v___y_1598_;
v___y_1713_ = v___y_1599_;
v___y_1714_ = v___y_1600_;
v___y_1715_ = v___y_1601_;
goto v___jp_1709_;
}
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
lean_dec_ref(v_snd_1739_);
lean_dec_ref(v_fst_1738_);
lean_dec_ref(v___x_1708_);
lean_dec_ref(v___x_1642_);
lean_dec_ref(v_e_1594_);
lean_dec(v___x_1592_);
v_a_1765_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1740_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1740_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4___boxed(lean_object* v___x_1800_, lean_object* v___x_1801_, lean_object* v_fst_1802_, lean_object* v___x_1803_, lean_object* v___x_1804_, lean_object* v_e_1805_, lean_object* v___y_1806_, lean_object* v_snd_1807_, lean_object* v_____r_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
uint8_t v___x_100763__boxed_1814_; uint8_t v___x_100767__boxed_1815_; uint8_t v___y_100768__boxed_1816_; lean_object* v_res_1817_; 
v___x_100763__boxed_1814_ = lean_unbox(v___x_1800_);
v___x_100767__boxed_1815_ = lean_unbox(v___x_1804_);
v___y_100768__boxed_1816_ = lean_unbox(v___y_1806_);
v_res_1817_ = l_Lean_Meta_rwMatcher___lam__4(v___x_100763__boxed_1814_, v___x_1801_, v_fst_1802_, v___x_1803_, v___x_100767__boxed_1815_, v_e_1805_, v___y_100768__boxed_1816_, v_snd_1807_, v_____r_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec_ref(v_snd_1807_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__5(uint8_t v___x_1818_, lean_object* v___x_1819_, lean_object* v_fst_1820_, lean_object* v___x_1821_, uint8_t v___x_1822_, lean_object* v_e_1823_, lean_object* v_snd_1824_, lean_object* v_____r_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v___y_1832_; lean_object* v_proof_1833_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; uint8_t v___y_1858_; lean_object* v___x_1870_; lean_object* v___y_1872_; uint8_t v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; uint8_t v___y_1892_; lean_object* v___y_1893_; lean_object* v_a_1894_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; uint8_t v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; size_t v_sz_1934_; size_t v___x_1935_; lean_object* v___x_1936_; lean_object* v___y_1938_; uint8_t v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; uint8_t v___y_1971_; uint8_t v_fst_1995_; lean_object* v_fst_1996_; lean_object* v_snd_1997_; lean_object* v___x_2009_; lean_object* v___x_2010_; uint8_t v___x_2011_; 
v___x_1870_ = l_Lean_mkAppN(v___x_1819_, v_fst_1820_);
v_sz_1934_ = lean_array_size(v_fst_1820_);
v___x_1935_ = ((size_t)0ULL);
v___x_1936_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4(v_sz_1934_, v___x_1935_, v_fst_1820_);
v___x_2009_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__18));
v___x_2010_ = lean_unsigned_to_nat(4u);
v___x_2011_ = l_Lean_Expr_isAppOfArity(v_snd_1824_, v___x_2009_, v___x_2010_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v___x_2012_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__20));
v___x_2013_ = lean_unsigned_to_nat(3u);
v___x_2014_ = l_Lean_Expr_isAppOfArity(v_snd_1824_, v___x_2012_, v___x_2013_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
lean_dec_ref(v___x_1936_);
lean_dec_ref(v___x_1870_);
lean_dec_ref(v_e_1823_);
v___x_2015_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__22, &l_Lean_Meta_rwMatcher___lam__1___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__22);
v___x_2016_ = l_Lean_MessageData_ofConstName(v___x_1821_, v___x_1822_);
v___x_2017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2015_);
lean_ctor_set(v___x_2017_, 1, v___x_2016_);
v___x_2018_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__24, &l_Lean_Meta_rwMatcher___lam__1___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__24);
v___x_2019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2017_);
lean_ctor_set(v___x_2019_, 1, v___x_2018_);
v___x_2020_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_2019_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_2020_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2020_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
else
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2029_ = l_Lean_Expr_appFn_x21(v_snd_1824_);
v___x_2030_ = l_Lean_Expr_appArg_x21(v___x_2029_);
lean_dec_ref(v___x_2029_);
v___x_2031_ = l_Lean_Expr_appArg_x21(v_snd_1824_);
v_fst_1995_ = v___x_1822_;
v_fst_1996_ = v___x_2030_;
v_snd_1997_ = v___x_2031_;
goto v___jp_1994_;
}
}
else
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2032_ = l_Lean_Expr_appFn_x21(v_snd_1824_);
v___x_2033_ = l_Lean_Expr_appFn_x21(v___x_2032_);
lean_dec_ref(v___x_2032_);
v___x_2034_ = l_Lean_Expr_appArg_x21(v___x_2033_);
lean_dec_ref(v___x_2033_);
v___x_2035_ = l_Lean_Expr_appArg_x21(v_snd_1824_);
v_fst_1995_ = v___x_1818_;
v_fst_1996_ = v___x_2034_;
v_snd_1997_ = v___x_2035_;
goto v___jp_1994_;
}
v___jp_1831_:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1834_, 0, v_proof_1833_);
v___x_1835_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1835_, 0, v___y_1832_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
lean_ctor_set_uint8(v___x_1835_, sizeof(void*)*2, v___x_1818_);
v___x_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
return v___x_1836_;
}
v___jp_1837_:
{
if (lean_obj_tag(v___y_1839_) == 0)
{
lean_object* v_a_1840_; 
v_a_1840_ = lean_ctor_get(v___y_1839_, 0);
lean_inc(v_a_1840_);
lean_dec_ref(v___y_1839_);
v___y_1832_ = v___y_1838_;
v_proof_1833_ = v_a_1840_;
goto v___jp_1831_;
}
else
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
lean_dec_ref(v___y_1838_);
v_a_1841_ = lean_ctor_get(v___y_1839_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___y_1839_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___y_1839_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___y_1839_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
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
v___jp_1849_:
{
if (v___y_1858_ == 0)
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
lean_dec_ref(v___y_1850_);
v___x_1859_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__1, &l_Lean_Meta_rwMatcher___lam__1___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__1);
v___x_1860_ = l_Lean_MessageData_ofExpr(v___y_1855_);
v___x_1861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1859_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__3, &l_Lean_Meta_rwMatcher___lam__1___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__3);
v___x_1863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1861_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = l_Lean_Exception_toMessageData(v___y_1857_);
v___x_1865_ = l_Lean_indentD(v___x_1864_);
v___x_1866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1863_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v___x_1867_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__5, &l_Lean_Meta_rwMatcher___lam__1___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__5);
v___x_1868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1866_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
v___x_1869_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1868_, v___y_1851_, v___y_1853_, v___y_1852_, v___y_1856_);
v___y_1838_ = v___y_1854_;
v___y_1839_ = v___x_1869_;
goto v___jp_1837_;
}
else
{
lean_dec_ref(v___y_1857_);
lean_dec_ref(v___y_1855_);
v___y_1838_ = v___y_1854_;
v___y_1839_ = v___y_1850_;
goto v___jp_1837_;
}
}
v___jp_1871_:
{
lean_object* v___x_1878_; lean_object* v_a_1879_; lean_object* v___x_1880_; 
v___x_1878_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___y_1872_, v___y_1875_);
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_a_1879_);
lean_dec_ref(v___x_1878_);
v___x_1880_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1870_, v___y_1875_);
if (v___y_1873_ == 0)
{
lean_object* v_a_1881_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref(v___x_1880_);
v___y_1832_ = v_a_1879_;
v_proof_1833_ = v_a_1881_;
goto v___jp_1831_;
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1883_; 
v_a_1882_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1882_);
lean_dec_ref(v___x_1880_);
lean_inc(v_a_1882_);
v___x_1883_ = l_Lean_Meta_mkEqOfHEq(v_a_1882_, v___x_1818_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_dec(v_a_1882_);
v___y_1838_ = v_a_1879_;
v___y_1839_ = v___x_1883_;
goto v___jp_1837_;
}
else
{
lean_object* v_a_1884_; uint8_t v___x_1885_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
v___x_1885_ = l_Lean_Exception_isInterrupt(v_a_1884_);
if (v___x_1885_ == 0)
{
uint8_t v___x_1886_; 
lean_inc(v_a_1884_);
v___x_1886_ = l_Lean_Exception_isRuntime(v_a_1884_);
v___y_1850_ = v___x_1883_;
v___y_1851_ = v___y_1874_;
v___y_1852_ = v___y_1876_;
v___y_1853_ = v___y_1875_;
v___y_1854_ = v_a_1879_;
v___y_1855_ = v_a_1882_;
v___y_1856_ = v___y_1877_;
v___y_1857_ = v_a_1884_;
v___y_1858_ = v___x_1886_;
goto v___jp_1849_;
}
else
{
v___y_1850_ = v___x_1883_;
v___y_1851_ = v___y_1874_;
v___y_1852_ = v___y_1876_;
v___y_1853_ = v___y_1875_;
v___y_1854_ = v_a_1879_;
v___y_1855_ = v_a_1882_;
v___y_1856_ = v___y_1877_;
v___y_1857_ = v_a_1884_;
v___y_1858_ = v___x_1885_;
goto v___jp_1849_;
}
}
}
}
v___jp_1887_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; uint8_t v___x_1897_; 
v___x_1895_ = lean_array_get_size(v_a_1894_);
v___x_1896_ = lean_unsigned_to_nat(0u);
v___x_1897_ = lean_nat_dec_eq(v___x_1895_, v___x_1896_);
if (v___x_1897_ == 0)
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_dec_ref(v___y_1888_);
lean_dec_ref(v___x_1870_);
v___x_1898_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__7, &l_Lean_Meta_rwMatcher___lam__1___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__7);
v___x_1899_ = l_Lean_MessageData_ofConstName(v___x_1821_, v___x_1822_);
v___x_1900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1898_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1901_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__9, &l_Lean_Meta_rwMatcher___lam__1___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__9);
v___x_1902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1900_);
lean_ctor_set(v___x_1902_, 1, v___x_1901_);
v___x_1903_ = lean_array_to_list(v_a_1894_);
v___x_1904_ = lean_box(0);
v___x_1905_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1903_, v___x_1904_);
v___x_1906_ = l_Lean_MessageData_ofList(v___x_1905_);
v___x_1907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1902_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1907_, v___y_1893_, v___y_1891_, v___y_1890_, v___y_1889_);
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1908_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1908_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
else
{
lean_dec_ref(v_a_1894_);
lean_dec(v___x_1821_);
v___y_1872_ = v___y_1888_;
v___y_1873_ = v___y_1892_;
v___y_1874_ = v___y_1893_;
v___y_1875_ = v___y_1891_;
v___y_1876_ = v___y_1890_;
v___y_1877_ = v___y_1889_;
goto v___jp_1871_;
}
}
v___jp_1917_:
{
if (lean_obj_tag(v___y_1924_) == 0)
{
lean_object* v_a_1925_; 
v_a_1925_ = lean_ctor_get(v___y_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref(v___y_1924_);
v___y_1888_ = v___y_1918_;
v___y_1889_ = v___y_1919_;
v___y_1890_ = v___y_1921_;
v___y_1891_ = v___y_1920_;
v___y_1892_ = v___y_1922_;
v___y_1893_ = v___y_1923_;
v_a_1894_ = v_a_1925_;
goto v___jp_1887_;
}
else
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_dec_ref(v___y_1918_);
lean_dec_ref(v___x_1870_);
lean_dec(v___x_1821_);
v_a_1926_ = lean_ctor_get(v___y_1924_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___y_1924_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___y_1924_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___y_1924_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
v___jp_1937_:
{
lean_object* v___x_1944_; size_t v_sz_1945_; lean_object* v___x_1946_; 
v___x_1944_ = lean_box(0);
v_sz_1945_ = lean_array_size(v___x_1936_);
v___x_1946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8(v___x_1936_, v_sz_1945_, v___x_1935_, v___x_1944_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; uint8_t v___x_1950_; 
lean_dec_ref(v___x_1946_);
v___x_1947_ = lean_unsigned_to_nat(0u);
v___x_1948_ = lean_array_get_size(v___x_1936_);
v___x_1949_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__10));
v___x_1950_ = lean_nat_dec_lt(v___x_1947_, v___x_1948_);
if (v___x_1950_ == 0)
{
lean_dec_ref(v___x_1936_);
v___y_1888_ = v___y_1938_;
v___y_1889_ = v___y_1943_;
v___y_1890_ = v___y_1942_;
v___y_1891_ = v___y_1941_;
v___y_1892_ = v___y_1939_;
v___y_1893_ = v___y_1940_;
v_a_1894_ = v___x_1949_;
goto v___jp_1887_;
}
else
{
uint8_t v___x_1951_; 
v___x_1951_ = lean_nat_dec_le(v___x_1948_, v___x_1948_);
if (v___x_1951_ == 0)
{
if (v___x_1950_ == 0)
{
lean_dec_ref(v___x_1936_);
v___y_1888_ = v___y_1938_;
v___y_1889_ = v___y_1943_;
v___y_1890_ = v___y_1942_;
v___y_1891_ = v___y_1941_;
v___y_1892_ = v___y_1939_;
v___y_1893_ = v___y_1940_;
v_a_1894_ = v___x_1949_;
goto v___jp_1887_;
}
else
{
size_t v___x_1952_; lean_object* v___x_1953_; 
v___x_1952_ = lean_usize_of_nat(v___x_1948_);
v___x_1953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(v___x_1822_, v___x_1936_, v___x_1935_, v___x_1952_, v___x_1949_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
lean_dec_ref(v___x_1936_);
v___y_1918_ = v___y_1938_;
v___y_1919_ = v___y_1943_;
v___y_1920_ = v___y_1941_;
v___y_1921_ = v___y_1942_;
v___y_1922_ = v___y_1939_;
v___y_1923_ = v___y_1940_;
v___y_1924_ = v___x_1953_;
goto v___jp_1917_;
}
}
else
{
size_t v___x_1954_; lean_object* v___x_1955_; 
v___x_1954_ = lean_usize_of_nat(v___x_1948_);
v___x_1955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(v___x_1822_, v___x_1936_, v___x_1935_, v___x_1954_, v___x_1949_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
lean_dec_ref(v___x_1936_);
v___y_1918_ = v___y_1938_;
v___y_1919_ = v___y_1943_;
v___y_1920_ = v___y_1941_;
v___y_1921_ = v___y_1942_;
v___y_1922_ = v___y_1939_;
v___y_1923_ = v___y_1940_;
v___y_1924_ = v___x_1955_;
goto v___jp_1917_;
}
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_dec_ref(v___y_1938_);
lean_dec_ref(v___x_1936_);
lean_dec_ref(v___x_1870_);
lean_dec(v___x_1821_);
v_a_1956_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1946_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1946_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
v___jp_1964_:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
lean_dec_ref(v___y_1965_);
v___x_1972_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__12, &l_Lean_Meta_rwMatcher___lam__1___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__12);
v___x_1973_ = l_Lean_MessageData_ofExpr(v___y_1966_);
v___x_1974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1972_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
v___x_1975_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__14, &l_Lean_Meta_rwMatcher___lam__1___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__14);
v___x_1976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1974_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
v___x_1977_ = l_Lean_MessageData_ofConstName(v___x_1821_, v___x_1822_);
v___x_1978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1976_);
lean_ctor_set(v___x_1978_, 1, v___x_1977_);
v___x_1979_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__16, &l_Lean_Meta_rwMatcher___lam__1___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__16);
v___x_1980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1978_);
lean_ctor_set(v___x_1980_, 1, v___x_1979_);
v___x_1981_ = l_Lean_MessageData_ofExpr(v_e_1823_);
v___x_1982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1980_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___x_1983_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
v___x_1984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1982_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v___x_1985_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1984_, v___y_1969_, v___y_1967_, v___y_1968_, v___y_1970_);
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1985_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1985_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
v___jp_1994_:
{
lean_object* v___x_1998_; 
lean_inc_ref(v_fst_1996_);
lean_inc_ref(v_e_1823_);
v___x_1998_ = l_Lean_Meta_isExprDefEq(v_e_1823_, v_fst_1996_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; uint8_t v___x_2000_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref(v___x_1998_);
v___x_2000_ = lean_unbox(v_a_1999_);
lean_dec(v_a_1999_);
if (v___x_2000_ == 0)
{
lean_dec_ref(v___x_1936_);
lean_dec_ref(v___x_1870_);
v___y_1965_ = v_snd_1997_;
v___y_1966_ = v_fst_1996_;
v___y_1967_ = v___y_1827_;
v___y_1968_ = v___y_1828_;
v___y_1969_ = v___y_1826_;
v___y_1970_ = v___y_1829_;
v___y_1971_ = v_fst_1995_;
goto v___jp_1964_;
}
else
{
if (v___x_1822_ == 0)
{
lean_dec_ref(v_fst_1996_);
lean_dec_ref(v_e_1823_);
v___y_1938_ = v_snd_1997_;
v___y_1939_ = v_fst_1995_;
v___y_1940_ = v___y_1826_;
v___y_1941_ = v___y_1827_;
v___y_1942_ = v___y_1828_;
v___y_1943_ = v___y_1829_;
goto v___jp_1937_;
}
else
{
lean_dec_ref(v___x_1936_);
lean_dec_ref(v___x_1870_);
v___y_1965_ = v_snd_1997_;
v___y_1966_ = v_fst_1996_;
v___y_1967_ = v___y_1827_;
v___y_1968_ = v___y_1828_;
v___y_1969_ = v___y_1826_;
v___y_1970_ = v___y_1829_;
v___y_1971_ = v_fst_1995_;
goto v___jp_1964_;
}
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec_ref(v_snd_1997_);
lean_dec_ref(v_fst_1996_);
lean_dec_ref(v___x_1936_);
lean_dec_ref(v___x_1870_);
lean_dec_ref(v_e_1823_);
lean_dec(v___x_1821_);
v_a_2001_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1998_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1998_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__5___boxed(lean_object* v___x_2036_, lean_object* v___x_2037_, lean_object* v_fst_2038_, lean_object* v___x_2039_, lean_object* v___x_2040_, lean_object* v_e_2041_, lean_object* v_snd_2042_, lean_object* v_____r_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
uint8_t v___x_101251__boxed_2049_; uint8_t v___x_101255__boxed_2050_; lean_object* v_res_2051_; 
v___x_101251__boxed_2049_ = lean_unbox(v___x_2036_);
v___x_101255__boxed_2050_ = lean_unbox(v___x_2040_);
v_res_2051_ = l_Lean_Meta_rwMatcher___lam__5(v___x_101251__boxed_2049_, v___x_2037_, v_fst_2038_, v___x_2039_, v___x_101255__boxed_2050_, v_e_2041_, v_snd_2042_, v_____r_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec_ref(v_snd_2042_);
return v_res_2051_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2052_; double v___x_2053_; 
v___x_2052_ = lean_unsigned_to_nat(0u);
v___x_2053_ = lean_float_of_nat(v___x_2052_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(lean_object* v_cls_2057_, lean_object* v_msg_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v_ref_2064_; lean_object* v___x_2065_; lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2110_; 
v_ref_2064_ = lean_ctor_get(v___y_2061_, 5);
v___x_2065_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3_spec__4(v_msg_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2068_ = v___x_2065_;
v_isShared_2069_ = v_isSharedCheck_2110_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2065_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2110_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2070_; lean_object* v_traceState_2071_; lean_object* v_env_2072_; lean_object* v_nextMacroScope_2073_; lean_object* v_ngen_2074_; lean_object* v_auxDeclNGen_2075_; lean_object* v_cache_2076_; lean_object* v_messages_2077_; lean_object* v_infoState_2078_; lean_object* v_snapshotTasks_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2109_; 
v___x_2070_ = lean_st_ref_take(v___y_2062_);
v_traceState_2071_ = lean_ctor_get(v___x_2070_, 4);
v_env_2072_ = lean_ctor_get(v___x_2070_, 0);
v_nextMacroScope_2073_ = lean_ctor_get(v___x_2070_, 1);
v_ngen_2074_ = lean_ctor_get(v___x_2070_, 2);
v_auxDeclNGen_2075_ = lean_ctor_get(v___x_2070_, 3);
v_cache_2076_ = lean_ctor_get(v___x_2070_, 5);
v_messages_2077_ = lean_ctor_get(v___x_2070_, 6);
v_infoState_2078_ = lean_ctor_get(v___x_2070_, 7);
v_snapshotTasks_2079_ = lean_ctor_get(v___x_2070_, 8);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2081_ = v___x_2070_;
v_isShared_2082_ = v_isSharedCheck_2109_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_snapshotTasks_2079_);
lean_inc(v_infoState_2078_);
lean_inc(v_messages_2077_);
lean_inc(v_cache_2076_);
lean_inc(v_traceState_2071_);
lean_inc(v_auxDeclNGen_2075_);
lean_inc(v_ngen_2074_);
lean_inc(v_nextMacroScope_2073_);
lean_inc(v_env_2072_);
lean_dec(v___x_2070_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2109_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
uint64_t v_tid_2083_; lean_object* v_traces_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2108_; 
v_tid_2083_ = lean_ctor_get_uint64(v_traceState_2071_, sizeof(void*)*1);
v_traces_2084_ = lean_ctor_get(v_traceState_2071_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_traceState_2071_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2086_ = v_traceState_2071_;
v_isShared_2087_ = v_isSharedCheck_2108_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_traces_2084_);
lean_dec(v_traceState_2071_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2108_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2088_; double v___x_2089_; uint8_t v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2098_; 
v___x_2088_ = lean_box(0);
v___x_2089_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0);
v___x_2090_ = 0;
v___x_2091_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__1));
v___x_2092_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2092_, 0, v_cls_2057_);
lean_ctor_set(v___x_2092_, 1, v___x_2088_);
lean_ctor_set(v___x_2092_, 2, v___x_2091_);
lean_ctor_set_float(v___x_2092_, sizeof(void*)*3, v___x_2089_);
lean_ctor_set_float(v___x_2092_, sizeof(void*)*3 + 8, v___x_2089_);
lean_ctor_set_uint8(v___x_2092_, sizeof(void*)*3 + 16, v___x_2090_);
v___x_2093_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__2));
v___x_2094_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2092_);
lean_ctor_set(v___x_2094_, 1, v_a_2066_);
lean_ctor_set(v___x_2094_, 2, v___x_2093_);
lean_inc(v_ref_2064_);
v___x_2095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2095_, 0, v_ref_2064_);
lean_ctor_set(v___x_2095_, 1, v___x_2094_);
v___x_2096_ = l_Lean_PersistentArray_push___redArg(v_traces_2084_, v___x_2095_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 0, v___x_2096_);
v___x_2098_ = v___x_2086_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2096_);
lean_ctor_set_uint64(v_reuseFailAlloc_2107_, sizeof(void*)*1, v_tid_2083_);
v___x_2098_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v___x_2100_; 
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 4, v___x_2098_);
v___x_2100_ = v___x_2081_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_env_2072_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v_nextMacroScope_2073_);
lean_ctor_set(v_reuseFailAlloc_2106_, 2, v_ngen_2074_);
lean_ctor_set(v_reuseFailAlloc_2106_, 3, v_auxDeclNGen_2075_);
lean_ctor_set(v_reuseFailAlloc_2106_, 4, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2106_, 5, v_cache_2076_);
lean_ctor_set(v_reuseFailAlloc_2106_, 6, v_messages_2077_);
lean_ctor_set(v_reuseFailAlloc_2106_, 7, v_infoState_2078_);
lean_ctor_set(v_reuseFailAlloc_2106_, 8, v_snapshotTasks_2079_);
v___x_2100_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2104_; 
v___x_2101_ = lean_st_ref_set(v___y_2062_, v___x_2100_);
v___x_2102_ = lean_box(0);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 0, v___x_2102_);
v___x_2104_ = v___x_2068_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2102_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___boxed(lean_object* v_cls_2111_, lean_object* v_msg_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(v_cls_2111_, v_msg_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_rwMatcher_spec__15(lean_object* v_b_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v___x_2125_; 
lean_inc_ref(v_b_2119_);
v___x_2125_ = l_Lean_Meta_reduceRecMatcher_x3f(v_b_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2139_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2128_ = v___x_2125_;
v_isShared_2129_ = v_isSharedCheck_2139_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2125_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2139_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
if (lean_obj_tag(v_a_2126_) == 1)
{
lean_object* v_val_2130_; lean_object* v___x_2131_; 
lean_del_object(v___x_2128_);
lean_dec_ref(v_b_2119_);
v_val_2130_ = lean_ctor_get(v_a_2126_, 0);
lean_inc(v_val_2130_);
lean_dec_ref(v_a_2126_);
v___x_2131_ = l_Lean_Expr_headBeta(v_val_2130_);
v_b_2119_ = v___x_2131_;
goto _start;
}
else
{
lean_object* v___x_2133_; uint8_t v___x_2134_; 
lean_dec(v_a_2126_);
lean_inc_ref(v_b_2119_);
v___x_2133_ = l_Lean_Expr_headBeta(v_b_2119_);
v___x_2134_ = lean_expr_eqv(v_b_2119_, v___x_2133_);
if (v___x_2134_ == 0)
{
lean_del_object(v___x_2128_);
lean_dec_ref(v_b_2119_);
v_b_2119_ = v___x_2133_;
goto _start;
}
else
{
lean_object* v___x_2137_; 
lean_dec_ref(v___x_2133_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 0, v_b_2119_);
v___x_2137_ = v___x_2128_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_b_2119_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_dec_ref(v_b_2119_);
v_a_2140_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2125_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2125_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_rwMatcher_spec__15___boxed(lean_object* v_b_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_rwMatcher_spec__15(v_b_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__17(lean_object* v_opts_2155_, lean_object* v_opt_2156_){
_start:
{
lean_object* v_name_2157_; lean_object* v_defValue_2158_; lean_object* v_map_2159_; lean_object* v___x_2160_; 
v_name_2157_ = lean_ctor_get(v_opt_2156_, 0);
v_defValue_2158_ = lean_ctor_get(v_opt_2156_, 1);
v_map_2159_ = lean_ctor_get(v_opts_2155_, 0);
v___x_2160_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2159_, v_name_2157_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_inc(v_defValue_2158_);
return v_defValue_2158_;
}
else
{
lean_object* v_val_2161_; 
v_val_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_val_2161_);
lean_dec_ref(v___x_2160_);
if (lean_obj_tag(v_val_2161_) == 3)
{
lean_object* v_v_2162_; 
v_v_2162_ = lean_ctor_get(v_val_2161_, 0);
lean_inc(v_v_2162_);
lean_dec_ref(v_val_2161_);
return v_v_2162_;
}
else
{
lean_dec(v_val_2161_);
lean_inc(v_defValue_2158_);
return v_defValue_2158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__17___boxed(lean_object* v_opts_2163_, lean_object* v_opt_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__17(v_opts_2163_, v_opt_2164_);
lean_dec_ref(v_opt_2164_);
lean_dec_ref(v_opts_2163_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16___redArg(lean_object* v_x_2166_){
_start:
{
if (lean_obj_tag(v_x_2166_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
v_a_2168_ = lean_ctor_get(v_x_2166_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v_x_2166_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v_x_2166_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v_x_2166_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
lean_ctor_set_tag(v___x_2170_, 1);
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
v_a_2176_ = lean_ctor_get(v_x_2166_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v_x_2166_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v_x_2166_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v_x_2166_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
lean_ctor_set_tag(v___x_2178_, 0);
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16___redArg___boxed(lean_object* v_x_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16___redArg(v_x_2184_);
return v_res_2186_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14(lean_object* v_e_2187_){
_start:
{
if (lean_obj_tag(v_e_2187_) == 0)
{
uint8_t v___x_2188_; 
v___x_2188_ = 2;
return v___x_2188_;
}
else
{
uint8_t v___x_2189_; 
v___x_2189_ = 0;
return v___x_2189_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14___boxed(lean_object* v_e_2190_){
_start:
{
uint8_t v_res_2191_; lean_object* v_r_2192_; 
v_res_2191_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14(v_e_2190_);
lean_dec_ref(v_e_2190_);
v_r_2192_ = lean_box(v_res_2191_);
return v_r_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15_spec__17(size_t v_sz_2193_, size_t v_i_2194_, lean_object* v_bs_2195_){
_start:
{
uint8_t v___x_2196_; 
v___x_2196_ = lean_usize_dec_lt(v_i_2194_, v_sz_2193_);
if (v___x_2196_ == 0)
{
return v_bs_2195_;
}
else
{
lean_object* v_v_2197_; lean_object* v_msg_2198_; lean_object* v___x_2199_; lean_object* v_bs_x27_2200_; size_t v___x_2201_; size_t v___x_2202_; lean_object* v___x_2203_; 
v_v_2197_ = lean_array_uget_borrowed(v_bs_2195_, v_i_2194_);
v_msg_2198_ = lean_ctor_get(v_v_2197_, 1);
lean_inc_ref(v_msg_2198_);
v___x_2199_ = lean_unsigned_to_nat(0u);
v_bs_x27_2200_ = lean_array_uset(v_bs_2195_, v_i_2194_, v___x_2199_);
v___x_2201_ = ((size_t)1ULL);
v___x_2202_ = lean_usize_add(v_i_2194_, v___x_2201_);
v___x_2203_ = lean_array_uset(v_bs_x27_2200_, v_i_2194_, v_msg_2198_);
v_i_2194_ = v___x_2202_;
v_bs_2195_ = v___x_2203_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15_spec__17___boxed(lean_object* v_sz_2205_, lean_object* v_i_2206_, lean_object* v_bs_2207_){
_start:
{
size_t v_sz_boxed_2208_; size_t v_i_boxed_2209_; lean_object* v_res_2210_; 
v_sz_boxed_2208_ = lean_unbox_usize(v_sz_2205_);
lean_dec(v_sz_2205_);
v_i_boxed_2209_ = lean_unbox_usize(v_i_2206_);
lean_dec(v_i_2206_);
v_res_2210_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15_spec__17(v_sz_boxed_2208_, v_i_boxed_2209_, v_bs_2207_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15(lean_object* v_oldTraces_2211_, lean_object* v_data_2212_, lean_object* v_ref_2213_, lean_object* v_msg_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v_fileName_2220_; lean_object* v_fileMap_2221_; lean_object* v_options_2222_; lean_object* v_currRecDepth_2223_; lean_object* v_maxRecDepth_2224_; lean_object* v_ref_2225_; lean_object* v_currNamespace_2226_; lean_object* v_openDecls_2227_; lean_object* v_initHeartbeats_2228_; lean_object* v_maxHeartbeats_2229_; lean_object* v_quotContext_2230_; lean_object* v_currMacroScope_2231_; uint8_t v_diag_2232_; lean_object* v_cancelTk_x3f_2233_; uint8_t v_suppressElabErrors_2234_; lean_object* v_inheritedTraceOptions_2235_; lean_object* v___x_2236_; lean_object* v_traceState_2237_; lean_object* v_traces_2238_; lean_object* v_ref_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; size_t v_sz_2242_; size_t v___x_2243_; lean_object* v___x_2244_; lean_object* v_msg_2245_; lean_object* v___x_2246_; lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2284_; 
v_fileName_2220_ = lean_ctor_get(v___y_2217_, 0);
v_fileMap_2221_ = lean_ctor_get(v___y_2217_, 1);
v_options_2222_ = lean_ctor_get(v___y_2217_, 2);
v_currRecDepth_2223_ = lean_ctor_get(v___y_2217_, 3);
v_maxRecDepth_2224_ = lean_ctor_get(v___y_2217_, 4);
v_ref_2225_ = lean_ctor_get(v___y_2217_, 5);
v_currNamespace_2226_ = lean_ctor_get(v___y_2217_, 6);
v_openDecls_2227_ = lean_ctor_get(v___y_2217_, 7);
v_initHeartbeats_2228_ = lean_ctor_get(v___y_2217_, 8);
v_maxHeartbeats_2229_ = lean_ctor_get(v___y_2217_, 9);
v_quotContext_2230_ = lean_ctor_get(v___y_2217_, 10);
v_currMacroScope_2231_ = lean_ctor_get(v___y_2217_, 11);
v_diag_2232_ = lean_ctor_get_uint8(v___y_2217_, sizeof(void*)*14);
v_cancelTk_x3f_2233_ = lean_ctor_get(v___y_2217_, 12);
v_suppressElabErrors_2234_ = lean_ctor_get_uint8(v___y_2217_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2235_ = lean_ctor_get(v___y_2217_, 13);
v___x_2236_ = lean_st_ref_get(v___y_2218_);
v_traceState_2237_ = lean_ctor_get(v___x_2236_, 4);
lean_inc_ref(v_traceState_2237_);
lean_dec(v___x_2236_);
v_traces_2238_ = lean_ctor_get(v_traceState_2237_, 0);
lean_inc_ref(v_traces_2238_);
lean_dec_ref(v_traceState_2237_);
v_ref_2239_ = l_Lean_replaceRef(v_ref_2213_, v_ref_2225_);
lean_inc_ref(v_inheritedTraceOptions_2235_);
lean_inc(v_cancelTk_x3f_2233_);
lean_inc(v_currMacroScope_2231_);
lean_inc(v_quotContext_2230_);
lean_inc(v_maxHeartbeats_2229_);
lean_inc(v_initHeartbeats_2228_);
lean_inc(v_openDecls_2227_);
lean_inc(v_currNamespace_2226_);
lean_inc(v_maxRecDepth_2224_);
lean_inc(v_currRecDepth_2223_);
lean_inc_ref(v_options_2222_);
lean_inc_ref(v_fileMap_2221_);
lean_inc_ref(v_fileName_2220_);
v___x_2240_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2240_, 0, v_fileName_2220_);
lean_ctor_set(v___x_2240_, 1, v_fileMap_2221_);
lean_ctor_set(v___x_2240_, 2, v_options_2222_);
lean_ctor_set(v___x_2240_, 3, v_currRecDepth_2223_);
lean_ctor_set(v___x_2240_, 4, v_maxRecDepth_2224_);
lean_ctor_set(v___x_2240_, 5, v_ref_2239_);
lean_ctor_set(v___x_2240_, 6, v_currNamespace_2226_);
lean_ctor_set(v___x_2240_, 7, v_openDecls_2227_);
lean_ctor_set(v___x_2240_, 8, v_initHeartbeats_2228_);
lean_ctor_set(v___x_2240_, 9, v_maxHeartbeats_2229_);
lean_ctor_set(v___x_2240_, 10, v_quotContext_2230_);
lean_ctor_set(v___x_2240_, 11, v_currMacroScope_2231_);
lean_ctor_set(v___x_2240_, 12, v_cancelTk_x3f_2233_);
lean_ctor_set(v___x_2240_, 13, v_inheritedTraceOptions_2235_);
lean_ctor_set_uint8(v___x_2240_, sizeof(void*)*14, v_diag_2232_);
lean_ctor_set_uint8(v___x_2240_, sizeof(void*)*14 + 1, v_suppressElabErrors_2234_);
v___x_2241_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2238_);
lean_dec_ref(v_traces_2238_);
v_sz_2242_ = lean_array_size(v___x_2241_);
v___x_2243_ = ((size_t)0ULL);
v___x_2244_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15_spec__17(v_sz_2242_, v___x_2243_, v___x_2241_);
v_msg_2245_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2245_, 0, v_data_2212_);
lean_ctor_set(v_msg_2245_, 1, v_msg_2214_);
lean_ctor_set(v_msg_2245_, 2, v___x_2244_);
v___x_2246_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3_spec__4(v_msg_2245_, v___y_2215_, v___y_2216_, v___x_2240_, v___y_2218_);
lean_dec_ref(v___x_2240_);
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2249_ = v___x_2246_;
v_isShared_2250_ = v_isSharedCheck_2284_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2246_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2284_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2251_; lean_object* v_traceState_2252_; lean_object* v_env_2253_; lean_object* v_nextMacroScope_2254_; lean_object* v_ngen_2255_; lean_object* v_auxDeclNGen_2256_; lean_object* v_cache_2257_; lean_object* v_messages_2258_; lean_object* v_infoState_2259_; lean_object* v_snapshotTasks_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2283_; 
v___x_2251_ = lean_st_ref_take(v___y_2218_);
v_traceState_2252_ = lean_ctor_get(v___x_2251_, 4);
v_env_2253_ = lean_ctor_get(v___x_2251_, 0);
v_nextMacroScope_2254_ = lean_ctor_get(v___x_2251_, 1);
v_ngen_2255_ = lean_ctor_get(v___x_2251_, 2);
v_auxDeclNGen_2256_ = lean_ctor_get(v___x_2251_, 3);
v_cache_2257_ = lean_ctor_get(v___x_2251_, 5);
v_messages_2258_ = lean_ctor_get(v___x_2251_, 6);
v_infoState_2259_ = lean_ctor_get(v___x_2251_, 7);
v_snapshotTasks_2260_ = lean_ctor_get(v___x_2251_, 8);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2262_ = v___x_2251_;
v_isShared_2263_ = v_isSharedCheck_2283_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_snapshotTasks_2260_);
lean_inc(v_infoState_2259_);
lean_inc(v_messages_2258_);
lean_inc(v_cache_2257_);
lean_inc(v_traceState_2252_);
lean_inc(v_auxDeclNGen_2256_);
lean_inc(v_ngen_2255_);
lean_inc(v_nextMacroScope_2254_);
lean_inc(v_env_2253_);
lean_dec(v___x_2251_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2283_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
uint64_t v_tid_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2281_; 
v_tid_2264_ = lean_ctor_get_uint64(v_traceState_2252_, sizeof(void*)*1);
v_isSharedCheck_2281_ = !lean_is_exclusive(v_traceState_2252_);
if (v_isSharedCheck_2281_ == 0)
{
lean_object* v_unused_2282_; 
v_unused_2282_ = lean_ctor_get(v_traceState_2252_, 0);
lean_dec(v_unused_2282_);
v___x_2266_ = v_traceState_2252_;
v_isShared_2267_ = v_isSharedCheck_2281_;
goto v_resetjp_2265_;
}
else
{
lean_dec(v_traceState_2252_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2281_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2271_; 
v___x_2268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2268_, 0, v_ref_2213_);
lean_ctor_set(v___x_2268_, 1, v_a_2247_);
v___x_2269_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2211_, v___x_2268_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 0, v___x_2269_);
v___x_2271_ = v___x_2266_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2269_);
lean_ctor_set_uint64(v_reuseFailAlloc_2280_, sizeof(void*)*1, v_tid_2264_);
v___x_2271_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
lean_object* v___x_2273_; 
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 4, v___x_2271_);
v___x_2273_ = v___x_2262_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_env_2253_);
lean_ctor_set(v_reuseFailAlloc_2279_, 1, v_nextMacroScope_2254_);
lean_ctor_set(v_reuseFailAlloc_2279_, 2, v_ngen_2255_);
lean_ctor_set(v_reuseFailAlloc_2279_, 3, v_auxDeclNGen_2256_);
lean_ctor_set(v_reuseFailAlloc_2279_, 4, v___x_2271_);
lean_ctor_set(v_reuseFailAlloc_2279_, 5, v_cache_2257_);
lean_ctor_set(v_reuseFailAlloc_2279_, 6, v_messages_2258_);
lean_ctor_set(v_reuseFailAlloc_2279_, 7, v_infoState_2259_);
lean_ctor_set(v_reuseFailAlloc_2279_, 8, v_snapshotTasks_2260_);
v___x_2273_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2277_; 
v___x_2274_ = lean_st_ref_set(v___y_2218_, v___x_2273_);
v___x_2275_ = lean_box(0);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 0, v___x_2275_);
v___x_2277_ = v___x_2249_;
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
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___boxed(lean_object* v_oldTraces_2285_, lean_object* v_data_2286_, lean_object* v_ref_2287_, lean_object* v_msg_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15(v_oldTraces_2285_, v_data_2286_, v_ref_2287_, v_msg_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
return v_res_2294_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__1(void){
_start:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2296_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__0));
v___x_2297_ = l_Lean_stringToMessageData(v___x_2296_);
return v___x_2297_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__2(void){
_start:
{
lean_object* v___x_2298_; double v___x_2299_; 
v___x_2298_ = lean_unsigned_to_nat(1000u);
v___x_2299_ = lean_float_of_nat(v___x_2298_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12(lean_object* v_cls_2300_, uint8_t v_collapsed_2301_, lean_object* v_tag_2302_, lean_object* v_opts_2303_, uint8_t v_clsEnabled_2304_, lean_object* v_oldTraces_2305_, lean_object* v_msg_2306_, lean_object* v_resStartStop_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_fst_2313_; lean_object* v_snd_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2412_; 
v_fst_2313_ = lean_ctor_get(v_resStartStop_2307_, 0);
v_snd_2314_ = lean_ctor_get(v_resStartStop_2307_, 1);
v_isSharedCheck_2412_ = !lean_is_exclusive(v_resStartStop_2307_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2316_ = v_resStartStop_2307_;
v_isShared_2317_ = v_isSharedCheck_2412_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_snd_2314_);
lean_inc(v_fst_2313_);
lean_dec(v_resStartStop_2307_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2412_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v_data_2321_; lean_object* v_fst_2332_; lean_object* v_snd_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2411_; 
v_fst_2332_ = lean_ctor_get(v_snd_2314_, 0);
v_snd_2333_ = lean_ctor_get(v_snd_2314_, 1);
v_isSharedCheck_2411_ = !lean_is_exclusive(v_snd_2314_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2335_ = v_snd_2314_;
v_isShared_2336_ = v_isSharedCheck_2411_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_snd_2333_);
lean_inc(v_fst_2332_);
lean_dec(v_snd_2314_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2411_;
goto v_resetjp_2334_;
}
v___jp_2318_:
{
lean_object* v___x_2322_; 
lean_inc(v___y_2320_);
v___x_2322_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15(v_oldTraces_2305_, v_data_2321_, v___y_2320_, v___y_2319_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v___x_2323_; 
lean_dec_ref(v___x_2322_);
v___x_2323_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16___redArg(v_fst_2313_);
return v___x_2323_;
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec(v_fst_2313_);
v_a_2324_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2322_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2322_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
v_resetjp_2334_:
{
lean_object* v___x_2337_; uint8_t v___x_2338_; lean_object* v___y_2340_; lean_object* v_a_2341_; uint8_t v___y_2365_; double v___y_2396_; 
v___x_2337_ = l_Lean_trace_profiler;
v___x_2338_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11(v_opts_2303_, v___x_2337_);
if (v___x_2338_ == 0)
{
v___y_2365_ = v___x_2338_;
goto v___jp_2364_;
}
else
{
lean_object* v___x_2401_; uint8_t v___x_2402_; 
v___x_2401_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2402_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11(v_opts_2303_, v___x_2401_);
if (v___x_2402_ == 0)
{
lean_object* v___x_2403_; lean_object* v___x_2404_; double v___x_2405_; double v___x_2406_; double v___x_2407_; 
v___x_2403_ = l_Lean_trace_profiler_threshold;
v___x_2404_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__17(v_opts_2303_, v___x_2403_);
v___x_2405_ = lean_float_of_nat(v___x_2404_);
v___x_2406_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__2);
v___x_2407_ = lean_float_div(v___x_2405_, v___x_2406_);
v___y_2396_ = v___x_2407_;
goto v___jp_2395_;
}
else
{
lean_object* v___x_2408_; lean_object* v___x_2409_; double v___x_2410_; 
v___x_2408_ = l_Lean_trace_profiler_threshold;
v___x_2409_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__17(v_opts_2303_, v___x_2408_);
v___x_2410_ = lean_float_of_nat(v___x_2409_);
v___y_2396_ = v___x_2410_;
goto v___jp_2395_;
}
}
v___jp_2339_:
{
uint8_t v_result_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2347_; 
v_result_2342_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14(v_fst_2313_);
v___x_2343_ = l_Lean_TraceResult_toEmoji(v_result_2342_);
v___x_2344_ = l_Lean_stringToMessageData(v___x_2343_);
v___x_2345_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__5, &l_Lean_Meta_rwMatcher___lam__1___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__5);
if (v_isShared_2336_ == 0)
{
lean_ctor_set_tag(v___x_2335_, 7);
lean_ctor_set(v___x_2335_, 1, v___x_2345_);
lean_ctor_set(v___x_2335_, 0, v___x_2344_);
v___x_2347_ = v___x_2335_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2344_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
lean_object* v_m_2349_; 
if (v_isShared_2317_ == 0)
{
lean_ctor_set_tag(v___x_2316_, 7);
lean_ctor_set(v___x_2316_, 1, v_a_2341_);
lean_ctor_set(v___x_2316_, 0, v___x_2347_);
v_m_2349_ = v___x_2316_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2347_);
lean_ctor_set(v_reuseFailAlloc_2357_, 1, v_a_2341_);
v_m_2349_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; double v___x_2352_; lean_object* v_data_2353_; 
v___x_2350_ = lean_box(v_result_2342_);
v___x_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2350_);
v___x_2352_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0);
lean_inc_ref(v_tag_2302_);
lean_inc_ref(v___x_2351_);
lean_inc(v_cls_2300_);
v_data_2353_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2353_, 0, v_cls_2300_);
lean_ctor_set(v_data_2353_, 1, v___x_2351_);
lean_ctor_set(v_data_2353_, 2, v_tag_2302_);
lean_ctor_set_float(v_data_2353_, sizeof(void*)*3, v___x_2352_);
lean_ctor_set_float(v_data_2353_, sizeof(void*)*3 + 8, v___x_2352_);
lean_ctor_set_uint8(v_data_2353_, sizeof(void*)*3 + 16, v_collapsed_2301_);
if (v___x_2338_ == 0)
{
lean_dec_ref(v___x_2351_);
lean_dec(v_snd_2333_);
lean_dec(v_fst_2332_);
lean_dec_ref(v_tag_2302_);
lean_dec(v_cls_2300_);
v___y_2319_ = v_m_2349_;
v___y_2320_ = v___y_2340_;
v_data_2321_ = v_data_2353_;
goto v___jp_2318_;
}
else
{
lean_object* v_data_2354_; double v___x_2355_; double v___x_2356_; 
lean_dec_ref(v_data_2353_);
v_data_2354_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2354_, 0, v_cls_2300_);
lean_ctor_set(v_data_2354_, 1, v___x_2351_);
lean_ctor_set(v_data_2354_, 2, v_tag_2302_);
v___x_2355_ = lean_unbox_float(v_fst_2332_);
lean_dec(v_fst_2332_);
lean_ctor_set_float(v_data_2354_, sizeof(void*)*3, v___x_2355_);
v___x_2356_ = lean_unbox_float(v_snd_2333_);
lean_dec(v_snd_2333_);
lean_ctor_set_float(v_data_2354_, sizeof(void*)*3 + 8, v___x_2356_);
lean_ctor_set_uint8(v_data_2354_, sizeof(void*)*3 + 16, v_collapsed_2301_);
v___y_2319_ = v_m_2349_;
v___y_2320_ = v___y_2340_;
v_data_2321_ = v_data_2354_;
goto v___jp_2318_;
}
}
}
}
v___jp_2359_:
{
lean_object* v_ref_2360_; lean_object* v___x_2361_; 
v_ref_2360_ = lean_ctor_get(v___y_2310_, 5);
lean_inc(v___y_2311_);
lean_inc_ref(v___y_2310_);
lean_inc(v___y_2309_);
lean_inc_ref(v___y_2308_);
lean_inc(v_fst_2313_);
v___x_2361_ = lean_apply_6(v_msg_2306_, v_fst_2313_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, lean_box(0));
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref(v___x_2361_);
v___y_2340_ = v_ref_2360_;
v_a_2341_ = v_a_2362_;
goto v___jp_2339_;
}
else
{
lean_object* v___x_2363_; 
lean_dec_ref(v___x_2361_);
v___x_2363_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__1);
v___y_2340_ = v_ref_2360_;
v_a_2341_ = v___x_2363_;
goto v___jp_2339_;
}
}
v___jp_2364_:
{
if (v_clsEnabled_2304_ == 0)
{
if (v___y_2365_ == 0)
{
lean_object* v___x_2366_; lean_object* v_traceState_2367_; lean_object* v_env_2368_; lean_object* v_nextMacroScope_2369_; lean_object* v_ngen_2370_; lean_object* v_auxDeclNGen_2371_; lean_object* v_cache_2372_; lean_object* v_messages_2373_; lean_object* v_infoState_2374_; lean_object* v_snapshotTasks_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2394_; 
lean_del_object(v___x_2335_);
lean_dec(v_snd_2333_);
lean_dec(v_fst_2332_);
lean_del_object(v___x_2316_);
lean_dec_ref(v_msg_2306_);
lean_dec_ref(v_tag_2302_);
lean_dec(v_cls_2300_);
v___x_2366_ = lean_st_ref_take(v___y_2311_);
v_traceState_2367_ = lean_ctor_get(v___x_2366_, 4);
v_env_2368_ = lean_ctor_get(v___x_2366_, 0);
v_nextMacroScope_2369_ = lean_ctor_get(v___x_2366_, 1);
v_ngen_2370_ = lean_ctor_get(v___x_2366_, 2);
v_auxDeclNGen_2371_ = lean_ctor_get(v___x_2366_, 3);
v_cache_2372_ = lean_ctor_get(v___x_2366_, 5);
v_messages_2373_ = lean_ctor_get(v___x_2366_, 6);
v_infoState_2374_ = lean_ctor_get(v___x_2366_, 7);
v_snapshotTasks_2375_ = lean_ctor_get(v___x_2366_, 8);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2377_ = v___x_2366_;
v_isShared_2378_ = v_isSharedCheck_2394_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_snapshotTasks_2375_);
lean_inc(v_infoState_2374_);
lean_inc(v_messages_2373_);
lean_inc(v_cache_2372_);
lean_inc(v_traceState_2367_);
lean_inc(v_auxDeclNGen_2371_);
lean_inc(v_ngen_2370_);
lean_inc(v_nextMacroScope_2369_);
lean_inc(v_env_2368_);
lean_dec(v___x_2366_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2394_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
uint64_t v_tid_2379_; lean_object* v_traces_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2393_; 
v_tid_2379_ = lean_ctor_get_uint64(v_traceState_2367_, sizeof(void*)*1);
v_traces_2380_ = lean_ctor_get(v_traceState_2367_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v_traceState_2367_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2382_ = v_traceState_2367_;
v_isShared_2383_ = v_isSharedCheck_2393_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_traces_2380_);
lean_dec(v_traceState_2367_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2393_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2384_; lean_object* v___x_2386_; 
v___x_2384_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2305_, v_traces_2380_);
lean_dec_ref(v_traces_2380_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 0, v___x_2384_);
v___x_2386_ = v___x_2382_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2384_);
lean_ctor_set_uint64(v_reuseFailAlloc_2392_, sizeof(void*)*1, v_tid_2379_);
v___x_2386_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
lean_object* v___x_2388_; 
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 4, v___x_2386_);
v___x_2388_ = v___x_2377_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_env_2368_);
lean_ctor_set(v_reuseFailAlloc_2391_, 1, v_nextMacroScope_2369_);
lean_ctor_set(v_reuseFailAlloc_2391_, 2, v_ngen_2370_);
lean_ctor_set(v_reuseFailAlloc_2391_, 3, v_auxDeclNGen_2371_);
lean_ctor_set(v_reuseFailAlloc_2391_, 4, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2391_, 5, v_cache_2372_);
lean_ctor_set(v_reuseFailAlloc_2391_, 6, v_messages_2373_);
lean_ctor_set(v_reuseFailAlloc_2391_, 7, v_infoState_2374_);
lean_ctor_set(v_reuseFailAlloc_2391_, 8, v_snapshotTasks_2375_);
v___x_2388_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = lean_st_ref_set(v___y_2311_, v___x_2388_);
v___x_2390_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16___redArg(v_fst_2313_);
return v___x_2390_;
}
}
}
}
}
else
{
goto v___jp_2359_;
}
}
else
{
goto v___jp_2359_;
}
}
v___jp_2395_:
{
double v___x_2397_; double v___x_2398_; double v___x_2399_; uint8_t v___x_2400_; 
v___x_2397_ = lean_unbox_float(v_snd_2333_);
v___x_2398_ = lean_unbox_float(v_fst_2332_);
v___x_2399_ = lean_float_sub(v___x_2397_, v___x_2398_);
v___x_2400_ = lean_float_decLt(v___y_2396_, v___x_2399_);
v___y_2365_ = v___x_2400_;
goto v___jp_2364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___boxed(lean_object* v_cls_2413_, lean_object* v_collapsed_2414_, lean_object* v_tag_2415_, lean_object* v_opts_2416_, lean_object* v_clsEnabled_2417_, lean_object* v_oldTraces_2418_, lean_object* v_msg_2419_, lean_object* v_resStartStop_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
uint8_t v_collapsed_boxed_2426_; uint8_t v_clsEnabled_boxed_2427_; lean_object* v_res_2428_; 
v_collapsed_boxed_2426_ = lean_unbox(v_collapsed_2414_);
v_clsEnabled_boxed_2427_ = lean_unbox(v_clsEnabled_2417_);
v_res_2428_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12(v_cls_2413_, v_collapsed_boxed_2426_, v_tag_2415_, v_opts_2416_, v_clsEnabled_boxed_2427_, v_oldTraces_2418_, v_msg_2419_, v_resStartStop_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec_ref(v_opts_2416_);
return v_res_2428_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__1(void){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__0));
v___x_2431_ = l_Lean_stringToMessageData(v___x_2430_);
return v___x_2431_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__3(void){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__2));
v___x_2434_ = l_Lean_stringToMessageData(v___x_2433_);
return v___x_2434_;
}
}
static double _init_l_Lean_Meta_rwMatcher___closed__4(void){
_start:
{
lean_object* v___x_2435_; double v___x_2436_; 
v___x_2435_ = lean_unsigned_to_nat(1000000000u);
v___x_2436_ = lean_float_of_nat(v___x_2435_);
return v___x_2436_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__6(void){
_start:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2438_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__5));
v___x_2439_ = l_Lean_stringToMessageData(v___x_2438_);
return v___x_2439_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__12(void){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__11));
v___x_2449_ = l_Lean_stringToMessageData(v___x_2448_);
return v___x_2449_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__14(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__13));
v___x_2452_ = l_Lean_stringToMessageData(v___x_2451_);
return v___x_2452_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__16(void){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__15));
v___x_2455_ = l_Lean_stringToMessageData(v___x_2454_);
return v___x_2455_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__18(void){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__17));
v___x_2458_ = l_Lean_stringToMessageData(v___x_2457_);
return v___x_2458_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__19(void){
_start:
{
lean_object* v___x_2459_; lean_object* v_dummy_2460_; 
v___x_2459_ = lean_box(0);
v_dummy_2460_ = l_Lean_Expr_sort___override(v___x_2459_);
return v_dummy_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher(lean_object* v_altIdx_2470_, lean_object* v_e_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_){
_start:
{
lean_object* v___y_2478_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; uint8_t v___y_2501_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v_a_2531_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; uint8_t v___y_2541_; uint8_t v___y_2546_; lean_object* v___y_2551_; uint8_t v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; uint8_t v___y_2560_; lean_object* v_a_2561_; lean_object* v___y_2571_; uint8_t v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; uint8_t v___y_2580_; lean_object* v_a_2581_; lean_object* v___y_2584_; uint8_t v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; uint8_t v___y_2593_; lean_object* v___y_2594_; uint8_t v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; uint8_t v___y_2614_; lean_object* v_a_2615_; uint8_t v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; uint8_t v___y_2637_; lean_object* v_a_2638_; uint8_t v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; uint8_t v___y_2650_; lean_object* v___y_2651_; uint8_t v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; uint8_t v___y_2665_; lean_object* v___y_2666_; uint8_t v___y_2667_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v___y_2670_; lean_object* v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; uint8_t v___y_2674_; uint8_t v___y_2740_; lean_object* v___x_2918_; uint8_t v___x_2919_; 
v___x_2918_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__22));
v___x_2919_ = l_Lean_Expr_isAppOf(v_e_2471_, v___x_2918_);
if (v___x_2919_ == 0)
{
lean_object* v___x_2920_; uint8_t v___x_2921_; 
v___x_2920_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__24));
v___x_2921_ = l_Lean_Expr_isAppOf(v_e_2471_, v___x_2920_);
v___y_2740_ = v___x_2921_;
goto v___jp_2739_;
}
else
{
v___y_2740_ = v___x_2919_;
goto v___jp_2739_;
}
v___jp_2477_:
{
if (lean_obj_tag(v___y_2478_) == 0)
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2487_; 
v_a_2479_ = lean_ctor_get(v___y_2478_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___y_2478_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2481_ = v___y_2478_;
v_isShared_2482_ = v_isSharedCheck_2487_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___y_2478_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2487_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v_a_2483_; lean_object* v___x_2485_; 
v_a_2483_ = lean_ctor_get(v_a_2479_, 0);
lean_inc(v_a_2483_);
lean_dec(v_a_2479_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 0, v_a_2483_);
v___x_2485_ = v___x_2481_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2483_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
else
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
v_a_2488_ = lean_ctor_get(v___y_2478_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___y_2478_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2490_ = v___y_2478_;
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___y_2478_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2493_; 
if (v_isShared_2491_ == 0)
{
v___x_2493_ = v___x_2490_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2488_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
}
v___jp_2496_:
{
if (v___y_2501_ == 0)
{
lean_object* v___x_2502_; lean_object* v_a_2503_; uint8_t v___x_2504_; 
lean_inc(v___y_2500_);
v___x_2502_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg(v___y_2500_, v_a_2474_);
v_a_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_a_2503_);
lean_dec_ref(v___x_2502_);
v___x_2504_ = lean_unbox(v_a_2503_);
lean_dec(v_a_2503_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
lean_dec(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
v___x_2505_ = lean_box(0);
lean_inc(v_a_2475_);
lean_inc_ref(v_a_2474_);
lean_inc(v_a_2473_);
lean_inc_ref(v_a_2472_);
v___x_2506_ = lean_apply_6(v___y_2497_, v___x_2505_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, lean_box(0));
v___y_2478_ = v___x_2506_;
goto v___jp_2477_;
}
else
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2507_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__1, &l_Lean_Meta_rwMatcher___closed__1_once, _init_l_Lean_Meta_rwMatcher___closed__1);
v___x_2508_ = l_Lean_MessageData_ofConstName(v___y_2499_, v___y_2501_);
v___x_2509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2507_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
v___x_2510_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__3, &l_Lean_Meta_rwMatcher___closed__3_once, _init_l_Lean_Meta_rwMatcher___closed__3);
v___x_2511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2509_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
v___x_2512_ = l_Lean_Exception_toMessageData(v___y_2498_);
v___x_2513_ = l_Lean_indentD(v___x_2512_);
v___x_2514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2511_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
v___x_2515_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(v___y_2500_, v___x_2514_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2517_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2516_);
lean_dec_ref(v___x_2515_);
lean_inc(v_a_2475_);
lean_inc_ref(v_a_2474_);
lean_inc(v_a_2473_);
lean_inc_ref(v_a_2472_);
v___x_2517_ = lean_apply_6(v___y_2497_, v_a_2516_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, lean_box(0));
v___y_2478_ = v___x_2517_;
goto v___jp_2477_;
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
lean_dec_ref(v___y_2497_);
v_a_2518_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2515_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2515_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
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
}
else
{
lean_object* v___x_2526_; 
lean_dec(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2497_);
v___x_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2526_, 0, v___y_2498_);
return v___x_2526_;
}
}
v___jp_2527_:
{
uint8_t v___x_2532_; 
v___x_2532_ = l_Lean_Exception_isInterrupt(v_a_2531_);
if (v___x_2532_ == 0)
{
uint8_t v___x_2533_; 
lean_inc_ref(v_a_2531_);
v___x_2533_ = l_Lean_Exception_isRuntime(v_a_2531_);
v___y_2497_ = v___y_2528_;
v___y_2498_ = v_a_2531_;
v___y_2499_ = v___y_2530_;
v___y_2500_ = v___y_2529_;
v___y_2501_ = v___x_2533_;
goto v___jp_2496_;
}
else
{
v___y_2497_ = v___y_2528_;
v___y_2498_ = v_a_2531_;
v___y_2499_ = v___y_2530_;
v___y_2500_ = v___y_2529_;
v___y_2501_ = v___x_2532_;
goto v___jp_2496_;
}
}
v___jp_2534_:
{
if (lean_obj_tag(v___y_2538_) == 0)
{
lean_dec(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
return v___y_2538_;
}
else
{
lean_object* v_a_2539_; 
v_a_2539_ = lean_ctor_get(v___y_2538_, 0);
lean_inc(v_a_2539_);
lean_dec_ref(v___y_2538_);
v___y_2528_ = v___y_2535_;
v___y_2529_ = v___y_2537_;
v___y_2530_ = v___y_2536_;
v_a_2531_ = v_a_2539_;
goto v___jp_2527_;
}
}
v___jp_2540_:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2542_ = lean_box(0);
v___x_2543_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2543_, 0, v_e_2471_);
lean_ctor_set(v___x_2543_, 1, v___x_2542_);
lean_ctor_set_uint8(v___x_2543_, sizeof(void*)*2, v___y_2541_);
v___x_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2543_);
return v___x_2544_;
}
v___jp_2545_:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2547_ = lean_box(0);
v___x_2548_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2548_, 0, v_e_2471_);
lean_ctor_set(v___x_2548_, 1, v___x_2547_);
lean_ctor_set_uint8(v___x_2548_, sizeof(void*)*2, v___y_2546_);
v___x_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2548_);
return v___x_2549_;
}
v___jp_2550_:
{
lean_object* v___x_2562_; double v___x_2563_; double v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2562_ = lean_io_get_num_heartbeats();
v___x_2563_ = lean_float_of_nat(v___y_2551_);
v___x_2564_ = lean_float_of_nat(v___x_2562_);
v___x_2565_ = lean_box_float(v___x_2563_);
v___x_2566_ = lean_box_float(v___x_2564_);
v___x_2567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2565_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
v___x_2568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2568_, 0, v_a_2561_);
lean_ctor_set(v___x_2568_, 1, v___x_2567_);
lean_inc(v___y_2558_);
v___x_2569_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12(v___y_2558_, v___y_2560_, v___y_2555_, v___y_2559_, v___y_2552_, v___y_2557_, v___y_2554_, v___x_2568_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
v___y_2535_ = v___y_2553_;
v___y_2536_ = v___y_2556_;
v___y_2537_ = v___y_2558_;
v___y_2538_ = v___x_2569_;
goto v___jp_2534_;
}
v___jp_2570_:
{
lean_object* v___x_2582_; 
v___x_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2582_, 0, v_a_2581_);
v___y_2551_ = v___y_2571_;
v___y_2552_ = v___y_2572_;
v___y_2553_ = v___y_2574_;
v___y_2554_ = v___y_2573_;
v___y_2555_ = v___y_2575_;
v___y_2556_ = v___y_2578_;
v___y_2557_ = v___y_2577_;
v___y_2558_ = v___y_2576_;
v___y_2559_ = v___y_2579_;
v___y_2560_ = v___y_2580_;
v_a_2561_ = v___x_2582_;
goto v___jp_2550_;
}
v___jp_2583_:
{
if (lean_obj_tag(v___y_2594_) == 0)
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
v_a_2595_ = lean_ctor_get(v___y_2594_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___y_2594_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___y_2594_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___y_2594_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
lean_ctor_set_tag(v___x_2597_, 1);
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
v___y_2551_ = v___y_2584_;
v___y_2552_ = v___y_2585_;
v___y_2553_ = v___y_2587_;
v___y_2554_ = v___y_2586_;
v___y_2555_ = v___y_2588_;
v___y_2556_ = v___y_2591_;
v___y_2557_ = v___y_2590_;
v___y_2558_ = v___y_2589_;
v___y_2559_ = v___y_2592_;
v___y_2560_ = v___y_2593_;
v_a_2561_ = v___x_2600_;
goto v___jp_2550_;
}
}
}
else
{
lean_object* v_a_2603_; 
v_a_2603_ = lean_ctor_get(v___y_2594_, 0);
lean_inc(v_a_2603_);
lean_dec_ref(v___y_2594_);
v___y_2571_ = v___y_2584_;
v___y_2572_ = v___y_2585_;
v___y_2573_ = v___y_2586_;
v___y_2574_ = v___y_2587_;
v___y_2575_ = v___y_2588_;
v___y_2576_ = v___y_2589_;
v___y_2577_ = v___y_2590_;
v___y_2578_ = v___y_2591_;
v___y_2579_ = v___y_2592_;
v___y_2580_ = v___y_2593_;
v_a_2581_ = v_a_2603_;
goto v___jp_2570_;
}
}
v___jp_2604_:
{
lean_object* v___x_2616_; double v___x_2617_; double v___x_2618_; double v___x_2619_; double v___x_2620_; double v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2616_ = lean_io_mono_nanos_now();
v___x_2617_ = lean_float_of_nat(v___y_2612_);
v___x_2618_ = lean_float_once(&l_Lean_Meta_rwMatcher___closed__4, &l_Lean_Meta_rwMatcher___closed__4_once, _init_l_Lean_Meta_rwMatcher___closed__4);
v___x_2619_ = lean_float_div(v___x_2617_, v___x_2618_);
v___x_2620_ = lean_float_of_nat(v___x_2616_);
v___x_2621_ = lean_float_div(v___x_2620_, v___x_2618_);
v___x_2622_ = lean_box_float(v___x_2619_);
v___x_2623_ = lean_box_float(v___x_2621_);
v___x_2624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2622_);
lean_ctor_set(v___x_2624_, 1, v___x_2623_);
v___x_2625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2625_, 0, v_a_2615_);
lean_ctor_set(v___x_2625_, 1, v___x_2624_);
lean_inc(v___y_2611_);
v___x_2626_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12(v___y_2611_, v___y_2614_, v___y_2608_, v___y_2613_, v___y_2605_, v___y_2610_, v___y_2607_, v___x_2625_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
v___y_2535_ = v___y_2606_;
v___y_2536_ = v___y_2609_;
v___y_2537_ = v___y_2611_;
v___y_2538_ = v___x_2626_;
goto v___jp_2534_;
}
v___jp_2627_:
{
lean_object* v___x_2639_; 
v___x_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2639_, 0, v_a_2638_);
v___y_2605_ = v___y_2628_;
v___y_2606_ = v___y_2630_;
v___y_2607_ = v___y_2629_;
v___y_2608_ = v___y_2631_;
v___y_2609_ = v___y_2635_;
v___y_2610_ = v___y_2634_;
v___y_2611_ = v___y_2633_;
v___y_2612_ = v___y_2632_;
v___y_2613_ = v___y_2636_;
v___y_2614_ = v___y_2637_;
v_a_2615_ = v___x_2639_;
goto v___jp_2604_;
}
v___jp_2640_:
{
if (lean_obj_tag(v___y_2651_) == 0)
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
v_a_2652_ = lean_ctor_get(v___y_2651_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___y_2651_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___y_2651_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___y_2651_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
lean_ctor_set_tag(v___x_2654_, 1);
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
v___y_2605_ = v___y_2641_;
v___y_2606_ = v___y_2643_;
v___y_2607_ = v___y_2642_;
v___y_2608_ = v___y_2644_;
v___y_2609_ = v___y_2648_;
v___y_2610_ = v___y_2647_;
v___y_2611_ = v___y_2646_;
v___y_2612_ = v___y_2645_;
v___y_2613_ = v___y_2649_;
v___y_2614_ = v___y_2650_;
v_a_2615_ = v___x_2657_;
goto v___jp_2604_;
}
}
}
else
{
lean_object* v_a_2660_; 
v_a_2660_ = lean_ctor_get(v___y_2651_, 0);
lean_inc(v_a_2660_);
lean_dec_ref(v___y_2651_);
v___y_2628_ = v___y_2641_;
v___y_2629_ = v___y_2642_;
v___y_2630_ = v___y_2643_;
v___y_2631_ = v___y_2644_;
v___y_2632_ = v___y_2645_;
v___y_2633_ = v___y_2646_;
v___y_2634_ = v___y_2647_;
v___y_2635_ = v___y_2648_;
v___y_2636_ = v___y_2649_;
v___y_2637_ = v___y_2650_;
v_a_2638_ = v_a_2660_;
goto v___jp_2627_;
}
}
v___jp_2661_:
{
lean_object* v___x_2675_; lean_object* v_a_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
v___x_2675_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg(v_a_2475_);
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref(v___x_2675_);
v___x_2677_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2678_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11(v___y_2673_, v___x_2677_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2679_ = lean_io_mono_nanos_now();
lean_inc(v_a_2475_);
lean_inc_ref(v_a_2474_);
lean_inc(v_a_2473_);
lean_inc_ref(v_a_2472_);
v___x_2680_ = lean_infer_type(v___y_2668_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; uint8_t v___x_2682_; lean_object* v___x_2683_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref(v___x_2680_);
v___x_2682_ = 0;
v___x_2683_ = l_Lean_Meta_forallMetaTelescope(v_a_2681_, v___x_2682_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v_a_2684_; lean_object* v_snd_2685_; lean_object* v_fst_2686_; lean_object* v_snd_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2705_; 
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
lean_inc(v_a_2684_);
lean_dec_ref(v___x_2683_);
v_snd_2685_ = lean_ctor_get(v_a_2684_, 1);
lean_inc(v_snd_2685_);
v_fst_2686_ = lean_ctor_get(v_a_2684_, 0);
lean_inc(v_fst_2686_);
lean_dec(v_a_2684_);
v_snd_2687_ = lean_ctor_get(v_snd_2685_, 1);
v_isSharedCheck_2705_ = !lean_is_exclusive(v_snd_2685_);
if (v_isSharedCheck_2705_ == 0)
{
lean_object* v_unused_2706_; 
v_unused_2706_ = lean_ctor_get(v_snd_2685_, 0);
lean_dec(v_unused_2706_);
v___x_2689_ = v_snd_2685_;
v_isShared_2690_ = v_isSharedCheck_2705_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_snd_2687_);
lean_dec(v_snd_2685_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2705_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2691_; lean_object* v_a_2692_; uint8_t v___x_2693_; 
lean_inc(v___y_2671_);
v___x_2691_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg(v___y_2671_, v_a_2474_);
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2692_);
lean_dec_ref(v___x_2691_);
v___x_2693_ = lean_unbox(v_a_2692_);
lean_dec(v_a_2692_);
if (v___x_2693_ == 0)
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
lean_del_object(v___x_2689_);
v___x_2694_ = lean_box(0);
v___x_2695_ = l_Lean_Meta_rwMatcher___lam__3(v___y_2667_, v___y_2663_, v_fst_2686_, v___y_2666_, v___x_2678_, v_e_2471_, v_snd_2687_, v___x_2694_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
lean_dec(v_snd_2687_);
v___y_2641_ = v___y_2662_;
v___y_2642_ = v___y_2664_;
v___y_2643_ = v___y_2669_;
v___y_2644_ = v___y_2670_;
v___y_2645_ = v___x_2679_;
v___y_2646_ = v___y_2671_;
v___y_2647_ = v_a_2676_;
v___y_2648_ = v___y_2672_;
v___y_2649_ = v___y_2673_;
v___y_2650_ = v___y_2674_;
v___y_2651_ = v___x_2695_;
goto v___jp_2640_;
}
else
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2699_; 
v___x_2696_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__6, &l_Lean_Meta_rwMatcher___closed__6_once, _init_l_Lean_Meta_rwMatcher___closed__6);
lean_inc(v_snd_2687_);
v___x_2697_ = l_Lean_indentExpr(v_snd_2687_);
if (v_isShared_2690_ == 0)
{
lean_ctor_set_tag(v___x_2689_, 7);
lean_ctor_set(v___x_2689_, 1, v___x_2697_);
lean_ctor_set(v___x_2689_, 0, v___x_2696_);
v___x_2699_ = v___x_2689_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2696_);
lean_ctor_set(v_reuseFailAlloc_2704_, 1, v___x_2697_);
v___x_2699_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
lean_object* v___x_2700_; 
lean_inc(v___y_2671_);
v___x_2700_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(v___y_2671_, v___x_2699_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_object* v_a_2701_; lean_object* v___x_2702_; 
v_a_2701_ = lean_ctor_get(v___x_2700_, 0);
lean_inc(v_a_2701_);
lean_dec_ref(v___x_2700_);
v___x_2702_ = l_Lean_Meta_rwMatcher___lam__3(v___y_2667_, v___y_2663_, v_fst_2686_, v___y_2666_, v___x_2678_, v_e_2471_, v_snd_2687_, v_a_2701_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
lean_dec(v_snd_2687_);
v___y_2641_ = v___y_2662_;
v___y_2642_ = v___y_2664_;
v___y_2643_ = v___y_2669_;
v___y_2644_ = v___y_2670_;
v___y_2645_ = v___x_2679_;
v___y_2646_ = v___y_2671_;
v___y_2647_ = v_a_2676_;
v___y_2648_ = v___y_2672_;
v___y_2649_ = v___y_2673_;
v___y_2650_ = v___y_2674_;
v___y_2651_ = v___x_2702_;
goto v___jp_2640_;
}
else
{
lean_object* v_a_2703_; 
lean_dec(v_snd_2687_);
lean_dec(v_fst_2686_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2663_);
lean_dec_ref(v_e_2471_);
v_a_2703_ = lean_ctor_get(v___x_2700_, 0);
lean_inc(v_a_2703_);
lean_dec_ref(v___x_2700_);
v___y_2628_ = v___y_2662_;
v___y_2629_ = v___y_2664_;
v___y_2630_ = v___y_2669_;
v___y_2631_ = v___y_2670_;
v___y_2632_ = v___x_2679_;
v___y_2633_ = v___y_2671_;
v___y_2634_ = v_a_2676_;
v___y_2635_ = v___y_2672_;
v___y_2636_ = v___y_2673_;
v___y_2637_ = v___y_2674_;
v_a_2638_ = v_a_2703_;
goto v___jp_2627_;
}
}
}
}
}
else
{
lean_object* v_a_2707_; 
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2663_);
lean_dec_ref(v_e_2471_);
v_a_2707_ = lean_ctor_get(v___x_2683_, 0);
lean_inc(v_a_2707_);
lean_dec_ref(v___x_2683_);
v___y_2628_ = v___y_2662_;
v___y_2629_ = v___y_2664_;
v___y_2630_ = v___y_2669_;
v___y_2631_ = v___y_2670_;
v___y_2632_ = v___x_2679_;
v___y_2633_ = v___y_2671_;
v___y_2634_ = v_a_2676_;
v___y_2635_ = v___y_2672_;
v___y_2636_ = v___y_2673_;
v___y_2637_ = v___y_2674_;
v_a_2638_ = v_a_2707_;
goto v___jp_2627_;
}
}
else
{
lean_object* v_a_2708_; 
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2663_);
lean_dec_ref(v_e_2471_);
v_a_2708_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2708_);
lean_dec_ref(v___x_2680_);
v___y_2628_ = v___y_2662_;
v___y_2629_ = v___y_2664_;
v___y_2630_ = v___y_2669_;
v___y_2631_ = v___y_2670_;
v___y_2632_ = v___x_2679_;
v___y_2633_ = v___y_2671_;
v___y_2634_ = v_a_2676_;
v___y_2635_ = v___y_2672_;
v___y_2636_ = v___y_2673_;
v___y_2637_ = v___y_2674_;
v_a_2638_ = v_a_2708_;
goto v___jp_2627_;
}
}
else
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2709_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2475_);
lean_inc_ref(v_a_2474_);
lean_inc(v_a_2473_);
lean_inc_ref(v_a_2472_);
v___x_2710_ = lean_infer_type(v___y_2668_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; uint8_t v___x_2712_; lean_object* v___x_2713_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2711_);
lean_dec_ref(v___x_2710_);
v___x_2712_ = 0;
v___x_2713_ = l_Lean_Meta_forallMetaTelescope(v_a_2711_, v___x_2712_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v_a_2714_; lean_object* v_snd_2715_; lean_object* v_fst_2716_; lean_object* v_snd_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2735_; 
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_a_2714_);
lean_dec_ref(v___x_2713_);
v_snd_2715_ = lean_ctor_get(v_a_2714_, 1);
lean_inc(v_snd_2715_);
v_fst_2716_ = lean_ctor_get(v_a_2714_, 0);
lean_inc(v_fst_2716_);
lean_dec(v_a_2714_);
v_snd_2717_ = lean_ctor_get(v_snd_2715_, 1);
v_isSharedCheck_2735_ = !lean_is_exclusive(v_snd_2715_);
if (v_isSharedCheck_2735_ == 0)
{
lean_object* v_unused_2736_; 
v_unused_2736_ = lean_ctor_get(v_snd_2715_, 0);
lean_dec(v_unused_2736_);
v___x_2719_ = v_snd_2715_;
v_isShared_2720_ = v_isSharedCheck_2735_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_snd_2717_);
lean_dec(v_snd_2715_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2735_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2721_; lean_object* v_a_2722_; uint8_t v___x_2723_; 
lean_inc(v___y_2671_);
v___x_2721_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg(v___y_2671_, v_a_2474_);
v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
lean_inc(v_a_2722_);
lean_dec_ref(v___x_2721_);
v___x_2723_ = lean_unbox(v_a_2722_);
lean_dec(v_a_2722_);
if (v___x_2723_ == 0)
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
lean_del_object(v___x_2719_);
v___x_2724_ = lean_box(0);
v___x_2725_ = l_Lean_Meta_rwMatcher___lam__4(v___y_2667_, v___y_2663_, v_fst_2716_, v___y_2666_, v___x_2678_, v_e_2471_, v___y_2665_, v_snd_2717_, v___x_2724_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
lean_dec(v_snd_2717_);
v___y_2584_ = v___x_2709_;
v___y_2585_ = v___y_2662_;
v___y_2586_ = v___y_2664_;
v___y_2587_ = v___y_2669_;
v___y_2588_ = v___y_2670_;
v___y_2589_ = v___y_2671_;
v___y_2590_ = v_a_2676_;
v___y_2591_ = v___y_2672_;
v___y_2592_ = v___y_2673_;
v___y_2593_ = v___y_2674_;
v___y_2594_ = v___x_2725_;
goto v___jp_2583_;
}
else
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2729_; 
v___x_2726_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__6, &l_Lean_Meta_rwMatcher___closed__6_once, _init_l_Lean_Meta_rwMatcher___closed__6);
lean_inc(v_snd_2717_);
v___x_2727_ = l_Lean_indentExpr(v_snd_2717_);
if (v_isShared_2720_ == 0)
{
lean_ctor_set_tag(v___x_2719_, 7);
lean_ctor_set(v___x_2719_, 1, v___x_2727_);
lean_ctor_set(v___x_2719_, 0, v___x_2726_);
v___x_2729_ = v___x_2719_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2726_);
lean_ctor_set(v_reuseFailAlloc_2734_, 1, v___x_2727_);
v___x_2729_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
lean_object* v___x_2730_; 
lean_inc(v___y_2671_);
v___x_2730_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(v___y_2671_, v___x_2729_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; lean_object* v___x_2732_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref(v___x_2730_);
v___x_2732_ = l_Lean_Meta_rwMatcher___lam__4(v___y_2667_, v___y_2663_, v_fst_2716_, v___y_2666_, v___x_2678_, v_e_2471_, v___y_2665_, v_snd_2717_, v_a_2731_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
lean_dec(v_snd_2717_);
v___y_2584_ = v___x_2709_;
v___y_2585_ = v___y_2662_;
v___y_2586_ = v___y_2664_;
v___y_2587_ = v___y_2669_;
v___y_2588_ = v___y_2670_;
v___y_2589_ = v___y_2671_;
v___y_2590_ = v_a_2676_;
v___y_2591_ = v___y_2672_;
v___y_2592_ = v___y_2673_;
v___y_2593_ = v___y_2674_;
v___y_2594_ = v___x_2732_;
goto v___jp_2583_;
}
else
{
lean_object* v_a_2733_; 
lean_dec(v_snd_2717_);
lean_dec(v_fst_2716_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2663_);
lean_dec_ref(v_e_2471_);
v_a_2733_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2733_);
lean_dec_ref(v___x_2730_);
v___y_2571_ = v___x_2709_;
v___y_2572_ = v___y_2662_;
v___y_2573_ = v___y_2664_;
v___y_2574_ = v___y_2669_;
v___y_2575_ = v___y_2670_;
v___y_2576_ = v___y_2671_;
v___y_2577_ = v_a_2676_;
v___y_2578_ = v___y_2672_;
v___y_2579_ = v___y_2673_;
v___y_2580_ = v___y_2674_;
v_a_2581_ = v_a_2733_;
goto v___jp_2570_;
}
}
}
}
}
else
{
lean_object* v_a_2737_; 
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2663_);
lean_dec_ref(v_e_2471_);
v_a_2737_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_a_2737_);
lean_dec_ref(v___x_2713_);
v___y_2571_ = v___x_2709_;
v___y_2572_ = v___y_2662_;
v___y_2573_ = v___y_2664_;
v___y_2574_ = v___y_2669_;
v___y_2575_ = v___y_2670_;
v___y_2576_ = v___y_2671_;
v___y_2577_ = v_a_2676_;
v___y_2578_ = v___y_2672_;
v___y_2579_ = v___y_2673_;
v___y_2580_ = v___y_2674_;
v_a_2581_ = v_a_2737_;
goto v___jp_2570_;
}
}
else
{
lean_object* v_a_2738_; 
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2663_);
lean_dec_ref(v_e_2471_);
v_a_2738_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2738_);
lean_dec_ref(v___x_2710_);
v___y_2571_ = v___x_2709_;
v___y_2572_ = v___y_2662_;
v___y_2573_ = v___y_2664_;
v___y_2574_ = v___y_2669_;
v___y_2575_ = v___y_2670_;
v___y_2576_ = v___y_2671_;
v___y_2577_ = v_a_2676_;
v___y_2578_ = v___y_2672_;
v___y_2579_ = v___y_2673_;
v___y_2580_ = v___y_2674_;
v_a_2581_ = v_a_2738_;
goto v___jp_2570_;
}
}
}
v___jp_2739_:
{
uint8_t v___x_2741_; 
v___x_2741_ = 1;
if (v___y_2740_ == 0)
{
lean_object* v___x_2742_; lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2898_; 
v___x_2742_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(v_e_2471_, v_a_2475_);
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2745_ = v___x_2742_;
v_isShared_2746_ = v_isSharedCheck_2898_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2742_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2898_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
uint8_t v___x_2747_; 
v___x_2747_ = lean_unbox(v_a_2743_);
lean_dec(v_a_2743_);
if (v___x_2747_ == 0)
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v_a_2750_; uint8_t v___x_2751_; 
lean_del_object(v___x_2745_);
lean_dec(v_altIdx_2470_);
v___x_2748_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__10));
v___x_2749_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg(v___x_2748_, v_a_2474_);
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref(v___x_2749_);
v___x_2751_ = lean_unbox(v_a_2750_);
lean_dec(v_a_2750_);
if (v___x_2751_ == 0)
{
v___y_2541_ = v___x_2741_;
goto v___jp_2540_;
}
else
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2752_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__12, &l_Lean_Meta_rwMatcher___closed__12_once, _init_l_Lean_Meta_rwMatcher___closed__12);
lean_inc_ref(v_e_2471_);
v___x_2753_ = l_Lean_indentExpr(v_e_2471_);
v___x_2754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2752_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
v___x_2755_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(v___x_2748_, v___x_2754_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_dec_ref(v___x_2755_);
v___y_2541_ = v___x_2741_;
goto v___jp_2540_;
}
else
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
lean_dec_ref(v_e_2471_);
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2755_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2755_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
}
else
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2764_ = l_Lean_Expr_getAppFn(v_e_2471_);
v___x_2765_ = l_Lean_Expr_constName_x21(v___x_2764_);
lean_inc(v_a_2475_);
lean_inc_ref(v_a_2474_);
lean_inc(v_a_2473_);
lean_inc_ref(v_a_2472_);
lean_inc(v___x_2765_);
v___x_2766_ = lean_get_congr_match_equations_for(v___x_2765_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; lean_object* v___x_2768_; uint8_t v___x_2769_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_a_2767_);
lean_dec_ref(v___x_2766_);
v___x_2768_ = lean_array_get_size(v_a_2767_);
v___x_2769_ = lean_nat_dec_lt(v_altIdx_2470_, v___x_2768_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2805_; 
lean_dec(v_a_2767_);
lean_dec_ref(v___x_2764_);
v___x_2770_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__10));
v___x_2771_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg(v___x_2770_, v_a_2474_);
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2774_ = v___x_2771_;
v_isShared_2775_ = v_isSharedCheck_2805_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2771_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2805_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
uint8_t v___x_2776_; 
v___x_2776_ = lean_unbox(v_a_2772_);
lean_dec(v_a_2772_);
if (v___x_2776_ == 0)
{
lean_del_object(v___x_2774_);
lean_dec(v___x_2765_);
lean_del_object(v___x_2745_);
lean_dec(v_altIdx_2470_);
v___y_2546_ = v___x_2741_;
goto v___jp_2545_;
}
else
{
lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2780_; 
v___x_2777_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__14, &l_Lean_Meta_rwMatcher___closed__14_once, _init_l_Lean_Meta_rwMatcher___closed__14);
v___x_2778_ = l_Nat_reprFast(v_altIdx_2470_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set_tag(v___x_2774_, 3);
lean_ctor_set(v___x_2774_, 0, v___x_2778_);
v___x_2780_ = v___x_2774_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2778_);
v___x_2780_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2787_; 
v___x_2781_ = l_Lean_MessageData_ofFormat(v___x_2780_);
v___x_2782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2777_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
v___x_2783_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__16, &l_Lean_Meta_rwMatcher___closed__16_once, _init_l_Lean_Meta_rwMatcher___closed__16);
v___x_2784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2782_);
lean_ctor_set(v___x_2784_, 1, v___x_2783_);
v___x_2785_ = l_Nat_reprFast(v___x_2768_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set_tag(v___x_2745_, 3);
lean_ctor_set(v___x_2745_, 0, v___x_2785_);
v___x_2787_ = v___x_2745_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v___x_2785_);
v___x_2787_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2788_ = l_Lean_MessageData_ofFormat(v___x_2787_);
v___x_2789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2784_);
lean_ctor_set(v___x_2789_, 1, v___x_2788_);
v___x_2790_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__18, &l_Lean_Meta_rwMatcher___closed__18_once, _init_l_Lean_Meta_rwMatcher___closed__18);
v___x_2791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2789_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
v___x_2792_ = l_Lean_MessageData_ofConstName(v___x_2765_, v___y_2740_);
v___x_2793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2791_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
v___x_2794_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(v___x_2770_, v___x_2793_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_dec_ref(v___x_2794_);
v___y_2546_ = v___x_2741_;
goto v___jp_2545_;
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
lean_dec_ref(v_e_2471_);
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2794_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2794_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
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
lean_object* v_options_2806_; uint8_t v_hasTrace_2807_; lean_object* v_nargs_2808_; lean_object* v___x_2809_; lean_object* v___f_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v_dummy_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
lean_dec(v___x_2765_);
lean_del_object(v___x_2745_);
v_options_2806_ = lean_ctor_get(v_a_2474_, 2);
v_hasTrace_2807_ = lean_ctor_get_uint8(v_options_2806_, sizeof(void*)*1);
v_nargs_2808_ = l_Lean_Expr_getAppNumArgs(v_e_2471_);
v___x_2809_ = lean_box(v___x_2741_);
lean_inc_ref(v_e_2471_);
v___f_2810_ = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2810_, 0, v_e_2471_);
lean_closure_set(v___f_2810_, 1, v___x_2809_);
v___x_2811_ = lean_box(0);
v___x_2812_ = lean_array_get(v___x_2811_, v_a_2767_, v_altIdx_2470_);
lean_dec(v_altIdx_2470_);
lean_dec(v_a_2767_);
v___x_2813_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__10));
v___x_2814_ = l_Lean_Expr_constLevels_x21(v___x_2764_);
lean_dec_ref(v___x_2764_);
lean_inc(v___x_2812_);
v___x_2815_ = l_Lean_mkConst(v___x_2812_, v___x_2814_);
v_dummy_2816_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__19, &l_Lean_Meta_rwMatcher___closed__19_once, _init_l_Lean_Meta_rwMatcher___closed__19);
lean_inc(v_nargs_2808_);
v___x_2817_ = lean_mk_array(v_nargs_2808_, v_dummy_2816_);
v___x_2818_ = lean_unsigned_to_nat(1u);
v___x_2819_ = lean_nat_sub(v_nargs_2808_, v___x_2818_);
lean_dec(v_nargs_2808_);
lean_inc_ref(v_e_2471_);
v___x_2820_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2471_, v___x_2817_, v___x_2819_);
v___x_2821_ = l_Lean_mkAppN(v___x_2815_, v___x_2820_);
lean_dec_ref(v___x_2820_);
if (v_hasTrace_2807_ == 0)
{
lean_object* v___x_2822_; 
lean_inc(v_a_2475_);
lean_inc_ref(v_a_2474_);
lean_inc(v_a_2473_);
lean_inc_ref(v_a_2472_);
lean_inc_ref(v___x_2821_);
v___x_2822_ = lean_infer_type(v___x_2821_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; uint8_t v___x_2824_; lean_object* v___x_2825_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2823_);
lean_dec_ref(v___x_2822_);
v___x_2824_ = 0;
v___x_2825_ = l_Lean_Meta_forallMetaTelescope(v_a_2823_, v___x_2824_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v_snd_2827_; lean_object* v_fst_2828_; lean_object* v_snd_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2847_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2826_);
lean_dec_ref(v___x_2825_);
v_snd_2827_ = lean_ctor_get(v_a_2826_, 1);
lean_inc(v_snd_2827_);
v_fst_2828_ = lean_ctor_get(v_a_2826_, 0);
lean_inc(v_fst_2828_);
lean_dec(v_a_2826_);
v_snd_2829_ = lean_ctor_get(v_snd_2827_, 1);
v_isSharedCheck_2847_ = !lean_is_exclusive(v_snd_2827_);
if (v_isSharedCheck_2847_ == 0)
{
lean_object* v_unused_2848_; 
v_unused_2848_ = lean_ctor_get(v_snd_2827_, 0);
lean_dec(v_unused_2848_);
v___x_2831_ = v_snd_2827_;
v_isShared_2832_ = v_isSharedCheck_2847_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_snd_2829_);
lean_dec(v_snd_2827_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2847_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2833_; lean_object* v_a_2834_; uint8_t v___x_2835_; 
v___x_2833_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg(v___x_2813_, v_a_2474_);
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_a_2834_);
lean_dec_ref(v___x_2833_);
v___x_2835_ = lean_unbox(v_a_2834_);
lean_dec(v_a_2834_);
if (v___x_2835_ == 0)
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
lean_del_object(v___x_2831_);
v___x_2836_ = lean_box(0);
lean_inc(v___x_2812_);
v___x_2837_ = l_Lean_Meta_rwMatcher___lam__1(v___x_2741_, v___x_2821_, v_fst_2828_, v___x_2812_, v_hasTrace_2807_, v_e_2471_, v_snd_2829_, v___x_2836_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
lean_dec(v_snd_2829_);
v___y_2535_ = v___f_2810_;
v___y_2536_ = v___x_2812_;
v___y_2537_ = v___x_2813_;
v___y_2538_ = v___x_2837_;
goto v___jp_2534_;
}
else
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2841_; 
v___x_2838_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__6, &l_Lean_Meta_rwMatcher___closed__6_once, _init_l_Lean_Meta_rwMatcher___closed__6);
lean_inc(v_snd_2829_);
v___x_2839_ = l_Lean_indentExpr(v_snd_2829_);
if (v_isShared_2832_ == 0)
{
lean_ctor_set_tag(v___x_2831_, 7);
lean_ctor_set(v___x_2831_, 1, v___x_2839_);
lean_ctor_set(v___x_2831_, 0, v___x_2838_);
v___x_2841_ = v___x_2831_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2838_);
lean_ctor_set(v_reuseFailAlloc_2846_, 1, v___x_2839_);
v___x_2841_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2842_; 
v___x_2842_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(v___x_2813_, v___x_2841_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v_a_2843_; lean_object* v___x_2844_; 
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
lean_inc(v_a_2843_);
lean_dec_ref(v___x_2842_);
lean_inc(v___x_2812_);
v___x_2844_ = l_Lean_Meta_rwMatcher___lam__1(v___x_2741_, v___x_2821_, v_fst_2828_, v___x_2812_, v_hasTrace_2807_, v_e_2471_, v_snd_2829_, v_a_2843_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
lean_dec(v_snd_2829_);
v___y_2535_ = v___f_2810_;
v___y_2536_ = v___x_2812_;
v___y_2537_ = v___x_2813_;
v___y_2538_ = v___x_2844_;
goto v___jp_2534_;
}
else
{
lean_object* v_a_2845_; 
lean_dec(v_snd_2829_);
lean_dec(v_fst_2828_);
lean_dec_ref(v___x_2821_);
lean_dec_ref(v_e_2471_);
v_a_2845_ = lean_ctor_get(v___x_2842_, 0);
lean_inc(v_a_2845_);
lean_dec_ref(v___x_2842_);
v___y_2528_ = v___f_2810_;
v___y_2529_ = v___x_2813_;
v___y_2530_ = v___x_2812_;
v_a_2531_ = v_a_2845_;
goto v___jp_2527_;
}
}
}
}
}
else
{
lean_object* v_a_2849_; 
lean_dec_ref(v___x_2821_);
lean_dec_ref(v_e_2471_);
v_a_2849_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2849_);
lean_dec_ref(v___x_2825_);
v___y_2528_ = v___f_2810_;
v___y_2529_ = v___x_2813_;
v___y_2530_ = v___x_2812_;
v_a_2531_ = v_a_2849_;
goto v___jp_2527_;
}
}
else
{
lean_object* v_a_2850_; 
lean_dec_ref(v___x_2821_);
lean_dec_ref(v_e_2471_);
v_a_2850_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2850_);
lean_dec_ref(v___x_2822_);
v___y_2528_ = v___f_2810_;
v___y_2529_ = v___x_2813_;
v___y_2530_ = v___x_2812_;
v_a_2531_ = v_a_2850_;
goto v___jp_2527_;
}
}
else
{
lean_object* v___x_2851_; lean_object* v_a_2852_; lean_object* v___x_2853_; lean_object* v___f_2854_; lean_object* v___x_2855_; uint8_t v___x_2856_; 
v___x_2851_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg(v___x_2813_, v_a_2474_);
v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
lean_inc(v_a_2852_);
lean_dec_ref(v___x_2851_);
v___x_2853_ = lean_box(v___y_2740_);
lean_inc_ref(v_e_2471_);
lean_inc(v___x_2812_);
v___f_2854_ = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__2___boxed), 9, 3);
lean_closure_set(v___f_2854_, 0, v___x_2812_);
lean_closure_set(v___f_2854_, 1, v___x_2853_);
lean_closure_set(v___f_2854_, 2, v_e_2471_);
v___x_2855_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__1));
v___x_2856_ = lean_unbox(v_a_2852_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; uint8_t v___x_2858_; 
v___x_2857_ = l_Lean_trace_profiler;
v___x_2858_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11(v_options_2806_, v___x_2857_);
if (v___x_2858_ == 0)
{
lean_object* v___x_2859_; 
lean_dec_ref(v___f_2854_);
lean_dec(v_a_2852_);
lean_inc(v_a_2475_);
lean_inc_ref(v_a_2474_);
lean_inc(v_a_2473_);
lean_inc_ref(v_a_2472_);
lean_inc_ref(v___x_2821_);
v___x_2859_ = lean_infer_type(v___x_2821_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; uint8_t v___x_2861_; lean_object* v___x_2862_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_a_2860_);
lean_dec_ref(v___x_2859_);
v___x_2861_ = 0;
v___x_2862_ = l_Lean_Meta_forallMetaTelescope(v_a_2860_, v___x_2861_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; lean_object* v_snd_2864_; lean_object* v_fst_2865_; lean_object* v_snd_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2884_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2863_);
lean_dec_ref(v___x_2862_);
v_snd_2864_ = lean_ctor_get(v_a_2863_, 1);
lean_inc(v_snd_2864_);
v_fst_2865_ = lean_ctor_get(v_a_2863_, 0);
lean_inc(v_fst_2865_);
lean_dec(v_a_2863_);
v_snd_2866_ = lean_ctor_get(v_snd_2864_, 1);
v_isSharedCheck_2884_ = !lean_is_exclusive(v_snd_2864_);
if (v_isSharedCheck_2884_ == 0)
{
lean_object* v_unused_2885_; 
v_unused_2885_ = lean_ctor_get(v_snd_2864_, 0);
lean_dec(v_unused_2885_);
v___x_2868_ = v_snd_2864_;
v_isShared_2869_ = v_isSharedCheck_2884_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_snd_2866_);
lean_dec(v_snd_2864_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2884_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2870_; lean_object* v_a_2871_; uint8_t v___x_2872_; 
v___x_2870_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_rwMatcher_spec__2___redArg(v___x_2813_, v_a_2474_);
v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
lean_inc(v_a_2871_);
lean_dec_ref(v___x_2870_);
v___x_2872_ = lean_unbox(v_a_2871_);
lean_dec(v_a_2871_);
if (v___x_2872_ == 0)
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
lean_del_object(v___x_2868_);
v___x_2873_ = lean_box(0);
lean_inc(v___x_2812_);
v___x_2874_ = l_Lean_Meta_rwMatcher___lam__5(v___x_2741_, v___x_2821_, v_fst_2865_, v___x_2812_, v___x_2858_, v_e_2471_, v_snd_2866_, v___x_2873_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
lean_dec(v_snd_2866_);
v___y_2535_ = v___f_2810_;
v___y_2536_ = v___x_2812_;
v___y_2537_ = v___x_2813_;
v___y_2538_ = v___x_2874_;
goto v___jp_2534_;
}
else
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2878_; 
v___x_2875_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__6, &l_Lean_Meta_rwMatcher___closed__6_once, _init_l_Lean_Meta_rwMatcher___closed__6);
lean_inc(v_snd_2866_);
v___x_2876_ = l_Lean_indentExpr(v_snd_2866_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set_tag(v___x_2868_, 7);
lean_ctor_set(v___x_2868_, 1, v___x_2876_);
lean_ctor_set(v___x_2868_, 0, v___x_2875_);
v___x_2878_ = v___x_2868_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2875_);
lean_ctor_set(v_reuseFailAlloc_2883_, 1, v___x_2876_);
v___x_2878_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
lean_object* v___x_2879_; 
v___x_2879_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(v___x_2813_, v___x_2878_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v___x_2881_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_a_2880_);
lean_dec_ref(v___x_2879_);
lean_inc(v___x_2812_);
v___x_2881_ = l_Lean_Meta_rwMatcher___lam__5(v___x_2741_, v___x_2821_, v_fst_2865_, v___x_2812_, v___x_2858_, v_e_2471_, v_snd_2866_, v_a_2880_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
lean_dec(v_snd_2866_);
v___y_2535_ = v___f_2810_;
v___y_2536_ = v___x_2812_;
v___y_2537_ = v___x_2813_;
v___y_2538_ = v___x_2881_;
goto v___jp_2534_;
}
else
{
lean_object* v_a_2882_; 
lean_dec(v_snd_2866_);
lean_dec(v_fst_2865_);
lean_dec_ref(v___x_2821_);
lean_dec_ref(v_e_2471_);
v_a_2882_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_a_2882_);
lean_dec_ref(v___x_2879_);
v___y_2528_ = v___f_2810_;
v___y_2529_ = v___x_2813_;
v___y_2530_ = v___x_2812_;
v_a_2531_ = v_a_2882_;
goto v___jp_2527_;
}
}
}
}
}
else
{
lean_object* v_a_2886_; 
lean_dec_ref(v___x_2821_);
lean_dec_ref(v_e_2471_);
v_a_2886_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2886_);
lean_dec_ref(v___x_2862_);
v___y_2528_ = v___f_2810_;
v___y_2529_ = v___x_2813_;
v___y_2530_ = v___x_2812_;
v_a_2531_ = v_a_2886_;
goto v___jp_2527_;
}
}
else
{
lean_object* v_a_2887_; 
lean_dec_ref(v___x_2821_);
lean_dec_ref(v_e_2471_);
v_a_2887_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_a_2887_);
lean_dec_ref(v___x_2859_);
v___y_2528_ = v___f_2810_;
v___y_2529_ = v___x_2813_;
v___y_2530_ = v___x_2812_;
v_a_2531_ = v_a_2887_;
goto v___jp_2527_;
}
}
else
{
uint8_t v___x_2888_; 
v___x_2888_ = lean_unbox(v_a_2852_);
lean_dec(v_a_2852_);
lean_inc(v___x_2812_);
lean_inc_ref(v___x_2821_);
v___y_2662_ = v___x_2888_;
v___y_2663_ = v___x_2821_;
v___y_2664_ = v___f_2854_;
v___y_2665_ = v___y_2740_;
v___y_2666_ = v___x_2812_;
v___y_2667_ = v___x_2741_;
v___y_2668_ = v___x_2821_;
v___y_2669_ = v___f_2810_;
v___y_2670_ = v___x_2855_;
v___y_2671_ = v___x_2813_;
v___y_2672_ = v___x_2812_;
v___y_2673_ = v_options_2806_;
v___y_2674_ = v___x_2741_;
goto v___jp_2661_;
}
}
else
{
uint8_t v___x_2889_; 
v___x_2889_ = lean_unbox(v_a_2852_);
lean_dec(v_a_2852_);
lean_inc(v___x_2812_);
lean_inc_ref(v___x_2821_);
v___y_2662_ = v___x_2889_;
v___y_2663_ = v___x_2821_;
v___y_2664_ = v___f_2854_;
v___y_2665_ = v___y_2740_;
v___y_2666_ = v___x_2812_;
v___y_2667_ = v___x_2741_;
v___y_2668_ = v___x_2821_;
v___y_2669_ = v___f_2810_;
v___y_2670_ = v___x_2855_;
v___y_2671_ = v___x_2813_;
v___y_2672_ = v___x_2812_;
v___y_2673_ = v_options_2806_;
v___y_2674_ = v___x_2741_;
goto v___jp_2661_;
}
}
}
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_dec(v___x_2765_);
lean_dec_ref(v___x_2764_);
lean_del_object(v___x_2745_);
lean_dec_ref(v_e_2471_);
lean_dec(v_altIdx_2470_);
v_a_2890_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2766_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2766_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
}
}
else
{
lean_object* v___x_2899_; 
lean_dec(v_altIdx_2470_);
v___x_2899_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_rwMatcher_spec__15(v_e_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2909_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2902_ = v___x_2899_;
v_isShared_2903_ = v_isSharedCheck_2909_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2899_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2909_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2907_; 
v___x_2904_ = lean_box(0);
v___x_2905_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2905_, 0, v_a_2900_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
lean_ctor_set_uint8(v___x_2905_, sizeof(void*)*2, v___x_2741_);
if (v_isShared_2903_ == 0)
{
lean_ctor_set(v___x_2902_, 0, v___x_2905_);
v___x_2907_ = v___x_2902_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2905_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
v_a_2910_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2899_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2899_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___boxed(lean_object* v_altIdx_2922_, lean_object* v_e_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l_Lean_Meta_rwMatcher(v_altIdx_2922_, v_e_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_);
lean_dec(v_a_2927_);
lean_dec_ref(v_a_2926_);
lean_dec(v_a_2925_);
lean_dec_ref(v_a_2924_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(lean_object* v_mvarId_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v___x_2936_; 
v___x_2936_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_mvarId_2930_, v___y_2932_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___boxed(lean_object* v_mvarId_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(v_mvarId_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v_mvarId_2937_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6(lean_object* v_00_u03b1_2944_, lean_object* v_msg_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
lean_object* v___x_2951_; 
v___x_2951_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v_msg_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___boxed(lean_object* v_00_u03b1_2952_, lean_object* v_msg_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6(v_00_u03b1_2952_, v_msg_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16(lean_object* v_00_u03b1_2960_, lean_object* v_x_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16___redArg(v_x_2961_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2968_, lean_object* v_x_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16(v_00_u03b1_2968_, v_x_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
return v_res_2975_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(lean_object* v_00_u03b2_2976_, lean_object* v_x_2977_, lean_object* v_x_2978_){
_start:
{
uint8_t v___x_2979_; 
v___x_2979_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_x_2977_, v_x_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2980_, lean_object* v_x_2981_, lean_object* v_x_2982_){
_start:
{
uint8_t v_res_2983_; lean_object* v_r_2984_; 
v_res_2983_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(v_00_u03b2_2980_, v_x_2981_, v_x_2982_);
lean_dec(v_x_2982_);
v_r_2984_ = lean_box(v_res_2983_);
return v_r_2984_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_2985_, lean_object* v_x_2986_, size_t v_x_2987_, lean_object* v_x_2988_){
_start:
{
uint8_t v___x_2989_; 
v___x_2989_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___redArg(v_x_2986_, v_x_2987_, v_x_2988_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6___boxed(lean_object* v_00_u03b2_2990_, lean_object* v_x_2991_, lean_object* v_x_2992_, lean_object* v_x_2993_){
_start:
{
size_t v_x_103340__boxed_2994_; uint8_t v_res_2995_; lean_object* v_r_2996_; 
v_x_103340__boxed_2994_ = lean_unbox_usize(v_x_2992_);
lean_dec(v_x_2992_);
v_res_2995_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6(v_00_u03b2_2990_, v_x_2991_, v_x_103340__boxed_2994_, v_x_2993_);
lean_dec(v_x_2993_);
v_r_2996_ = lean_box(v_res_2995_);
return v_r_2996_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6_spec__21(lean_object* v_00_u03b2_2997_, lean_object* v_keys_2998_, lean_object* v_vals_2999_, lean_object* v_heq_3000_, lean_object* v_i_3001_, lean_object* v_k_3002_){
_start:
{
uint8_t v___x_3003_; 
v___x_3003_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6_spec__21___redArg(v_keys_2998_, v_i_3001_, v_k_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6_spec__21___boxed(lean_object* v_00_u03b2_3004_, lean_object* v_keys_3005_, lean_object* v_vals_3006_, lean_object* v_heq_3007_, lean_object* v_i_3008_, lean_object* v_k_3009_){
_start:
{
uint8_t v_res_3010_; lean_object* v_r_3011_; 
v_res_3010_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__6_spec__21(v_00_u03b2_3004_, v_keys_3005_, v_vals_3006_, v_heq_3007_, v_i_3008_, v_k_3009_);
lean_dec(v_k_3009_);
lean_dec_ref(v_vals_3006_);
lean_dec_ref(v_keys_3005_);
v_r_3011_ = lean_box(v_res_3010_);
return v_r_3011_;
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
