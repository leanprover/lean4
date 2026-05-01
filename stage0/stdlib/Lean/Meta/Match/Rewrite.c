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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Meta_isMatcherAppCore(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
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
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_io_mono_nanos_now();
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Failed to resolve `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Failed to discharge `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_rwMatcher_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_rwMatcher_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14_spec__16(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13___boxed(lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(lean_object* v_e_402_, lean_object* v___y_403_){
_start:
{
uint8_t v___x_405_; 
v___x_405_ = l_Lean_Expr_hasMVar(v_e_402_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; 
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v_e_402_);
return v___x_406_;
}
else
{
lean_object* v___x_407_; lean_object* v_mctx_408_; lean_object* v___x_409_; lean_object* v_fst_410_; lean_object* v_snd_411_; lean_object* v___x_412_; lean_object* v_cache_413_; lean_object* v_zetaDeltaFVarIds_414_; lean_object* v_postponed_415_; lean_object* v_diag_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_425_; 
v___x_407_ = lean_st_ref_get(v___y_403_);
v_mctx_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc_ref(v_mctx_408_);
lean_dec(v___x_407_);
v___x_409_ = l_Lean_instantiateMVarsCore(v_mctx_408_, v_e_402_);
v_fst_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_fst_410_);
v_snd_411_ = lean_ctor_get(v___x_409_, 1);
lean_inc(v_snd_411_);
lean_dec_ref(v___x_409_);
v___x_412_ = lean_st_ref_take(v___y_403_);
v_cache_413_ = lean_ctor_get(v___x_412_, 1);
v_zetaDeltaFVarIds_414_ = lean_ctor_get(v___x_412_, 2);
v_postponed_415_ = lean_ctor_get(v___x_412_, 3);
v_diag_416_ = lean_ctor_get(v___x_412_, 4);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; 
v_unused_426_ = lean_ctor_get(v___x_412_, 0);
lean_dec(v_unused_426_);
v___x_418_ = v___x_412_;
v_isShared_419_ = v_isSharedCheck_425_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_diag_416_);
lean_inc(v_postponed_415_);
lean_inc(v_zetaDeltaFVarIds_414_);
lean_inc(v_cache_413_);
lean_dec(v___x_412_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_425_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v_snd_411_);
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_snd_411_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_cache_413_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_zetaDeltaFVarIds_414_);
lean_ctor_set(v_reuseFailAlloc_424_, 3, v_postponed_415_);
lean_ctor_set(v_reuseFailAlloc_424_, 4, v_diag_416_);
v___x_421_ = v_reuseFailAlloc_424_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_st_ref_set(v___y_403_, v___x_421_);
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v_fst_410_);
return v___x_423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg___boxed(lean_object* v_e_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v_e_427_, v___y_428_);
lean_dec(v___y_428_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4(lean_object* v_e_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v_e_431_, v___y_433_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___boxed(lean_object* v_e_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4(v_e_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
return v_res_444_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_445_ = lean_unsigned_to_nat(32u);
v___x_446_ = lean_mk_empty_array_with_capacity(v___x_445_);
v___x_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
return v___x_447_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__1(void){
_start:
{
size_t v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_448_ = ((size_t)5ULL);
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = lean_unsigned_to_nat(32u);
v___x_451_ = lean_mk_empty_array_with_capacity(v___x_450_);
v___x_452_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__0);
v___x_453_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v___x_451_);
lean_ctor_set(v___x_453_, 2, v___x_449_);
lean_ctor_set(v___x_453_, 3, v___x_449_);
lean_ctor_set_usize(v___x_453_, 4, v___x_448_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg(lean_object* v___y_454_){
_start:
{
lean_object* v___x_456_; lean_object* v_traceState_457_; lean_object* v_traces_458_; lean_object* v___x_459_; lean_object* v_traceState_460_; lean_object* v_env_461_; lean_object* v_nextMacroScope_462_; lean_object* v_ngen_463_; lean_object* v_auxDeclNGen_464_; lean_object* v_cache_465_; lean_object* v_messages_466_; lean_object* v_infoState_467_; lean_object* v_snapshotTasks_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_487_; 
v___x_456_ = lean_st_ref_get(v___y_454_);
v_traceState_457_ = lean_ctor_get(v___x_456_, 4);
lean_inc_ref(v_traceState_457_);
lean_dec(v___x_456_);
v_traces_458_ = lean_ctor_get(v_traceState_457_, 0);
lean_inc_ref(v_traces_458_);
lean_dec_ref(v_traceState_457_);
v___x_459_ = lean_st_ref_take(v___y_454_);
v_traceState_460_ = lean_ctor_get(v___x_459_, 4);
v_env_461_ = lean_ctor_get(v___x_459_, 0);
v_nextMacroScope_462_ = lean_ctor_get(v___x_459_, 1);
v_ngen_463_ = lean_ctor_get(v___x_459_, 2);
v_auxDeclNGen_464_ = lean_ctor_get(v___x_459_, 3);
v_cache_465_ = lean_ctor_get(v___x_459_, 5);
v_messages_466_ = lean_ctor_get(v___x_459_, 6);
v_infoState_467_ = lean_ctor_get(v___x_459_, 7);
v_snapshotTasks_468_ = lean_ctor_get(v___x_459_, 8);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_487_ == 0)
{
v___x_470_ = v___x_459_;
v_isShared_471_ = v_isSharedCheck_487_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_snapshotTasks_468_);
lean_inc(v_infoState_467_);
lean_inc(v_messages_466_);
lean_inc(v_cache_465_);
lean_inc(v_traceState_460_);
lean_inc(v_auxDeclNGen_464_);
lean_inc(v_ngen_463_);
lean_inc(v_nextMacroScope_462_);
lean_inc(v_env_461_);
lean_dec(v___x_459_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_487_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
uint64_t v_tid_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_485_; 
v_tid_472_ = lean_ctor_get_uint64(v_traceState_460_, sizeof(void*)*1);
v_isSharedCheck_485_ = !lean_is_exclusive(v_traceState_460_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; 
v_unused_486_ = lean_ctor_get(v_traceState_460_, 0);
lean_dec(v_unused_486_);
v___x_474_ = v_traceState_460_;
v_isShared_475_ = v_isSharedCheck_485_;
goto v_resetjp_473_;
}
else
{
lean_dec(v_traceState_460_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_485_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_476_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__1);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_476_);
v___x_478_ = v___x_474_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_476_);
lean_ctor_set_uint64(v_reuseFailAlloc_484_, sizeof(void*)*1, v_tid_472_);
v___x_478_ = v_reuseFailAlloc_484_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_480_; 
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 4, v___x_478_);
v___x_480_ = v___x_470_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_env_461_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v_nextMacroScope_462_);
lean_ctor_set(v_reuseFailAlloc_483_, 2, v_ngen_463_);
lean_ctor_set(v_reuseFailAlloc_483_, 3, v_auxDeclNGen_464_);
lean_ctor_set(v_reuseFailAlloc_483_, 4, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_483_, 5, v_cache_465_);
lean_ctor_set(v_reuseFailAlloc_483_, 6, v_messages_466_);
lean_ctor_set(v_reuseFailAlloc_483_, 7, v_infoState_467_);
lean_ctor_set(v_reuseFailAlloc_483_, 8, v_snapshotTasks_468_);
v___x_480_ = v_reuseFailAlloc_483_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_st_ref_set(v___y_454_, v___x_480_);
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v_traces_458_);
return v___x_482_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___boxed(lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg(v___y_488_);
lean_dec(v___y_488_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9(lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg(v___y_494_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___boxed(lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9(v___y_497_, v___y_498_, v___y_499_, v___y_500_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
return v_res_502_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(lean_object* v_opts_503_, lean_object* v_opt_504_){
_start:
{
lean_object* v_name_505_; lean_object* v_defValue_506_; lean_object* v_map_507_; lean_object* v___x_508_; 
v_name_505_ = lean_ctor_get(v_opt_504_, 0);
v_defValue_506_ = lean_ctor_get(v_opt_504_, 1);
v_map_507_ = lean_ctor_get(v_opts_503_, 0);
v___x_508_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_507_, v_name_505_);
if (lean_obj_tag(v___x_508_) == 0)
{
uint8_t v___x_509_; 
v___x_509_ = lean_unbox(v_defValue_506_);
return v___x_509_;
}
else
{
lean_object* v_val_510_; 
v_val_510_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_val_510_);
lean_dec_ref(v___x_508_);
if (lean_obj_tag(v_val_510_) == 1)
{
uint8_t v_v_511_; 
v_v_511_ = lean_ctor_get_uint8(v_val_510_, 0);
lean_dec_ref(v_val_510_);
return v_v_511_;
}
else
{
uint8_t v___x_512_; 
lean_dec(v_val_510_);
v___x_512_ = lean_unbox(v_defValue_506_);
return v___x_512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10___boxed(lean_object* v_opts_513_, lean_object* v_opt_514_){
_start:
{
uint8_t v_res_515_; lean_object* v_r_516_; 
v_res_515_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_opts_513_, v_opt_514_);
lean_dec_ref(v_opt_514_);
lean_dec_ref(v_opts_513_);
v_r_516_ = lean_box(v_res_515_);
return v_r_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__0(lean_object* v_e_517_, uint8_t v___x_518_, lean_object* v_____r_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_525_ = lean_box(0);
v___x_526_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_526_, 0, v_e_517_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*2, v___x_518_);
v___x_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__0___boxed(lean_object* v_e_529_, lean_object* v___x_530_, lean_object* v_____r_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
uint8_t v___x_107500__boxed_537_; lean_object* v_res_538_; 
v___x_107500__boxed_537_ = lean_unbox(v___x_530_);
v_res_538_ = l_Lean_Meta_rwMatcher___lam__0(v_e_529_, v___x_107500__boxed_537_, v_____r_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
return v_res_538_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__1(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__0));
v___x_541_ = l_Lean_stringToMessageData(v___x_540_);
return v___x_541_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__3(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__2));
v___x_544_ = l_Lean_stringToMessageData(v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__1(lean_object* v___x_545_, uint8_t v___y_546_, lean_object* v_e_547_, lean_object* v_x_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_554_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__1, &l_Lean_Meta_rwMatcher___lam__1___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__1);
v___x_555_ = l_Lean_MessageData_ofConstName(v___x_545_, v___y_546_);
v___x_556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_554_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v___x_557_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__3, &l_Lean_Meta_rwMatcher___lam__1___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__3);
v___x_558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_556_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
v___x_559_ = l_Lean_indentExpr(v_e_547_);
v___x_560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_558_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__1___boxed(lean_object* v___x_562_, lean_object* v___y_563_, lean_object* v_e_564_, lean_object* v_x_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
uint8_t v___y_107542__boxed_571_; lean_object* v_res_572_; 
v___y_107542__boxed_571_ = lean_unbox(v___y_563_);
v_res_572_ = l_Lean_Meta_rwMatcher___lam__1(v___x_562_, v___y_107542__boxed_571_, v_e_564_, v_x_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec_ref(v_x_565_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(size_t v_sz_573_, size_t v_i_574_, lean_object* v_bs_575_){
_start:
{
uint8_t v___x_576_; 
v___x_576_ = lean_usize_dec_lt(v_i_574_, v_sz_573_);
if (v___x_576_ == 0)
{
return v_bs_575_;
}
else
{
lean_object* v_v_577_; lean_object* v___x_578_; lean_object* v_bs_x27_579_; lean_object* v___x_580_; size_t v___x_581_; size_t v___x_582_; lean_object* v___x_583_; 
v_v_577_ = lean_array_uget(v_bs_575_, v_i_574_);
v___x_578_ = lean_unsigned_to_nat(0u);
v_bs_x27_579_ = lean_array_uset(v_bs_575_, v_i_574_, v___x_578_);
v___x_580_ = l_Lean_Expr_mvarId_x21(v_v_577_);
lean_dec(v_v_577_);
v___x_581_ = ((size_t)1ULL);
v___x_582_ = lean_usize_add(v_i_574_, v___x_581_);
v___x_583_ = lean_array_uset(v_bs_x27_579_, v_i_574_, v___x_580_);
v_i_574_ = v___x_582_;
v_bs_575_ = v___x_583_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3___boxed(lean_object* v_sz_585_, lean_object* v_i_586_, lean_object* v_bs_587_){
_start:
{
size_t v_sz_boxed_588_; size_t v_i_boxed_589_; lean_object* v_res_590_; 
v_sz_boxed_588_ = lean_unbox_usize(v_sz_585_);
lean_dec(v_sz_585_);
v_i_boxed_589_ = lean_unbox_usize(v_i_586_);
lean_dec(v_i_586_);
v_res_590_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_boxed_588_, v_i_boxed_589_, v_bs_587_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(lean_object* v_msgData_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v___x_597_; lean_object* v_env_598_; lean_object* v___x_599_; lean_object* v_mctx_600_; lean_object* v_lctx_601_; lean_object* v_options_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_597_ = lean_st_ref_get(v___y_595_);
v_env_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc_ref(v_env_598_);
lean_dec(v___x_597_);
v___x_599_ = lean_st_ref_get(v___y_593_);
v_mctx_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc_ref(v_mctx_600_);
lean_dec(v___x_599_);
v_lctx_601_ = lean_ctor_get(v___y_592_, 2);
v_options_602_ = lean_ctor_get(v___y_594_, 2);
lean_inc_ref(v_options_602_);
lean_inc_ref(v_lctx_601_);
v___x_603_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_603_, 0, v_env_598_);
lean_ctor_set(v___x_603_, 1, v_mctx_600_);
lean_ctor_set(v___x_603_, 2, v_lctx_601_);
lean_ctor_set(v___x_603_, 3, v_options_602_);
v___x_604_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
lean_ctor_set(v___x_604_, 1, v_msgData_591_);
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3___boxed(lean_object* v_msgData_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msgData_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(lean_object* v_msg_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_ref_619_; lean_object* v___x_620_; lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_629_; 
v_ref_619_ = lean_ctor_get(v___y_616_, 5);
v___x_620_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
v_a_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_629_ == 0)
{
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_629_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_629_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; lean_object* v___x_627_; 
lean_inc(v_ref_619_);
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v_ref_619_);
lean_ctor_set(v___x_625_, 1, v_a_621_);
if (v_isShared_624_ == 0)
{
lean_ctor_set_tag(v___x_623_, 1);
lean_ctor_set(v___x_623_, 0, v___x_625_);
v___x_627_ = v___x_623_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg___boxed(lean_object* v_msg_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v_msg_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
return v_res_636_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20___redArg(lean_object* v_keys_637_, lean_object* v_i_638_, lean_object* v_k_639_){
_start:
{
lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_640_ = lean_array_get_size(v_keys_637_);
v___x_641_ = lean_nat_dec_lt(v_i_638_, v___x_640_);
if (v___x_641_ == 0)
{
lean_dec(v_i_638_);
return v___x_641_;
}
else
{
lean_object* v_k_x27_642_; uint8_t v___x_643_; 
v_k_x27_642_ = lean_array_fget_borrowed(v_keys_637_, v_i_638_);
v___x_643_ = l_Lean_instBEqMVarId_beq(v_k_639_, v_k_x27_642_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_unsigned_to_nat(1u);
v___x_645_ = lean_nat_add(v_i_638_, v___x_644_);
lean_dec(v_i_638_);
v_i_638_ = v___x_645_;
goto _start;
}
else
{
lean_dec(v_i_638_);
return v___x_643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20___redArg___boxed(lean_object* v_keys_647_, lean_object* v_i_648_, lean_object* v_k_649_){
_start:
{
uint8_t v_res_650_; lean_object* v_r_651_; 
v_res_650_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20___redArg(v_keys_647_, v_i_648_, v_k_649_);
lean_dec(v_k_649_);
lean_dec_ref(v_keys_647_);
v_r_651_ = lean_box(v_res_650_);
return v_r_651_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__0(void){
_start:
{
size_t v___x_652_; size_t v___x_653_; size_t v___x_654_; 
v___x_652_ = ((size_t)5ULL);
v___x_653_ = ((size_t)1ULL);
v___x_654_ = lean_usize_shift_left(v___x_653_, v___x_652_);
return v___x_654_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_655_; size_t v___x_656_; size_t v___x_657_; 
v___x_655_ = ((size_t)1ULL);
v___x_656_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__0);
v___x_657_ = lean_usize_sub(v___x_656_, v___x_655_);
return v___x_657_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(lean_object* v_x_658_, size_t v_x_659_, lean_object* v_x_660_){
_start:
{
if (lean_obj_tag(v_x_658_) == 0)
{
lean_object* v_es_661_; lean_object* v___x_662_; size_t v___x_663_; size_t v___x_664_; size_t v___x_665_; lean_object* v_j_666_; lean_object* v___x_667_; 
v_es_661_ = lean_ctor_get(v_x_658_, 0);
v___x_662_ = lean_box(2);
v___x_663_ = ((size_t)5ULL);
v___x_664_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__1);
v___x_665_ = lean_usize_land(v_x_659_, v___x_664_);
v_j_666_ = lean_usize_to_nat(v___x_665_);
v___x_667_ = lean_array_get_borrowed(v___x_662_, v_es_661_, v_j_666_);
lean_dec(v_j_666_);
switch(lean_obj_tag(v___x_667_))
{
case 0:
{
lean_object* v_key_668_; uint8_t v___x_669_; 
v_key_668_ = lean_ctor_get(v___x_667_, 0);
v___x_669_ = l_Lean_instBEqMVarId_beq(v_x_660_, v_key_668_);
return v___x_669_;
}
case 1:
{
lean_object* v_node_670_; size_t v___x_671_; 
v_node_670_ = lean_ctor_get(v___x_667_, 0);
v___x_671_ = lean_usize_shift_right(v_x_659_, v___x_663_);
v_x_658_ = v_node_670_;
v_x_659_ = v___x_671_;
goto _start;
}
default: 
{
uint8_t v___x_673_; 
v___x_673_ = 0;
return v___x_673_;
}
}
}
else
{
lean_object* v_ks_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v_ks_674_ = lean_ctor_get(v_x_658_, 0);
v___x_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20___redArg(v_ks_674_, v___x_675_, v_x_660_);
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_677_, lean_object* v_x_678_, lean_object* v_x_679_){
_start:
{
size_t v_x_107687__boxed_680_; uint8_t v_res_681_; lean_object* v_r_682_; 
v_x_107687__boxed_680_ = lean_unbox_usize(v_x_678_);
lean_dec(v_x_678_);
v_res_681_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_677_, v_x_107687__boxed_680_, v_x_679_);
lean_dec(v_x_679_);
lean_dec_ref(v_x_677_);
v_r_682_ = lean_box(v_res_681_);
return v_r_682_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(lean_object* v_x_683_, lean_object* v_x_684_){
_start:
{
uint64_t v___x_685_; size_t v___x_686_; uint8_t v___x_687_; 
v___x_685_ = l_Lean_instHashableMVarId_hash(v_x_684_);
v___x_686_ = lean_uint64_to_usize(v___x_685_);
v___x_687_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_683_, v___x_686_, v_x_684_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg___boxed(lean_object* v_x_688_, lean_object* v_x_689_){
_start:
{
uint8_t v_res_690_; lean_object* v_r_691_; 
v_res_690_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_x_688_, v_x_689_);
lean_dec(v_x_689_);
lean_dec_ref(v_x_688_);
v_r_691_ = lean_box(v_res_690_);
return v_r_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(lean_object* v_mvarId_692_, lean_object* v___y_693_){
_start:
{
lean_object* v___x_695_; lean_object* v_mctx_696_; lean_object* v_eAssignment_697_; uint8_t v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_695_ = lean_st_ref_get(v___y_693_);
v_mctx_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc_ref(v_mctx_696_);
lean_dec(v___x_695_);
v_eAssignment_697_ = lean_ctor_get(v_mctx_696_, 8);
lean_inc_ref(v_eAssignment_697_);
lean_dec_ref(v_mctx_696_);
v___x_698_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_eAssignment_697_, v_mvarId_692_);
lean_dec_ref(v_eAssignment_697_);
v___x_699_ = lean_box(v___x_698_);
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg___boxed(lean_object* v_mvarId_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_mvarId_701_, v___y_702_);
lean_dec(v___y_702_);
lean_dec(v_mvarId_701_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12(uint8_t v___x_705_, lean_object* v_as_706_, size_t v_i_707_, size_t v_stop_708_, lean_object* v_b_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v_a_716_; uint8_t v___x_720_; 
v___x_720_ = lean_usize_dec_eq(v_i_707_, v_stop_708_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; uint8_t v_a_725_; lean_object* v___x_726_; 
v___x_721_ = lean_array_uget_borrowed(v_as_706_, v_i_707_);
v___x_726_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v___x_721_, v___y_711_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; uint8_t v___x_728_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref(v___x_726_);
v___x_728_ = lean_unbox(v_a_727_);
lean_dec(v_a_727_);
if (v___x_728_ == 0)
{
goto v___jp_722_;
}
else
{
v_a_725_ = v___x_705_;
goto v___jp_724_;
}
}
else
{
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_729_; uint8_t v___x_730_; 
v_a_729_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_729_);
lean_dec_ref(v___x_726_);
v___x_730_ = lean_unbox(v_a_729_);
lean_dec(v_a_729_);
v_a_725_ = v___x_730_;
goto v___jp_724_;
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec_ref(v_b_709_);
v_a_731_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_726_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_726_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
v___jp_722_:
{
lean_object* v___x_723_; 
lean_inc(v___x_721_);
v___x_723_ = lean_array_push(v_b_709_, v___x_721_);
v_a_716_ = v___x_723_;
goto v___jp_715_;
}
v___jp_724_:
{
if (v_a_725_ == 0)
{
v_a_716_ = v_b_709_;
goto v___jp_715_;
}
else
{
goto v___jp_722_;
}
}
}
else
{
lean_object* v___x_739_; 
v___x_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_739_, 0, v_b_709_);
return v___x_739_;
}
v___jp_715_:
{
size_t v___x_717_; size_t v___x_718_; 
v___x_717_ = ((size_t)1ULL);
v___x_718_ = lean_usize_add(v_i_707_, v___x_717_);
v_i_707_ = v___x_718_;
v_b_709_ = v_a_716_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12___boxed(lean_object* v___x_740_, lean_object* v_as_741_, lean_object* v_i_742_, lean_object* v_stop_743_, lean_object* v_b_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
uint8_t v___x_107759__boxed_750_; size_t v_i_boxed_751_; size_t v_stop_boxed_752_; lean_object* v_res_753_; 
v___x_107759__boxed_750_ = lean_unbox(v___x_740_);
v_i_boxed_751_ = lean_unbox_usize(v_i_742_);
lean_dec(v_i_742_);
v_stop_boxed_752_ = lean_unbox_usize(v_stop_743_);
lean_dec(v_stop_743_);
v_res_753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12(v___x_107759__boxed_750_, v_as_741_, v_i_boxed_751_, v_stop_boxed_752_, v_b_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec_ref(v_as_741_);
return v_res_753_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__0));
v___x_756_ = l_Lean_stringToMessageData(v___x_755_);
return v___x_756_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__2));
v___x_759_ = l_Lean_stringToMessageData(v___x_758_);
return v___x_759_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__4));
v___x_762_ = l_Lean_stringToMessageData(v___x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(lean_object* v_as_763_, size_t v_sz_764_, size_t v_i_765_, lean_object* v_b_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_a_773_; uint8_t v___x_777_; 
v___x_777_ = lean_usize_dec_lt(v_i_765_, v_sz_764_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; 
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v_b_766_);
return v___x_778_;
}
else
{
lean_object* v_a_779_; lean_object* v___x_780_; 
v_a_779_ = lean_array_uget_borrowed(v_as_763_, v_i_765_);
v___x_780_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_a_779_, v___y_768_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; lean_object* v___x_782_; lean_object* v___y_784_; lean_object* v___y_786_; lean_object* v___y_787_; uint8_t v___y_788_; lean_object* v___y_804_; lean_object* v___y_806_; lean_object* v___y_807_; uint8_t v___y_808_; lean_object* v___y_824_; uint8_t v___x_825_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_781_);
lean_dec_ref(v___x_780_);
v___x_782_ = lean_box(0);
v___x_825_ = lean_unbox(v_a_781_);
lean_dec(v_a_781_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; 
lean_inc(v_a_779_);
v___x_826_ = l_Lean_MVarId_getType(v_a_779_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; uint8_t v___x_828_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc_n(v_a_827_, 2);
lean_dec_ref(v___x_826_);
v___x_828_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_a_827_);
if (v___x_828_ == 0)
{
uint8_t v___x_829_; 
v___x_829_ = l_Lean_Expr_isEq(v_a_827_);
if (v___x_829_ == 0)
{
uint8_t v___x_830_; 
v___x_830_ = l_Lean_Expr_isHEq(v_a_827_);
lean_dec(v_a_827_);
if (v___x_830_ == 0)
{
v_a_773_ = v___x_782_;
goto v___jp_772_;
}
else
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_Meta_saveState___redArg(v___y_768_, v___y_770_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; lean_object* v___x_833_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_832_);
lean_dec_ref(v___x_831_);
lean_inc(v_a_779_);
v___x_833_ = l_Lean_MVarId_assumption(v_a_779_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_dec(v_a_832_);
v___y_804_ = v___x_833_;
goto v___jp_803_;
}
else
{
lean_object* v_a_834_; uint8_t v___y_836_; uint8_t v___x_852_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_a_834_);
v___x_852_ = l_Lean_Exception_isInterrupt(v_a_834_);
if (v___x_852_ == 0)
{
uint8_t v___x_853_; 
v___x_853_ = l_Lean_Exception_isRuntime(v_a_834_);
v___y_836_ = v___x_853_;
goto v___jp_835_;
}
else
{
lean_dec(v_a_834_);
v___y_836_ = v___x_852_;
goto v___jp_835_;
}
v___jp_835_:
{
if (v___y_836_ == 0)
{
lean_object* v___x_837_; 
lean_dec_ref(v___x_833_);
v___x_837_ = l_Lean_Meta_SavedState_restore___redArg(v_a_832_, v___y_768_, v___y_770_);
lean_dec(v_a_832_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v___x_838_; 
lean_dec_ref(v___x_837_);
v___x_838_ = l_Lean_Meta_saveState___redArg(v___y_768_, v___y_770_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v___x_840_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_a_839_);
lean_dec_ref(v___x_838_);
lean_inc(v_a_779_);
v___x_840_ = l_Lean_MVarId_hrefl(v_a_779_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_dec(v_a_839_);
v___y_804_ = v___x_840_;
goto v___jp_803_;
}
else
{
lean_object* v_a_841_; uint8_t v___x_842_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_a_841_);
v___x_842_ = l_Lean_Exception_isInterrupt(v_a_841_);
if (v___x_842_ == 0)
{
uint8_t v___x_843_; 
v___x_843_ = l_Lean_Exception_isRuntime(v_a_841_);
v___y_806_ = v___x_840_;
v___y_807_ = v_a_839_;
v___y_808_ = v___x_843_;
goto v___jp_805_;
}
else
{
lean_dec(v_a_841_);
v___y_806_ = v___x_840_;
v___y_807_ = v_a_839_;
v___y_808_ = v___x_842_;
goto v___jp_805_;
}
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
v_a_844_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_838_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_838_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
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
v___y_804_ = v___x_837_;
goto v___jp_803_;
}
}
else
{
lean_dec(v_a_832_);
v___y_804_ = v___x_833_;
goto v___jp_803_;
}
}
}
}
else
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
v_a_854_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_831_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_831_);
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
lean_object* v___x_862_; 
lean_dec(v_a_827_);
v___x_862_ = l_Lean_Meta_saveState___redArg(v___y_768_, v___y_770_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_864_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref(v___x_862_);
lean_inc(v_a_779_);
v___x_864_ = l_Lean_MVarId_assumption(v_a_779_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_dec(v_a_863_);
v___y_784_ = v___x_864_;
goto v___jp_783_;
}
else
{
lean_object* v_a_865_; uint8_t v___y_867_; uint8_t v___x_883_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
v___x_883_ = l_Lean_Exception_isInterrupt(v_a_865_);
if (v___x_883_ == 0)
{
uint8_t v___x_884_; 
v___x_884_ = l_Lean_Exception_isRuntime(v_a_865_);
v___y_867_ = v___x_884_;
goto v___jp_866_;
}
else
{
lean_dec(v_a_865_);
v___y_867_ = v___x_883_;
goto v___jp_866_;
}
v___jp_866_:
{
if (v___y_867_ == 0)
{
lean_object* v___x_868_; 
lean_dec_ref(v___x_864_);
v___x_868_ = l_Lean_Meta_SavedState_restore___redArg(v_a_863_, v___y_768_, v___y_770_);
lean_dec(v_a_863_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v___x_869_; 
lean_dec_ref(v___x_868_);
v___x_869_ = l_Lean_Meta_saveState___redArg(v___y_768_, v___y_770_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_871_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_a_870_);
lean_dec_ref(v___x_869_);
lean_inc(v_a_779_);
v___x_871_ = l_Lean_MVarId_refl(v_a_779_, v___x_829_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_dec(v_a_870_);
v___y_784_ = v___x_871_;
goto v___jp_783_;
}
else
{
lean_object* v_a_872_; uint8_t v___x_873_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
v___x_873_ = l_Lean_Exception_isInterrupt(v_a_872_);
if (v___x_873_ == 0)
{
uint8_t v___x_874_; 
v___x_874_ = l_Lean_Exception_isRuntime(v_a_872_);
v___y_786_ = v___x_871_;
v___y_787_ = v_a_870_;
v___y_788_ = v___x_874_;
goto v___jp_785_;
}
else
{
lean_dec(v_a_872_);
v___y_786_ = v___x_871_;
v___y_787_ = v_a_870_;
v___y_788_ = v___x_873_;
goto v___jp_785_;
}
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
v_a_875_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_869_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_869_);
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
v___y_784_ = v___x_868_;
goto v___jp_783_;
}
}
else
{
lean_dec(v_a_863_);
v___y_784_ = v___x_864_;
goto v___jp_783_;
}
}
}
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
v_a_885_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_862_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_862_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
else
{
lean_object* v___x_893_; 
lean_dec(v_a_827_);
v___x_893_ = l_Lean_Meta_saveState___redArg(v___y_768_, v___y_770_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_895_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_a_894_);
lean_dec_ref(v___x_893_);
lean_inc(v_a_779_);
v___x_895_ = l_Lean_MVarId_assumption(v_a_779_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_dec(v_a_894_);
v___y_824_ = v___x_895_;
goto v___jp_823_;
}
else
{
lean_object* v_a_896_; uint8_t v___y_898_; uint8_t v___x_913_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_a_896_);
v___x_913_ = l_Lean_Exception_isInterrupt(v_a_896_);
if (v___x_913_ == 0)
{
uint8_t v___x_914_; 
v___x_914_ = l_Lean_Exception_isRuntime(v_a_896_);
v___y_898_ = v___x_914_;
goto v___jp_897_;
}
else
{
lean_dec(v_a_896_);
v___y_898_ = v___x_913_;
goto v___jp_897_;
}
v___jp_897_:
{
if (v___y_898_ == 0)
{
lean_object* v___x_899_; 
lean_dec_ref(v___x_895_);
v___x_899_ = l_Lean_Meta_SavedState_restore___redArg(v_a_894_, v___y_768_, v___y_770_);
lean_dec(v_a_894_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_911_; 
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_911_ == 0)
{
lean_object* v_unused_912_; 
v_unused_912_ = lean_ctor_get(v___x_899_, 0);
lean_dec(v_unused_912_);
v___x_901_ = v___x_899_;
v_isShared_902_ = v_isSharedCheck_911_;
goto v_resetjp_900_;
}
else
{
lean_dec(v___x_899_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_911_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; lean_object* v___x_905_; 
v___x_903_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5);
lean_inc(v_a_779_);
if (v_isShared_902_ == 0)
{
lean_ctor_set_tag(v___x_901_, 1);
lean_ctor_set(v___x_901_, 0, v_a_779_);
v___x_905_ = v___x_901_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_779_);
v___x_905_ = v_reuseFailAlloc_910_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_903_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_908_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
v___y_824_ = v___x_909_;
goto v___jp_823_;
}
}
}
else
{
v___y_824_ = v___x_899_;
goto v___jp_823_;
}
}
else
{
lean_dec(v_a_894_);
v___y_824_ = v___x_895_;
goto v___jp_823_;
}
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
v_a_915_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_893_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_893_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
v_a_923_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_826_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_826_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
else
{
v_a_773_ = v___x_782_;
goto v___jp_772_;
}
v___jp_783_:
{
if (lean_obj_tag(v___y_784_) == 0)
{
lean_dec_ref(v___y_784_);
v_a_773_ = v___x_782_;
goto v___jp_772_;
}
else
{
return v___y_784_;
}
}
v___jp_785_:
{
if (v___y_788_ == 0)
{
lean_object* v___x_789_; 
lean_dec_ref(v___y_786_);
v___x_789_ = l_Lean_Meta_SavedState_restore___redArg(v___y_787_, v___y_768_, v___y_770_);
lean_dec_ref(v___y_787_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_801_; 
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_801_ == 0)
{
lean_object* v_unused_802_; 
v_unused_802_ = lean_ctor_get(v___x_789_, 0);
lean_dec(v_unused_802_);
v___x_791_ = v___x_789_;
v_isShared_792_ = v_isSharedCheck_801_;
goto v_resetjp_790_;
}
else
{
lean_dec(v___x_789_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_801_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_793_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1);
lean_inc(v_a_779_);
if (v_isShared_792_ == 0)
{
lean_ctor_set_tag(v___x_791_, 1);
lean_ctor_set(v___x_791_, 0, v_a_779_);
v___x_795_ = v___x_791_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_779_);
v___x_795_ = v_reuseFailAlloc_800_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_793_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_796_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_798_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
v___y_784_ = v___x_799_;
goto v___jp_783_;
}
}
}
else
{
v___y_784_ = v___x_789_;
goto v___jp_783_;
}
}
else
{
lean_dec_ref(v___y_787_);
v___y_784_ = v___y_786_;
goto v___jp_783_;
}
}
v___jp_803_:
{
if (lean_obj_tag(v___y_804_) == 0)
{
lean_dec_ref(v___y_804_);
v_a_773_ = v___x_782_;
goto v___jp_772_;
}
else
{
return v___y_804_;
}
}
v___jp_805_:
{
if (v___y_808_ == 0)
{
lean_object* v___x_809_; 
lean_dec_ref(v___y_806_);
v___x_809_ = l_Lean_Meta_SavedState_restore___redArg(v___y_807_, v___y_768_, v___y_770_);
lean_dec_ref(v___y_807_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_821_; 
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v___x_809_, 0);
lean_dec(v_unused_822_);
v___x_811_ = v___x_809_;
v_isShared_812_ = v_isSharedCheck_821_;
goto v_resetjp_810_;
}
else
{
lean_dec(v___x_809_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_821_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_813_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1);
lean_inc(v_a_779_);
if (v_isShared_812_ == 0)
{
lean_ctor_set_tag(v___x_811_, 1);
lean_ctor_set(v___x_811_, 0, v_a_779_);
v___x_815_ = v___x_811_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_779_);
v___x_815_ = v_reuseFailAlloc_820_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_813_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_818_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
v___y_804_ = v___x_819_;
goto v___jp_803_;
}
}
}
else
{
v___y_804_ = v___x_809_;
goto v___jp_803_;
}
}
else
{
lean_dec_ref(v___y_807_);
v___y_804_ = v___y_806_;
goto v___jp_803_;
}
}
v___jp_823_:
{
if (lean_obj_tag(v___y_824_) == 0)
{
lean_dec_ref(v___y_824_);
v_a_773_ = v___x_782_;
goto v___jp_772_;
}
else
{
return v___y_824_;
}
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
v_a_931_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_780_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_780_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
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
v___jp_772_:
{
size_t v___x_774_; size_t v___x_775_; 
v___x_774_ = ((size_t)1ULL);
v___x_775_ = lean_usize_add(v_i_765_, v___x_774_);
v_i_765_ = v___x_775_;
v_b_766_ = v_a_773_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___boxed(lean_object* v_as_939_, lean_object* v_sz_940_, lean_object* v_i_941_, lean_object* v_b_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
size_t v_sz_boxed_948_; size_t v_i_boxed_949_; lean_object* v_res_950_; 
v_sz_boxed_948_ = lean_unbox_usize(v_sz_940_);
lean_dec(v_sz_940_);
v_i_boxed_949_ = lean_unbox_usize(v_i_941_);
lean_dec(v_i_941_);
v_res_950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v_as_939_, v_sz_boxed_948_, v_i_boxed_949_, v_b_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec_ref(v_as_939_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
if (lean_obj_tag(v_a_951_) == 0)
{
lean_object* v___x_953_; 
v___x_953_ = l_List_reverse___redArg(v_a_952_);
return v___x_953_;
}
else
{
lean_object* v_head_954_; lean_object* v_tail_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_964_; 
v_head_954_ = lean_ctor_get(v_a_951_, 0);
v_tail_955_ = lean_ctor_get(v_a_951_, 1);
v_isSharedCheck_964_ = !lean_is_exclusive(v_a_951_);
if (v_isSharedCheck_964_ == 0)
{
v___x_957_ = v_a_951_;
v_isShared_958_ = v_isSharedCheck_964_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_tail_955_);
lean_inc(v_head_954_);
lean_dec(v_a_951_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_964_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; lean_object* v___x_961_; 
v___x_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_959_, 0, v_head_954_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 1, v_a_952_);
lean_ctor_set(v___x_957_, 0, v___x_959_);
v___x_961_ = v___x_957_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_959_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_a_952_);
v___x_961_ = v_reuseFailAlloc_963_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
v_a_951_ = v_tail_955_;
v_a_952_ = v___x_961_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__1(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__0));
v___x_967_ = l_Lean_stringToMessageData(v___x_966_);
return v___x_967_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__3(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__2));
v___x_970_ = l_Lean_stringToMessageData(v___x_969_);
return v___x_970_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__5(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__4));
v___x_973_ = l_Lean_stringToMessageData(v___x_972_);
return v___x_973_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__7(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__6));
v___x_976_ = l_Lean_stringToMessageData(v___x_975_);
return v___x_976_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__9(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__8));
v___x_979_ = l_Lean_stringToMessageData(v___x_978_);
return v___x_979_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__12(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__11));
v___x_984_ = l_Lean_stringToMessageData(v___x_983_);
return v___x_984_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__14(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__13));
v___x_987_ = l_Lean_stringToMessageData(v___x_986_);
return v___x_987_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__16(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__15));
v___x_990_ = l_Lean_stringToMessageData(v___x_989_);
return v___x_990_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__22(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__21));
v___x_999_ = l_Lean_stringToMessageData(v___x_998_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__24(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__23));
v___x_1002_ = l_Lean_stringToMessageData(v___x_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2(uint8_t v___x_1003_, lean_object* v___x_1004_, lean_object* v_fst_1005_, lean_object* v___x_1006_, uint8_t v___x_1007_, lean_object* v_e_1008_, lean_object* v_snd_1009_, lean_object* v_____r_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v___y_1017_; lean_object* v_proof_1018_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; uint8_t v___y_1043_; lean_object* v___x_1055_; lean_object* v___y_1057_; uint8_t v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1073_; uint8_t v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v_a_1079_; lean_object* v___y_1103_; uint8_t v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; size_t v_sz_1119_; size_t v___x_1120_; lean_object* v___x_1121_; lean_object* v___y_1123_; uint8_t v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1150_; uint8_t v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; uint8_t v_fst_1180_; lean_object* v_fst_1181_; lean_object* v_snd_1182_; lean_object* v___x_1194_; lean_object* v___x_1195_; uint8_t v___x_1196_; 
v___x_1055_ = l_Lean_mkAppN(v___x_1004_, v_fst_1005_);
v_sz_1119_ = lean_array_size(v_fst_1005_);
v___x_1120_ = ((size_t)0ULL);
v___x_1121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_1119_, v___x_1120_, v_fst_1005_);
v___x_1194_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1195_ = lean_unsigned_to_nat(4u);
v___x_1196_ = l_Lean_Expr_isAppOfArity(v_snd_1009_, v___x_1194_, v___x_1195_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1197_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1198_ = lean_unsigned_to_nat(3u);
v___x_1199_ = l_Lean_Expr_isAppOfArity(v_snd_1009_, v___x_1197_, v___x_1198_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_dec_ref(v___x_1121_);
lean_dec_ref(v___x_1055_);
lean_dec_ref(v_e_1008_);
v___x_1200_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1201_ = l_Lean_MessageData_ofConstName(v___x_1006_, v___x_1007_);
v___x_1202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1200_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1202_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
v___x_1205_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1204_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1205_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1205_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
else
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1214_ = l_Lean_Expr_appFn_x21(v_snd_1009_);
v___x_1215_ = l_Lean_Expr_appArg_x21(v___x_1214_);
lean_dec_ref(v___x_1214_);
v___x_1216_ = l_Lean_Expr_appArg_x21(v_snd_1009_);
v_fst_1180_ = v___x_1007_;
v_fst_1181_ = v___x_1215_;
v_snd_1182_ = v___x_1216_;
goto v___jp_1179_;
}
}
else
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1217_ = l_Lean_Expr_appFn_x21(v_snd_1009_);
v___x_1218_ = l_Lean_Expr_appFn_x21(v___x_1217_);
lean_dec_ref(v___x_1217_);
v___x_1219_ = l_Lean_Expr_appArg_x21(v___x_1218_);
lean_dec_ref(v___x_1218_);
v___x_1220_ = l_Lean_Expr_appArg_x21(v_snd_1009_);
v_fst_1180_ = v___x_1003_;
v_fst_1181_ = v___x_1219_;
v_snd_1182_ = v___x_1220_;
goto v___jp_1179_;
}
v___jp_1016_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1019_, 0, v_proof_1018_);
v___x_1020_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1020_, 0, v___y_1017_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
lean_ctor_set_uint8(v___x_1020_, sizeof(void*)*2, v___x_1003_);
v___x_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
return v___x_1021_;
}
v___jp_1022_:
{
if (lean_obj_tag(v___y_1024_) == 0)
{
lean_object* v_a_1025_; 
v_a_1025_ = lean_ctor_get(v___y_1024_, 0);
lean_inc(v_a_1025_);
lean_dec_ref(v___y_1024_);
v___y_1017_ = v___y_1023_;
v_proof_1018_ = v_a_1025_;
goto v___jp_1016_;
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec_ref(v___y_1023_);
v_a_1026_ = lean_ctor_get(v___y_1024_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___y_1024_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___y_1024_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___y_1024_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
v___jp_1034_:
{
if (v___y_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_dec_ref(v___y_1037_);
v___x_1044_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1045_ = l_Lean_MessageData_ofExpr(v___y_1036_);
v___x_1046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1046_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = l_Lean_Exception_toMessageData(v___y_1041_);
v___x_1050_ = l_Lean_indentD(v___x_1049_);
v___x_1051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1048_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1051_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v___x_1054_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1053_, v___y_1040_, v___y_1039_, v___y_1038_, v___y_1035_);
v___y_1023_ = v___y_1042_;
v___y_1024_ = v___x_1054_;
goto v___jp_1022_;
}
else
{
lean_dec_ref(v___y_1041_);
lean_dec_ref(v___y_1036_);
v___y_1023_ = v___y_1042_;
v___y_1024_ = v___y_1037_;
goto v___jp_1022_;
}
}
v___jp_1056_:
{
lean_object* v___x_1063_; lean_object* v_a_1064_; lean_object* v___x_1065_; 
v___x_1063_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_1057_, v___y_1060_);
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1064_);
lean_dec_ref(v___x_1063_);
v___x_1065_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___x_1055_, v___y_1060_);
if (v___y_1058_ == 0)
{
lean_object* v_a_1066_; 
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1066_);
lean_dec_ref(v___x_1065_);
v___y_1017_ = v_a_1064_;
v_proof_1018_ = v_a_1066_;
goto v___jp_1016_;
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1068_; 
v_a_1067_ = lean_ctor_get(v___x_1065_, 0);
lean_inc_n(v_a_1067_, 2);
lean_dec_ref(v___x_1065_);
v___x_1068_ = l_Lean_Meta_mkEqOfHEq(v_a_1067_, v___x_1003_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_dec(v_a_1067_);
v___y_1023_ = v_a_1064_;
v___y_1024_ = v___x_1068_;
goto v___jp_1022_;
}
else
{
lean_object* v_a_1069_; uint8_t v___x_1070_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
v___x_1070_ = l_Lean_Exception_isInterrupt(v_a_1069_);
if (v___x_1070_ == 0)
{
uint8_t v___x_1071_; 
lean_inc(v_a_1069_);
v___x_1071_ = l_Lean_Exception_isRuntime(v_a_1069_);
v___y_1035_ = v___y_1062_;
v___y_1036_ = v_a_1067_;
v___y_1037_ = v___x_1068_;
v___y_1038_ = v___y_1061_;
v___y_1039_ = v___y_1060_;
v___y_1040_ = v___y_1059_;
v___y_1041_ = v_a_1069_;
v___y_1042_ = v_a_1064_;
v___y_1043_ = v___x_1071_;
goto v___jp_1034_;
}
else
{
v___y_1035_ = v___y_1062_;
v___y_1036_ = v_a_1067_;
v___y_1037_ = v___x_1068_;
v___y_1038_ = v___y_1061_;
v___y_1039_ = v___y_1060_;
v___y_1040_ = v___y_1059_;
v___y_1041_ = v_a_1069_;
v___y_1042_ = v_a_1064_;
v___y_1043_ = v___x_1070_;
goto v___jp_1034_;
}
}
}
}
v___jp_1072_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1080_ = lean_array_get_size(v_a_1079_);
v___x_1081_ = lean_unsigned_to_nat(0u);
v___x_1082_ = lean_nat_dec_eq(v___x_1080_, v___x_1081_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
lean_dec_ref(v___y_1073_);
lean_dec_ref(v___x_1055_);
v___x_1083_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1084_ = l_Lean_MessageData_ofConstName(v___x_1006_, v___x_1007_);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = lean_array_to_list(v_a_1079_);
v___x_1089_ = lean_box(0);
v___x_1090_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_1088_, v___x_1089_);
v___x_1091_ = l_Lean_MessageData_ofList(v___x_1090_);
v___x_1092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1087_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1092_, v___y_1075_, v___y_1078_, v___y_1077_, v___y_1076_);
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v___x_1093_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1093_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
else
{
lean_dec_ref(v_a_1079_);
lean_dec(v___x_1006_);
v___y_1057_ = v___y_1073_;
v___y_1058_ = v___y_1074_;
v___y_1059_ = v___y_1075_;
v___y_1060_ = v___y_1078_;
v___y_1061_ = v___y_1077_;
v___y_1062_ = v___y_1076_;
goto v___jp_1056_;
}
}
v___jp_1102_:
{
if (lean_obj_tag(v___y_1109_) == 0)
{
lean_object* v_a_1110_; 
v_a_1110_ = lean_ctor_get(v___y_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref(v___y_1109_);
v___y_1073_ = v___y_1103_;
v___y_1074_ = v___y_1104_;
v___y_1075_ = v___y_1105_;
v___y_1076_ = v___y_1106_;
v___y_1077_ = v___y_1107_;
v___y_1078_ = v___y_1108_;
v_a_1079_ = v_a_1110_;
goto v___jp_1072_;
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec_ref(v___y_1103_);
lean_dec_ref(v___x_1055_);
lean_dec(v___x_1006_);
v_a_1111_ = lean_ctor_get(v___y_1109_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___y_1109_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___y_1109_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___y_1109_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
v___jp_1122_:
{
lean_object* v___x_1129_; size_t v_sz_1130_; lean_object* v___x_1131_; 
v___x_1129_ = lean_box(0);
v_sz_1130_ = lean_array_size(v___x_1121_);
v___x_1131_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1121_, v_sz_1130_, v___x_1120_, v___x_1129_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
lean_dec_ref(v___x_1131_);
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = lean_array_get_size(v___x_1121_);
v___x_1134_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1135_ = lean_nat_dec_lt(v___x_1132_, v___x_1133_);
if (v___x_1135_ == 0)
{
lean_dec_ref(v___x_1121_);
v___y_1073_ = v___y_1123_;
v___y_1074_ = v___y_1124_;
v___y_1075_ = v___y_1125_;
v___y_1076_ = v___y_1128_;
v___y_1077_ = v___y_1127_;
v___y_1078_ = v___y_1126_;
v_a_1079_ = v___x_1134_;
goto v___jp_1072_;
}
else
{
uint8_t v___x_1136_; 
v___x_1136_ = lean_nat_dec_le(v___x_1133_, v___x_1133_);
if (v___x_1136_ == 0)
{
if (v___x_1135_ == 0)
{
lean_dec_ref(v___x_1121_);
v___y_1073_ = v___y_1123_;
v___y_1074_ = v___y_1124_;
v___y_1075_ = v___y_1125_;
v___y_1076_ = v___y_1128_;
v___y_1077_ = v___y_1127_;
v___y_1078_ = v___y_1126_;
v_a_1079_ = v___x_1134_;
goto v___jp_1072_;
}
else
{
size_t v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_usize_of_nat(v___x_1133_);
v___x_1138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12(v___x_1007_, v___x_1121_, v___x_1120_, v___x_1137_, v___x_1134_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
lean_dec_ref(v___x_1121_);
v___y_1103_ = v___y_1123_;
v___y_1104_ = v___y_1124_;
v___y_1105_ = v___y_1125_;
v___y_1106_ = v___y_1128_;
v___y_1107_ = v___y_1127_;
v___y_1108_ = v___y_1126_;
v___y_1109_ = v___x_1138_;
goto v___jp_1102_;
}
}
else
{
size_t v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = lean_usize_of_nat(v___x_1133_);
v___x_1140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12(v___x_1007_, v___x_1121_, v___x_1120_, v___x_1139_, v___x_1134_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
lean_dec_ref(v___x_1121_);
v___y_1103_ = v___y_1123_;
v___y_1104_ = v___y_1124_;
v___y_1105_ = v___y_1125_;
v___y_1106_ = v___y_1128_;
v___y_1107_ = v___y_1127_;
v___y_1108_ = v___y_1126_;
v___y_1109_ = v___x_1140_;
goto v___jp_1102_;
}
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_dec_ref(v___y_1123_);
lean_dec_ref(v___x_1121_);
lean_dec_ref(v___x_1055_);
lean_dec(v___x_1006_);
v_a_1141_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1131_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1131_);
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
v___jp_1149_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
lean_dec_ref(v___y_1150_);
v___x_1157_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1158_ = l_Lean_MessageData_ofExpr(v___y_1155_);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1159_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v___x_1162_ = l_Lean_MessageData_ofConstName(v___x_1006_, v___x_1007_);
v___x_1163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1161_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___x_1164_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1163_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
v___x_1166_ = l_Lean_MessageData_ofExpr(v_e_1008_);
v___x_1167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1165_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_1169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1167_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1169_, v___y_1156_, v___y_1153_, v___y_1154_, v___y_1152_);
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1170_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1170_);
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
v___jp_1179_:
{
lean_object* v___x_1183_; 
lean_inc_ref(v_fst_1181_);
lean_inc_ref(v_e_1008_);
v___x_1183_ = l_Lean_Meta_isExprDefEq(v_e_1008_, v_fst_1181_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; uint8_t v___x_1185_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref(v___x_1183_);
v___x_1185_ = lean_unbox(v_a_1184_);
lean_dec(v_a_1184_);
if (v___x_1185_ == 0)
{
lean_dec_ref(v___x_1121_);
lean_dec_ref(v___x_1055_);
v___y_1150_ = v_snd_1182_;
v___y_1151_ = v_fst_1180_;
v___y_1152_ = v___y_1014_;
v___y_1153_ = v___y_1012_;
v___y_1154_ = v___y_1013_;
v___y_1155_ = v_fst_1181_;
v___y_1156_ = v___y_1011_;
goto v___jp_1149_;
}
else
{
if (v___x_1007_ == 0)
{
lean_dec_ref(v_fst_1181_);
lean_dec_ref(v_e_1008_);
v___y_1123_ = v_snd_1182_;
v___y_1124_ = v_fst_1180_;
v___y_1125_ = v___y_1011_;
v___y_1126_ = v___y_1012_;
v___y_1127_ = v___y_1013_;
v___y_1128_ = v___y_1014_;
goto v___jp_1122_;
}
else
{
lean_dec_ref(v___x_1121_);
lean_dec_ref(v___x_1055_);
v___y_1150_ = v_snd_1182_;
v___y_1151_ = v_fst_1180_;
v___y_1152_ = v___y_1014_;
v___y_1153_ = v___y_1012_;
v___y_1154_ = v___y_1013_;
v___y_1155_ = v_fst_1181_;
v___y_1156_ = v___y_1011_;
goto v___jp_1149_;
}
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_dec_ref(v_snd_1182_);
lean_dec_ref(v_fst_1181_);
lean_dec_ref(v___x_1121_);
lean_dec_ref(v___x_1055_);
lean_dec_ref(v_e_1008_);
lean_dec(v___x_1006_);
v_a_1186_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1183_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1183_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2___boxed(lean_object* v___x_1221_, lean_object* v___x_1222_, lean_object* v_fst_1223_, lean_object* v___x_1224_, lean_object* v___x_1225_, lean_object* v_e_1226_, lean_object* v_snd_1227_, lean_object* v_____r_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
uint8_t v___x_108338__boxed_1234_; uint8_t v___x_108342__boxed_1235_; lean_object* v_res_1236_; 
v___x_108338__boxed_1234_ = lean_unbox(v___x_1221_);
v___x_108342__boxed_1235_ = lean_unbox(v___x_1225_);
v_res_1236_ = l_Lean_Meta_rwMatcher___lam__2(v___x_108338__boxed_1234_, v___x_1222_, v_fst_1223_, v___x_1224_, v___x_108342__boxed_1235_, v_e_1226_, v_snd_1227_, v_____r_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec_ref(v_snd_1227_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(uint8_t v___x_1237_, lean_object* v_as_1238_, size_t v_i_1239_, size_t v_stop_1240_, lean_object* v_b_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v_a_1248_; uint8_t v___x_1252_; 
v___x_1252_ = lean_usize_dec_eq(v_i_1239_, v_stop_1240_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; uint8_t v_a_1255_; lean_object* v___x_1257_; 
v___x_1253_ = lean_array_uget_borrowed(v_as_1238_, v_i_1239_);
v___x_1257_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v___x_1253_, v___y_1243_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; uint8_t v___x_1259_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_a_1258_);
lean_dec_ref(v___x_1257_);
v___x_1259_ = lean_unbox(v_a_1258_);
lean_dec(v_a_1258_);
if (v___x_1259_ == 0)
{
v_a_1255_ = v___x_1237_;
goto v___jp_1254_;
}
else
{
v_a_1248_ = v_b_1241_;
goto v___jp_1247_;
}
}
else
{
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1260_; uint8_t v___x_1261_; 
v_a_1260_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_a_1260_);
lean_dec_ref(v___x_1257_);
v___x_1261_ = lean_unbox(v_a_1260_);
lean_dec(v_a_1260_);
v_a_1255_ = v___x_1261_;
goto v___jp_1254_;
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec_ref(v_b_1241_);
v_a_1262_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1257_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1257_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
v___jp_1254_:
{
if (v_a_1255_ == 0)
{
v_a_1248_ = v_b_1241_;
goto v___jp_1247_;
}
else
{
lean_object* v___x_1256_; 
lean_inc(v___x_1253_);
v___x_1256_ = lean_array_push(v_b_1241_, v___x_1253_);
v_a_1248_ = v___x_1256_;
goto v___jp_1247_;
}
}
}
else
{
lean_object* v___x_1270_; 
v___x_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1270_, 0, v_b_1241_);
return v___x_1270_;
}
v___jp_1247_:
{
size_t v___x_1249_; size_t v___x_1250_; 
v___x_1249_ = ((size_t)1ULL);
v___x_1250_ = lean_usize_add(v_i_1239_, v___x_1249_);
v_i_1239_ = v___x_1250_;
v_b_1241_ = v_a_1248_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13___boxed(lean_object* v___x_1271_, lean_object* v_as_1272_, lean_object* v_i_1273_, lean_object* v_stop_1274_, lean_object* v_b_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
uint8_t v___x_108823__boxed_1281_; size_t v_i_boxed_1282_; size_t v_stop_boxed_1283_; lean_object* v_res_1284_; 
v___x_108823__boxed_1281_ = lean_unbox(v___x_1271_);
v_i_boxed_1282_ = lean_unbox_usize(v_i_1273_);
lean_dec(v_i_1273_);
v_stop_boxed_1283_ = lean_unbox_usize(v_stop_1274_);
lean_dec(v_stop_1274_);
v_res_1284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(v___x_108823__boxed_1281_, v_as_1272_, v_i_boxed_1282_, v_stop_boxed_1283_, v_b_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec_ref(v_as_1272_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3(uint8_t v___x_1285_, lean_object* v___x_1286_, lean_object* v_fst_1287_, lean_object* v___x_1288_, uint8_t v___x_1289_, lean_object* v_e_1290_, uint8_t v___y_1291_, lean_object* v_snd_1292_, lean_object* v_____r_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v___y_1300_; lean_object* v_proof_1301_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; uint8_t v___y_1326_; lean_object* v___x_1338_; uint8_t v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1356_; uint8_t v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v_a_1362_; lean_object* v___y_1386_; lean_object* v___y_1387_; uint8_t v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; size_t v_sz_1402_; size_t v___x_1403_; lean_object* v___x_1404_; uint8_t v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; uint8_t v_fst_1433_; lean_object* v_fst_1434_; lean_object* v_snd_1435_; lean_object* v___x_1469_; lean_object* v___x_1470_; uint8_t v___x_1471_; 
v___x_1338_ = l_Lean_mkAppN(v___x_1286_, v_fst_1287_);
v_sz_1402_ = lean_array_size(v_fst_1287_);
v___x_1403_ = ((size_t)0ULL);
v___x_1404_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_1402_, v___x_1403_, v_fst_1287_);
v___x_1469_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1470_ = lean_unsigned_to_nat(4u);
v___x_1471_ = l_Lean_Expr_isAppOfArity(v_snd_1292_, v___x_1469_, v___x_1470_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1473_; uint8_t v___x_1474_; 
v___x_1472_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1473_ = lean_unsigned_to_nat(3u);
v___x_1474_ = l_Lean_Expr_isAppOfArity(v_snd_1292_, v___x_1472_, v___x_1473_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec_ref(v___x_1404_);
lean_dec_ref(v___x_1338_);
lean_dec_ref(v_e_1290_);
v___x_1475_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1476_ = l_Lean_MessageData_ofConstName(v___x_1288_, v___x_1474_);
v___x_1477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1475_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
v___x_1478_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1477_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
v___x_1480_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1479_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
else
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1489_ = l_Lean_Expr_appFn_x21(v_snd_1292_);
v___x_1490_ = l_Lean_Expr_appArg_x21(v___x_1489_);
lean_dec_ref(v___x_1489_);
v___x_1491_ = l_Lean_Expr_appArg_x21(v_snd_1292_);
v_fst_1433_ = v___x_1471_;
v_fst_1434_ = v___x_1490_;
v_snd_1435_ = v___x_1491_;
goto v___jp_1432_;
}
}
else
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1492_ = l_Lean_Expr_appFn_x21(v_snd_1292_);
v___x_1493_ = l_Lean_Expr_appFn_x21(v___x_1492_);
lean_dec_ref(v___x_1492_);
v___x_1494_ = l_Lean_Expr_appArg_x21(v___x_1493_);
lean_dec_ref(v___x_1493_);
v___x_1495_ = l_Lean_Expr_appArg_x21(v_snd_1292_);
v_fst_1433_ = v___x_1285_;
v_fst_1434_ = v___x_1494_;
v_snd_1435_ = v___x_1495_;
goto v___jp_1432_;
}
v___jp_1299_:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1302_, 0, v_proof_1301_);
v___x_1303_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1303_, 0, v___y_1300_);
lean_ctor_set(v___x_1303_, 1, v___x_1302_);
lean_ctor_set_uint8(v___x_1303_, sizeof(void*)*2, v___x_1285_);
v___x_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
return v___x_1304_;
}
v___jp_1305_:
{
if (lean_obj_tag(v___y_1307_) == 0)
{
lean_object* v_a_1308_; 
v_a_1308_ = lean_ctor_get(v___y_1307_, 0);
lean_inc(v_a_1308_);
lean_dec_ref(v___y_1307_);
v___y_1300_ = v___y_1306_;
v_proof_1301_ = v_a_1308_;
goto v___jp_1299_;
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_dec_ref(v___y_1306_);
v_a_1309_ = lean_ctor_get(v___y_1307_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___y_1307_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___y_1307_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___y_1307_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
v___jp_1317_:
{
if (v___y_1326_ == 0)
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
lean_dec_ref(v___y_1320_);
v___x_1327_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1328_ = l_Lean_MessageData_ofExpr(v___y_1323_);
v___x_1329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1327_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
v___x_1330_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1329_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
v___x_1332_ = l_Lean_Exception_toMessageData(v___y_1319_);
v___x_1333_ = l_Lean_indentD(v___x_1332_);
v___x_1334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1331_);
lean_ctor_set(v___x_1334_, 1, v___x_1333_);
v___x_1335_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1334_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
v___x_1337_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1336_, v___y_1321_, v___y_1322_, v___y_1325_, v___y_1318_);
v___y_1306_ = v___y_1324_;
v___y_1307_ = v___x_1337_;
goto v___jp_1305_;
}
else
{
lean_dec_ref(v___y_1323_);
lean_dec_ref(v___y_1319_);
v___y_1306_ = v___y_1324_;
v___y_1307_ = v___y_1320_;
goto v___jp_1305_;
}
}
v___jp_1339_:
{
lean_object* v___x_1346_; lean_object* v_a_1347_; lean_object* v___x_1348_; 
v___x_1346_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_1341_, v___y_1343_);
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_a_1347_);
lean_dec_ref(v___x_1346_);
v___x_1348_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___x_1338_, v___y_1343_);
if (v___y_1340_ == 0)
{
lean_object* v_a_1349_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1349_);
lean_dec_ref(v___x_1348_);
v___y_1300_ = v_a_1347_;
v_proof_1301_ = v_a_1349_;
goto v___jp_1299_;
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1351_; 
v_a_1350_ = lean_ctor_get(v___x_1348_, 0);
lean_inc_n(v_a_1350_, 2);
lean_dec_ref(v___x_1348_);
v___x_1351_ = l_Lean_Meta_mkEqOfHEq(v_a_1350_, v___x_1285_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_dec(v_a_1350_);
v___y_1306_ = v_a_1347_;
v___y_1307_ = v___x_1351_;
goto v___jp_1305_;
}
else
{
lean_object* v_a_1352_; uint8_t v___x_1353_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1352_);
v___x_1353_ = l_Lean_Exception_isInterrupt(v_a_1352_);
if (v___x_1353_ == 0)
{
uint8_t v___x_1354_; 
lean_inc(v_a_1352_);
v___x_1354_ = l_Lean_Exception_isRuntime(v_a_1352_);
v___y_1318_ = v___y_1345_;
v___y_1319_ = v_a_1352_;
v___y_1320_ = v___x_1351_;
v___y_1321_ = v___y_1342_;
v___y_1322_ = v___y_1343_;
v___y_1323_ = v_a_1350_;
v___y_1324_ = v_a_1347_;
v___y_1325_ = v___y_1344_;
v___y_1326_ = v___x_1354_;
goto v___jp_1317_;
}
else
{
v___y_1318_ = v___y_1345_;
v___y_1319_ = v_a_1352_;
v___y_1320_ = v___x_1351_;
v___y_1321_ = v___y_1342_;
v___y_1322_ = v___y_1343_;
v___y_1323_ = v_a_1350_;
v___y_1324_ = v_a_1347_;
v___y_1325_ = v___y_1344_;
v___y_1326_ = v___x_1353_;
goto v___jp_1317_;
}
}
}
}
v___jp_1355_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v___x_1363_ = lean_array_get_size(v_a_1362_);
v___x_1364_ = lean_unsigned_to_nat(0u);
v___x_1365_ = lean_nat_dec_eq(v___x_1363_, v___x_1364_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec_ref(v___y_1361_);
lean_dec_ref(v___x_1338_);
v___x_1366_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1367_ = l_Lean_MessageData_ofConstName(v___x_1288_, v___x_1365_);
v___x_1368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1366_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
v___x_1369_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1368_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
v___x_1371_ = lean_array_to_list(v_a_1362_);
v___x_1372_ = lean_box(0);
v___x_1373_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_1371_, v___x_1372_);
v___x_1374_ = l_Lean_MessageData_ofList(v___x_1373_);
v___x_1375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1370_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
v___x_1376_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1375_, v___y_1359_, v___y_1356_, v___y_1358_, v___y_1360_);
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1376_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1376_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
else
{
lean_dec_ref(v_a_1362_);
lean_dec(v___x_1288_);
v___y_1340_ = v___y_1357_;
v___y_1341_ = v___y_1361_;
v___y_1342_ = v___y_1359_;
v___y_1343_ = v___y_1356_;
v___y_1344_ = v___y_1358_;
v___y_1345_ = v___y_1360_;
goto v___jp_1339_;
}
}
v___jp_1385_:
{
if (lean_obj_tag(v___y_1392_) == 0)
{
lean_object* v_a_1393_; 
v_a_1393_ = lean_ctor_get(v___y_1392_, 0);
lean_inc(v_a_1393_);
lean_dec_ref(v___y_1392_);
v___y_1356_ = v___y_1386_;
v___y_1357_ = v___y_1388_;
v___y_1358_ = v___y_1387_;
v___y_1359_ = v___y_1389_;
v___y_1360_ = v___y_1390_;
v___y_1361_ = v___y_1391_;
v_a_1362_ = v_a_1393_;
goto v___jp_1355_;
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_dec_ref(v___y_1391_);
lean_dec_ref(v___x_1338_);
lean_dec(v___x_1288_);
v_a_1394_ = lean_ctor_get(v___y_1392_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___y_1392_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___y_1392_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___y_1392_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
v___jp_1405_:
{
lean_object* v___x_1412_; size_t v_sz_1413_; lean_object* v___x_1414_; 
v___x_1412_ = lean_box(0);
v_sz_1413_ = lean_array_size(v___x_1404_);
v___x_1414_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1404_, v_sz_1413_, v___x_1403_, v___x_1412_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
lean_dec_ref(v___x_1414_);
v___x_1415_ = lean_unsigned_to_nat(0u);
v___x_1416_ = lean_array_get_size(v___x_1404_);
v___x_1417_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1418_ = lean_nat_dec_lt(v___x_1415_, v___x_1416_);
if (v___x_1418_ == 0)
{
lean_dec_ref(v___x_1404_);
v___y_1356_ = v___y_1409_;
v___y_1357_ = v___y_1406_;
v___y_1358_ = v___y_1410_;
v___y_1359_ = v___y_1408_;
v___y_1360_ = v___y_1411_;
v___y_1361_ = v___y_1407_;
v_a_1362_ = v___x_1417_;
goto v___jp_1355_;
}
else
{
uint8_t v___x_1419_; 
v___x_1419_ = lean_nat_dec_le(v___x_1416_, v___x_1416_);
if (v___x_1419_ == 0)
{
if (v___x_1418_ == 0)
{
lean_dec_ref(v___x_1404_);
v___y_1356_ = v___y_1409_;
v___y_1357_ = v___y_1406_;
v___y_1358_ = v___y_1410_;
v___y_1359_ = v___y_1408_;
v___y_1360_ = v___y_1411_;
v___y_1361_ = v___y_1407_;
v_a_1362_ = v___x_1417_;
goto v___jp_1355_;
}
else
{
size_t v___x_1420_; lean_object* v___x_1421_; 
v___x_1420_ = lean_usize_of_nat(v___x_1416_);
v___x_1421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(v___x_1289_, v___x_1404_, v___x_1403_, v___x_1420_, v___x_1417_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
lean_dec_ref(v___x_1404_);
v___y_1386_ = v___y_1409_;
v___y_1387_ = v___y_1410_;
v___y_1388_ = v___y_1406_;
v___y_1389_ = v___y_1408_;
v___y_1390_ = v___y_1411_;
v___y_1391_ = v___y_1407_;
v___y_1392_ = v___x_1421_;
goto v___jp_1385_;
}
}
else
{
size_t v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = lean_usize_of_nat(v___x_1416_);
v___x_1423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(v___x_1289_, v___x_1404_, v___x_1403_, v___x_1422_, v___x_1417_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
lean_dec_ref(v___x_1404_);
v___y_1386_ = v___y_1409_;
v___y_1387_ = v___y_1410_;
v___y_1388_ = v___y_1406_;
v___y_1389_ = v___y_1408_;
v___y_1390_ = v___y_1411_;
v___y_1391_ = v___y_1407_;
v___y_1392_ = v___x_1423_;
goto v___jp_1385_;
}
}
}
else
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
lean_dec_ref(v___y_1407_);
lean_dec_ref(v___x_1404_);
lean_dec_ref(v___x_1338_);
lean_dec(v___x_1288_);
v_a_1424_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1414_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1414_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
v___jp_1432_:
{
lean_object* v___x_1436_; 
lean_inc_ref(v_fst_1434_);
lean_inc_ref(v_e_1290_);
v___x_1436_ = l_Lean_Meta_isExprDefEq(v_e_1290_, v_fst_1434_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; uint8_t v___x_1438_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
lean_inc(v_a_1437_);
lean_dec_ref(v___x_1436_);
v___x_1438_ = lean_unbox(v_a_1437_);
lean_dec(v_a_1437_);
if (v___x_1438_ == 0)
{
if (v___x_1289_ == 0)
{
lean_dec_ref(v_fst_1434_);
lean_dec_ref(v_e_1290_);
v___y_1406_ = v_fst_1433_;
v___y_1407_ = v_snd_1435_;
v___y_1408_ = v___y_1294_;
v___y_1409_ = v___y_1295_;
v___y_1410_ = v___y_1296_;
v___y_1411_ = v___y_1297_;
goto v___jp_1405_;
}
else
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
lean_dec_ref(v_snd_1435_);
lean_dec_ref(v___x_1404_);
lean_dec_ref(v___x_1338_);
v___x_1439_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1440_ = l_Lean_MessageData_ofExpr(v_fst_1434_);
v___x_1441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1439_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
v___x_1442_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1441_);
lean_ctor_set(v___x_1443_, 1, v___x_1442_);
v___x_1444_ = l_Lean_MessageData_ofConstName(v___x_1288_, v___y_1291_);
v___x_1445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1443_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
v___x_1446_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1445_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
v___x_1448_ = l_Lean_MessageData_ofExpr(v_e_1290_);
v___x_1449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1447_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_1451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1449_);
lean_ctor_set(v___x_1451_, 1, v___x_1450_);
v___x_1452_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1451_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1452_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1452_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1453_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
else
{
lean_dec_ref(v_fst_1434_);
lean_dec_ref(v_e_1290_);
v___y_1406_ = v_fst_1433_;
v___y_1407_ = v_snd_1435_;
v___y_1408_ = v___y_1294_;
v___y_1409_ = v___y_1295_;
v___y_1410_ = v___y_1296_;
v___y_1411_ = v___y_1297_;
goto v___jp_1405_;
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
lean_dec_ref(v_snd_1435_);
lean_dec_ref(v_fst_1434_);
lean_dec_ref(v___x_1404_);
lean_dec_ref(v___x_1338_);
lean_dec_ref(v_e_1290_);
lean_dec(v___x_1288_);
v_a_1461_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1436_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1436_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3___boxed(lean_object* v___x_1496_, lean_object* v___x_1497_, lean_object* v_fst_1498_, lean_object* v___x_1499_, lean_object* v___x_1500_, lean_object* v_e_1501_, lean_object* v___y_1502_, lean_object* v_snd_1503_, lean_object* v_____r_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
uint8_t v___x_108930__boxed_1510_; uint8_t v___x_108934__boxed_1511_; uint8_t v___y_108935__boxed_1512_; lean_object* v_res_1513_; 
v___x_108930__boxed_1510_ = lean_unbox(v___x_1496_);
v___x_108934__boxed_1511_ = lean_unbox(v___x_1500_);
v___y_108935__boxed_1512_ = lean_unbox(v___y_1502_);
v_res_1513_ = l_Lean_Meta_rwMatcher___lam__3(v___x_108930__boxed_1510_, v___x_1497_, v_fst_1498_, v___x_1499_, v___x_108934__boxed_1511_, v_e_1501_, v___y_108935__boxed_1512_, v_snd_1503_, v_____r_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec_ref(v_snd_1503_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4(uint8_t v___x_1514_, lean_object* v___x_1515_, lean_object* v_fst_1516_, lean_object* v___x_1517_, uint8_t v___x_1518_, lean_object* v_e_1519_, lean_object* v_snd_1520_, lean_object* v_____r_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v___y_1528_; lean_object* v_proof_1529_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; uint8_t v___y_1554_; lean_object* v___x_1566_; uint8_t v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; uint8_t v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v_a_1590_; lean_object* v___y_1614_; uint8_t v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; size_t v_sz_1630_; size_t v___x_1631_; lean_object* v___x_1632_; uint8_t v___y_1634_; lean_object* v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1661_; uint8_t v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; uint8_t v_fst_1691_; lean_object* v_fst_1692_; lean_object* v_snd_1693_; lean_object* v___x_1705_; lean_object* v___x_1706_; uint8_t v___x_1707_; 
v___x_1566_ = l_Lean_mkAppN(v___x_1515_, v_fst_1516_);
v_sz_1630_ = lean_array_size(v_fst_1516_);
v___x_1631_ = ((size_t)0ULL);
v___x_1632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_1630_, v___x_1631_, v_fst_1516_);
v___x_1705_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1706_ = lean_unsigned_to_nat(4u);
v___x_1707_ = l_Lean_Expr_isAppOfArity(v_snd_1520_, v___x_1705_, v___x_1706_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; lean_object* v___x_1709_; uint8_t v___x_1710_; 
v___x_1708_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1709_ = lean_unsigned_to_nat(3u);
v___x_1710_ = l_Lean_Expr_isAppOfArity(v_snd_1520_, v___x_1708_, v___x_1709_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
lean_dec_ref(v___x_1632_);
lean_dec_ref(v___x_1566_);
lean_dec_ref(v_e_1519_);
v___x_1711_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1712_ = l_Lean_MessageData_ofConstName(v___x_1517_, v___x_1518_);
v___x_1713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1711_);
lean_ctor_set(v___x_1713_, 1, v___x_1712_);
v___x_1714_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1713_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
v___x_1716_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1715_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1716_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1716_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
else
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = l_Lean_Expr_appFn_x21(v_snd_1520_);
v___x_1726_ = l_Lean_Expr_appArg_x21(v___x_1725_);
lean_dec_ref(v___x_1725_);
v___x_1727_ = l_Lean_Expr_appArg_x21(v_snd_1520_);
v_fst_1691_ = v___x_1518_;
v_fst_1692_ = v___x_1726_;
v_snd_1693_ = v___x_1727_;
goto v___jp_1690_;
}
}
else
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1728_ = l_Lean_Expr_appFn_x21(v_snd_1520_);
v___x_1729_ = l_Lean_Expr_appFn_x21(v___x_1728_);
lean_dec_ref(v___x_1728_);
v___x_1730_ = l_Lean_Expr_appArg_x21(v___x_1729_);
lean_dec_ref(v___x_1729_);
v___x_1731_ = l_Lean_Expr_appArg_x21(v_snd_1520_);
v_fst_1691_ = v___x_1514_;
v_fst_1692_ = v___x_1730_;
v_snd_1693_ = v___x_1731_;
goto v___jp_1690_;
}
v___jp_1527_:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1530_, 0, v_proof_1529_);
v___x_1531_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1531_, 0, v___y_1528_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
lean_ctor_set_uint8(v___x_1531_, sizeof(void*)*2, v___x_1514_);
v___x_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
return v___x_1532_;
}
v___jp_1533_:
{
if (lean_obj_tag(v___y_1535_) == 0)
{
lean_object* v_a_1536_; 
v_a_1536_ = lean_ctor_get(v___y_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref(v___y_1535_);
v___y_1528_ = v___y_1534_;
v_proof_1529_ = v_a_1536_;
goto v___jp_1527_;
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
lean_dec_ref(v___y_1534_);
v_a_1537_ = lean_ctor_get(v___y_1535_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___y_1535_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___y_1535_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___y_1535_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
v___jp_1545_:
{
if (v___y_1554_ == 0)
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
lean_dec_ref(v___y_1552_);
v___x_1555_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1556_ = l_Lean_MessageData_ofExpr(v___y_1546_);
v___x_1557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = l_Lean_Exception_toMessageData(v___y_1553_);
v___x_1561_ = l_Lean_indentD(v___x_1560_);
v___x_1562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1559_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
v___x_1563_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1562_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
v___x_1565_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1564_, v___y_1551_, v___y_1548_, v___y_1550_, v___y_1549_);
v___y_1534_ = v___y_1547_;
v___y_1535_ = v___x_1565_;
goto v___jp_1533_;
}
else
{
lean_dec_ref(v___y_1553_);
lean_dec_ref(v___y_1546_);
v___y_1534_ = v___y_1547_;
v___y_1535_ = v___y_1552_;
goto v___jp_1533_;
}
}
v___jp_1567_:
{
lean_object* v___x_1574_; lean_object* v_a_1575_; lean_object* v___x_1576_; 
v___x_1574_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_1569_, v___y_1571_);
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1575_);
lean_dec_ref(v___x_1574_);
v___x_1576_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___x_1566_, v___y_1571_);
if (v___y_1568_ == 0)
{
lean_object* v_a_1577_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1577_);
lean_dec_ref(v___x_1576_);
v___y_1528_ = v_a_1575_;
v_proof_1529_ = v_a_1577_;
goto v___jp_1527_;
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1579_; 
v_a_1578_ = lean_ctor_get(v___x_1576_, 0);
lean_inc_n(v_a_1578_, 2);
lean_dec_ref(v___x_1576_);
v___x_1579_ = l_Lean_Meta_mkEqOfHEq(v_a_1578_, v___x_1514_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_dec(v_a_1578_);
v___y_1534_ = v_a_1575_;
v___y_1535_ = v___x_1579_;
goto v___jp_1533_;
}
else
{
lean_object* v_a_1580_; uint8_t v___x_1581_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
v___x_1581_ = l_Lean_Exception_isInterrupt(v_a_1580_);
if (v___x_1581_ == 0)
{
uint8_t v___x_1582_; 
lean_inc(v_a_1580_);
v___x_1582_ = l_Lean_Exception_isRuntime(v_a_1580_);
v___y_1546_ = v_a_1578_;
v___y_1547_ = v_a_1575_;
v___y_1548_ = v___y_1571_;
v___y_1549_ = v___y_1573_;
v___y_1550_ = v___y_1572_;
v___y_1551_ = v___y_1570_;
v___y_1552_ = v___x_1579_;
v___y_1553_ = v_a_1580_;
v___y_1554_ = v___x_1582_;
goto v___jp_1545_;
}
else
{
v___y_1546_ = v_a_1578_;
v___y_1547_ = v_a_1575_;
v___y_1548_ = v___y_1571_;
v___y_1549_ = v___y_1573_;
v___y_1550_ = v___y_1572_;
v___y_1551_ = v___y_1570_;
v___y_1552_ = v___x_1579_;
v___y_1553_ = v_a_1580_;
v___y_1554_ = v___x_1581_;
goto v___jp_1545_;
}
}
}
}
v___jp_1583_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v___x_1591_ = lean_array_get_size(v_a_1590_);
v___x_1592_ = lean_unsigned_to_nat(0u);
v___x_1593_ = lean_nat_dec_eq(v___x_1591_, v___x_1592_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_dec_ref(v___y_1586_);
lean_dec_ref(v___x_1566_);
v___x_1594_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1595_ = l_Lean_MessageData_ofConstName(v___x_1517_, v___x_1518_);
v___x_1596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1594_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
v___x_1597_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1596_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
v___x_1599_ = lean_array_to_list(v_a_1590_);
v___x_1600_ = lean_box(0);
v___x_1601_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_1599_, v___x_1600_);
v___x_1602_ = l_Lean_MessageData_ofList(v___x_1601_);
v___x_1603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1598_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
v___x_1604_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1603_, v___y_1587_, v___y_1589_, v___y_1588_, v___y_1585_);
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1604_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1604_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
else
{
lean_dec_ref(v_a_1590_);
lean_dec(v___x_1517_);
v___y_1568_ = v___y_1584_;
v___y_1569_ = v___y_1586_;
v___y_1570_ = v___y_1587_;
v___y_1571_ = v___y_1589_;
v___y_1572_ = v___y_1588_;
v___y_1573_ = v___y_1585_;
goto v___jp_1567_;
}
}
v___jp_1613_:
{
if (lean_obj_tag(v___y_1620_) == 0)
{
lean_object* v_a_1621_; 
v_a_1621_ = lean_ctor_get(v___y_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref(v___y_1620_);
v___y_1584_ = v___y_1615_;
v___y_1585_ = v___y_1614_;
v___y_1586_ = v___y_1616_;
v___y_1587_ = v___y_1617_;
v___y_1588_ = v___y_1618_;
v___y_1589_ = v___y_1619_;
v_a_1590_ = v_a_1621_;
goto v___jp_1583_;
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec_ref(v___y_1616_);
lean_dec_ref(v___x_1566_);
lean_dec(v___x_1517_);
v_a_1622_ = lean_ctor_get(v___y_1620_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___y_1620_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___y_1620_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___y_1620_);
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
v___jp_1633_:
{
lean_object* v___x_1640_; size_t v_sz_1641_; lean_object* v___x_1642_; 
v___x_1640_ = lean_box(0);
v_sz_1641_ = lean_array_size(v___x_1632_);
v___x_1642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1632_, v_sz_1641_, v___x_1631_, v___x_1640_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; uint8_t v___x_1646_; 
lean_dec_ref(v___x_1642_);
v___x_1643_ = lean_unsigned_to_nat(0u);
v___x_1644_ = lean_array_get_size(v___x_1632_);
v___x_1645_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1646_ = lean_nat_dec_lt(v___x_1643_, v___x_1644_);
if (v___x_1646_ == 0)
{
lean_dec_ref(v___x_1632_);
v___y_1584_ = v___y_1634_;
v___y_1585_ = v___y_1639_;
v___y_1586_ = v___y_1635_;
v___y_1587_ = v___y_1636_;
v___y_1588_ = v___y_1638_;
v___y_1589_ = v___y_1637_;
v_a_1590_ = v___x_1645_;
goto v___jp_1583_;
}
else
{
uint8_t v___x_1647_; 
v___x_1647_ = lean_nat_dec_le(v___x_1644_, v___x_1644_);
if (v___x_1647_ == 0)
{
if (v___x_1646_ == 0)
{
lean_dec_ref(v___x_1632_);
v___y_1584_ = v___y_1634_;
v___y_1585_ = v___y_1639_;
v___y_1586_ = v___y_1635_;
v___y_1587_ = v___y_1636_;
v___y_1588_ = v___y_1638_;
v___y_1589_ = v___y_1637_;
v_a_1590_ = v___x_1645_;
goto v___jp_1583_;
}
else
{
size_t v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = lean_usize_of_nat(v___x_1644_);
v___x_1649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12(v___x_1518_, v___x_1632_, v___x_1631_, v___x_1648_, v___x_1645_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
lean_dec_ref(v___x_1632_);
v___y_1614_ = v___y_1639_;
v___y_1615_ = v___y_1634_;
v___y_1616_ = v___y_1635_;
v___y_1617_ = v___y_1636_;
v___y_1618_ = v___y_1638_;
v___y_1619_ = v___y_1637_;
v___y_1620_ = v___x_1649_;
goto v___jp_1613_;
}
}
else
{
size_t v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = lean_usize_of_nat(v___x_1644_);
v___x_1651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12(v___x_1518_, v___x_1632_, v___x_1631_, v___x_1650_, v___x_1645_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
lean_dec_ref(v___x_1632_);
v___y_1614_ = v___y_1639_;
v___y_1615_ = v___y_1634_;
v___y_1616_ = v___y_1635_;
v___y_1617_ = v___y_1636_;
v___y_1618_ = v___y_1638_;
v___y_1619_ = v___y_1637_;
v___y_1620_ = v___x_1651_;
goto v___jp_1613_;
}
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec_ref(v___y_1635_);
lean_dec_ref(v___x_1632_);
lean_dec_ref(v___x_1566_);
lean_dec(v___x_1517_);
v_a_1652_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1642_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1642_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
v___jp_1660_:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_dec_ref(v___y_1663_);
v___x_1668_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1669_ = l_Lean_MessageData_ofExpr(v___y_1665_);
v___x_1670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1668_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v___x_1671_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1670_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = l_Lean_MessageData_ofConstName(v___x_1517_, v___x_1518_);
v___x_1674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1672_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
v___x_1675_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1674_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = l_Lean_MessageData_ofExpr(v_e_1519_);
v___x_1678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1676_);
lean_ctor_set(v___x_1678_, 1, v___x_1677_);
v___x_1679_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_1680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1678_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
v___x_1681_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1680_, v___y_1661_, v___y_1664_, v___y_1666_, v___y_1667_);
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1681_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1681_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
v___jp_1690_:
{
lean_object* v___x_1694_; 
lean_inc_ref(v_fst_1692_);
lean_inc_ref(v_e_1519_);
v___x_1694_ = l_Lean_Meta_isExprDefEq(v_e_1519_, v_fst_1692_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; uint8_t v___x_1696_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1695_);
lean_dec_ref(v___x_1694_);
v___x_1696_ = lean_unbox(v_a_1695_);
lean_dec(v_a_1695_);
if (v___x_1696_ == 0)
{
lean_dec_ref(v___x_1632_);
lean_dec_ref(v___x_1566_);
v___y_1661_ = v___y_1522_;
v___y_1662_ = v_fst_1691_;
v___y_1663_ = v_snd_1693_;
v___y_1664_ = v___y_1523_;
v___y_1665_ = v_fst_1692_;
v___y_1666_ = v___y_1524_;
v___y_1667_ = v___y_1525_;
goto v___jp_1660_;
}
else
{
if (v___x_1518_ == 0)
{
lean_dec_ref(v_fst_1692_);
lean_dec_ref(v_e_1519_);
v___y_1634_ = v_fst_1691_;
v___y_1635_ = v_snd_1693_;
v___y_1636_ = v___y_1522_;
v___y_1637_ = v___y_1523_;
v___y_1638_ = v___y_1524_;
v___y_1639_ = v___y_1525_;
goto v___jp_1633_;
}
else
{
lean_dec_ref(v___x_1632_);
lean_dec_ref(v___x_1566_);
v___y_1661_ = v___y_1522_;
v___y_1662_ = v_fst_1691_;
v___y_1663_ = v_snd_1693_;
v___y_1664_ = v___y_1523_;
v___y_1665_ = v_fst_1692_;
v___y_1666_ = v___y_1524_;
v___y_1667_ = v___y_1525_;
goto v___jp_1660_;
}
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec_ref(v_snd_1693_);
lean_dec_ref(v_fst_1692_);
lean_dec_ref(v___x_1632_);
lean_dec_ref(v___x_1566_);
lean_dec_ref(v_e_1519_);
lean_dec(v___x_1517_);
v_a_1697_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1694_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1694_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4___boxed(lean_object* v___x_1732_, lean_object* v___x_1733_, lean_object* v_fst_1734_, lean_object* v___x_1735_, lean_object* v___x_1736_, lean_object* v_e_1737_, lean_object* v_snd_1738_, lean_object* v_____r_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
uint8_t v___x_109418__boxed_1745_; uint8_t v___x_109422__boxed_1746_; lean_object* v_res_1747_; 
v___x_109418__boxed_1745_ = lean_unbox(v___x_1732_);
v___x_109422__boxed_1746_ = lean_unbox(v___x_1736_);
v_res_1747_ = l_Lean_Meta_rwMatcher___lam__4(v___x_109418__boxed_1745_, v___x_1733_, v_fst_1734_, v___x_1735_, v___x_109422__boxed_1746_, v_e_1737_, v_snd_1738_, v_____r_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec_ref(v_snd_1738_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_rwMatcher_spec__14(lean_object* v_b_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_Meta_reduceRecMatcher_x3f(v_b_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1768_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1757_ = v___x_1754_;
v_isShared_1758_ = v_isSharedCheck_1768_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1754_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1768_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
if (lean_obj_tag(v_a_1755_) == 1)
{
lean_object* v_val_1759_; lean_object* v___x_1760_; 
lean_del_object(v___x_1757_);
lean_dec_ref(v_b_1748_);
v_val_1759_ = lean_ctor_get(v_a_1755_, 0);
lean_inc(v_val_1759_);
lean_dec_ref(v_a_1755_);
v___x_1760_ = l_Lean_Expr_headBeta(v_val_1759_);
v_b_1748_ = v___x_1760_;
goto _start;
}
else
{
lean_object* v___x_1762_; uint8_t v___x_1763_; 
lean_dec(v_a_1755_);
lean_inc_ref(v_b_1748_);
v___x_1762_ = l_Lean_Expr_headBeta(v_b_1748_);
v___x_1763_ = lean_expr_eqv(v_b_1748_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_del_object(v___x_1757_);
lean_dec_ref(v_b_1748_);
v_b_1748_ = v___x_1762_;
goto _start;
}
else
{
lean_object* v___x_1766_; 
lean_dec_ref(v___x_1762_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 0, v_b_1748_);
v___x_1766_ = v___x_1757_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_b_1748_);
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
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_dec_ref(v_b_1748_);
v_a_1769_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1754_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1754_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_rwMatcher_spec__14___boxed(lean_object* v_b_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_rwMatcher_spec__14(v_b_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
return v_res_1783_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1784_; double v___x_1785_; 
v___x_1784_ = lean_unsigned_to_nat(0u);
v___x_1785_ = lean_float_of_nat(v___x_1784_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(lean_object* v_cls_1789_, lean_object* v_msg_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v_ref_1796_; lean_object* v___x_1797_; lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1842_; 
v_ref_1796_ = lean_ctor_get(v___y_1793_, 5);
v___x_1797_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1842_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1842_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; lean_object* v_traceState_1803_; lean_object* v_env_1804_; lean_object* v_nextMacroScope_1805_; lean_object* v_ngen_1806_; lean_object* v_auxDeclNGen_1807_; lean_object* v_cache_1808_; lean_object* v_messages_1809_; lean_object* v_infoState_1810_; lean_object* v_snapshotTasks_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1841_; 
v___x_1802_ = lean_st_ref_take(v___y_1794_);
v_traceState_1803_ = lean_ctor_get(v___x_1802_, 4);
v_env_1804_ = lean_ctor_get(v___x_1802_, 0);
v_nextMacroScope_1805_ = lean_ctor_get(v___x_1802_, 1);
v_ngen_1806_ = lean_ctor_get(v___x_1802_, 2);
v_auxDeclNGen_1807_ = lean_ctor_get(v___x_1802_, 3);
v_cache_1808_ = lean_ctor_get(v___x_1802_, 5);
v_messages_1809_ = lean_ctor_get(v___x_1802_, 6);
v_infoState_1810_ = lean_ctor_get(v___x_1802_, 7);
v_snapshotTasks_1811_ = lean_ctor_get(v___x_1802_, 8);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1813_ = v___x_1802_;
v_isShared_1814_ = v_isSharedCheck_1841_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_snapshotTasks_1811_);
lean_inc(v_infoState_1810_);
lean_inc(v_messages_1809_);
lean_inc(v_cache_1808_);
lean_inc(v_traceState_1803_);
lean_inc(v_auxDeclNGen_1807_);
lean_inc(v_ngen_1806_);
lean_inc(v_nextMacroScope_1805_);
lean_inc(v_env_1804_);
lean_dec(v___x_1802_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1841_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
uint64_t v_tid_1815_; lean_object* v_traces_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1840_; 
v_tid_1815_ = lean_ctor_get_uint64(v_traceState_1803_, sizeof(void*)*1);
v_traces_1816_ = lean_ctor_get(v_traceState_1803_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_traceState_1803_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1818_ = v_traceState_1803_;
v_isShared_1819_ = v_isSharedCheck_1840_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_traces_1816_);
lean_dec(v_traceState_1803_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1840_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1820_; double v___x_1821_; uint8_t v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1830_; 
v___x_1820_ = lean_box(0);
v___x_1821_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0);
v___x_1822_ = 0;
v___x_1823_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1));
v___x_1824_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1824_, 0, v_cls_1789_);
lean_ctor_set(v___x_1824_, 1, v___x_1820_);
lean_ctor_set(v___x_1824_, 2, v___x_1823_);
lean_ctor_set_float(v___x_1824_, sizeof(void*)*3, v___x_1821_);
lean_ctor_set_float(v___x_1824_, sizeof(void*)*3 + 8, v___x_1821_);
lean_ctor_set_uint8(v___x_1824_, sizeof(void*)*3 + 16, v___x_1822_);
v___x_1825_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__2));
v___x_1826_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1824_);
lean_ctor_set(v___x_1826_, 1, v_a_1798_);
lean_ctor_set(v___x_1826_, 2, v___x_1825_);
lean_inc(v_ref_1796_);
v___x_1827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1827_, 0, v_ref_1796_);
lean_ctor_set(v___x_1827_, 1, v___x_1826_);
v___x_1828_ = l_Lean_PersistentArray_push___redArg(v_traces_1816_, v___x_1827_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1828_);
v___x_1830_ = v___x_1818_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1828_);
lean_ctor_set_uint64(v_reuseFailAlloc_1839_, sizeof(void*)*1, v_tid_1815_);
v___x_1830_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1832_; 
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 4, v___x_1830_);
v___x_1832_ = v___x_1813_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_env_1804_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_nextMacroScope_1805_);
lean_ctor_set(v_reuseFailAlloc_1838_, 2, v_ngen_1806_);
lean_ctor_set(v_reuseFailAlloc_1838_, 3, v_auxDeclNGen_1807_);
lean_ctor_set(v_reuseFailAlloc_1838_, 4, v___x_1830_);
lean_ctor_set(v_reuseFailAlloc_1838_, 5, v_cache_1808_);
lean_ctor_set(v_reuseFailAlloc_1838_, 6, v_messages_1809_);
lean_ctor_set(v_reuseFailAlloc_1838_, 7, v_infoState_1810_);
lean_ctor_set(v_reuseFailAlloc_1838_, 8, v_snapshotTasks_1811_);
v___x_1832_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1836_; 
v___x_1833_ = lean_st_ref_set(v___y_1794_, v___x_1832_);
v___x_1834_ = lean_box(0);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1834_);
v___x_1836_ = v___x_1800_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1834_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___boxed(lean_object* v_cls_1843_, lean_object* v_msg_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v_cls_1843_, v_msg_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(lean_object* v_as_1851_, size_t v_i_1852_, size_t v_stop_1853_, lean_object* v_b_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v_a_1861_; uint8_t v___x_1865_; 
v___x_1865_ = lean_usize_dec_eq(v_i_1852_, v_stop_1853_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; lean_object* v___x_1869_; 
v___x_1866_ = lean_array_uget_borrowed(v_as_1851_, v_i_1852_);
v___x_1869_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v___x_1866_, v___y_1856_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; uint8_t v___x_1871_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_a_1870_);
lean_dec_ref(v___x_1869_);
v___x_1871_ = lean_unbox(v_a_1870_);
lean_dec(v_a_1870_);
if (v___x_1871_ == 0)
{
goto v___jp_1867_;
}
else
{
v_a_1861_ = v_b_1854_;
goto v___jp_1860_;
}
}
else
{
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1872_; uint8_t v___x_1873_; 
v_a_1872_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_a_1872_);
lean_dec_ref(v___x_1869_);
v___x_1873_ = lean_unbox(v_a_1872_);
lean_dec(v_a_1872_);
if (v___x_1873_ == 0)
{
v_a_1861_ = v_b_1854_;
goto v___jp_1860_;
}
else
{
goto v___jp_1867_;
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_dec_ref(v_b_1854_);
v_a_1874_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1869_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1869_);
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
v___jp_1867_:
{
lean_object* v___x_1868_; 
lean_inc(v___x_1866_);
v___x_1868_ = lean_array_push(v_b_1854_, v___x_1866_);
v_a_1861_ = v___x_1868_;
goto v___jp_1860_;
}
}
else
{
lean_object* v___x_1882_; 
v___x_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1882_, 0, v_b_1854_);
return v___x_1882_;
}
v___jp_1860_:
{
size_t v___x_1862_; size_t v___x_1863_; 
v___x_1862_ = ((size_t)1ULL);
v___x_1863_ = lean_usize_add(v_i_1852_, v___x_1862_);
v_i_1852_ = v___x_1863_;
v_b_1854_ = v_a_1861_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8___boxed(lean_object* v_as_1883_, lean_object* v_i_1884_, lean_object* v_stop_1885_, lean_object* v_b_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
size_t v_i_boxed_1892_; size_t v_stop_boxed_1893_; lean_object* v_res_1894_; 
v_i_boxed_1892_ = lean_unbox_usize(v_i_1884_);
lean_dec(v_i_1884_);
v_stop_boxed_1893_ = lean_unbox_usize(v_stop_1885_);
lean_dec(v_stop_1885_);
v_res_1894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v_as_1883_, v_i_boxed_1892_, v_stop_boxed_1893_, v_b_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec_ref(v_as_1883_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14_spec__16(size_t v_sz_1895_, size_t v_i_1896_, lean_object* v_bs_1897_){
_start:
{
uint8_t v___x_1898_; 
v___x_1898_ = lean_usize_dec_lt(v_i_1896_, v_sz_1895_);
if (v___x_1898_ == 0)
{
return v_bs_1897_;
}
else
{
lean_object* v_v_1899_; lean_object* v_msg_1900_; lean_object* v___x_1901_; lean_object* v_bs_x27_1902_; size_t v___x_1903_; size_t v___x_1904_; lean_object* v___x_1905_; 
v_v_1899_ = lean_array_uget_borrowed(v_bs_1897_, v_i_1896_);
v_msg_1900_ = lean_ctor_get(v_v_1899_, 1);
lean_inc_ref(v_msg_1900_);
v___x_1901_ = lean_unsigned_to_nat(0u);
v_bs_x27_1902_ = lean_array_uset(v_bs_1897_, v_i_1896_, v___x_1901_);
v___x_1903_ = ((size_t)1ULL);
v___x_1904_ = lean_usize_add(v_i_1896_, v___x_1903_);
v___x_1905_ = lean_array_uset(v_bs_x27_1902_, v_i_1896_, v_msg_1900_);
v_i_1896_ = v___x_1904_;
v_bs_1897_ = v___x_1905_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14_spec__16___boxed(lean_object* v_sz_1907_, lean_object* v_i_1908_, lean_object* v_bs_1909_){
_start:
{
size_t v_sz_boxed_1910_; size_t v_i_boxed_1911_; lean_object* v_res_1912_; 
v_sz_boxed_1910_ = lean_unbox_usize(v_sz_1907_);
lean_dec(v_sz_1907_);
v_i_boxed_1911_ = lean_unbox_usize(v_i_1908_);
lean_dec(v_i_1908_);
v_res_1912_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14_spec__16(v_sz_boxed_1910_, v_i_boxed_1911_, v_bs_1909_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14(lean_object* v_oldTraces_1913_, lean_object* v_data_1914_, lean_object* v_ref_1915_, lean_object* v_msg_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v_fileName_1922_; lean_object* v_fileMap_1923_; lean_object* v_options_1924_; lean_object* v_currRecDepth_1925_; lean_object* v_maxRecDepth_1926_; lean_object* v_ref_1927_; lean_object* v_currNamespace_1928_; lean_object* v_openDecls_1929_; lean_object* v_initHeartbeats_1930_; lean_object* v_maxHeartbeats_1931_; lean_object* v_quotContext_1932_; lean_object* v_currMacroScope_1933_; uint8_t v_diag_1934_; lean_object* v_cancelTk_x3f_1935_; uint8_t v_suppressElabErrors_1936_; lean_object* v_inheritedTraceOptions_1937_; lean_object* v___x_1938_; lean_object* v_traceState_1939_; lean_object* v_traces_1940_; lean_object* v_ref_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; size_t v_sz_1944_; size_t v___x_1945_; lean_object* v___x_1946_; lean_object* v_msg_1947_; lean_object* v___x_1948_; lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1986_; 
v_fileName_1922_ = lean_ctor_get(v___y_1919_, 0);
v_fileMap_1923_ = lean_ctor_get(v___y_1919_, 1);
v_options_1924_ = lean_ctor_get(v___y_1919_, 2);
v_currRecDepth_1925_ = lean_ctor_get(v___y_1919_, 3);
v_maxRecDepth_1926_ = lean_ctor_get(v___y_1919_, 4);
v_ref_1927_ = lean_ctor_get(v___y_1919_, 5);
v_currNamespace_1928_ = lean_ctor_get(v___y_1919_, 6);
v_openDecls_1929_ = lean_ctor_get(v___y_1919_, 7);
v_initHeartbeats_1930_ = lean_ctor_get(v___y_1919_, 8);
v_maxHeartbeats_1931_ = lean_ctor_get(v___y_1919_, 9);
v_quotContext_1932_ = lean_ctor_get(v___y_1919_, 10);
v_currMacroScope_1933_ = lean_ctor_get(v___y_1919_, 11);
v_diag_1934_ = lean_ctor_get_uint8(v___y_1919_, sizeof(void*)*14);
v_cancelTk_x3f_1935_ = lean_ctor_get(v___y_1919_, 12);
v_suppressElabErrors_1936_ = lean_ctor_get_uint8(v___y_1919_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1937_ = lean_ctor_get(v___y_1919_, 13);
v___x_1938_ = lean_st_ref_get(v___y_1920_);
v_traceState_1939_ = lean_ctor_get(v___x_1938_, 4);
lean_inc_ref(v_traceState_1939_);
lean_dec(v___x_1938_);
v_traces_1940_ = lean_ctor_get(v_traceState_1939_, 0);
lean_inc_ref(v_traces_1940_);
lean_dec_ref(v_traceState_1939_);
v_ref_1941_ = l_Lean_replaceRef(v_ref_1915_, v_ref_1927_);
lean_inc_ref(v_inheritedTraceOptions_1937_);
lean_inc(v_cancelTk_x3f_1935_);
lean_inc(v_currMacroScope_1933_);
lean_inc(v_quotContext_1932_);
lean_inc(v_maxHeartbeats_1931_);
lean_inc(v_initHeartbeats_1930_);
lean_inc(v_openDecls_1929_);
lean_inc(v_currNamespace_1928_);
lean_inc(v_maxRecDepth_1926_);
lean_inc(v_currRecDepth_1925_);
lean_inc_ref(v_options_1924_);
lean_inc_ref(v_fileMap_1923_);
lean_inc_ref(v_fileName_1922_);
v___x_1942_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1942_, 0, v_fileName_1922_);
lean_ctor_set(v___x_1942_, 1, v_fileMap_1923_);
lean_ctor_set(v___x_1942_, 2, v_options_1924_);
lean_ctor_set(v___x_1942_, 3, v_currRecDepth_1925_);
lean_ctor_set(v___x_1942_, 4, v_maxRecDepth_1926_);
lean_ctor_set(v___x_1942_, 5, v_ref_1941_);
lean_ctor_set(v___x_1942_, 6, v_currNamespace_1928_);
lean_ctor_set(v___x_1942_, 7, v_openDecls_1929_);
lean_ctor_set(v___x_1942_, 8, v_initHeartbeats_1930_);
lean_ctor_set(v___x_1942_, 9, v_maxHeartbeats_1931_);
lean_ctor_set(v___x_1942_, 10, v_quotContext_1932_);
lean_ctor_set(v___x_1942_, 11, v_currMacroScope_1933_);
lean_ctor_set(v___x_1942_, 12, v_cancelTk_x3f_1935_);
lean_ctor_set(v___x_1942_, 13, v_inheritedTraceOptions_1937_);
lean_ctor_set_uint8(v___x_1942_, sizeof(void*)*14, v_diag_1934_);
lean_ctor_set_uint8(v___x_1942_, sizeof(void*)*14 + 1, v_suppressElabErrors_1936_);
v___x_1943_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1940_);
lean_dec_ref(v_traces_1940_);
v_sz_1944_ = lean_array_size(v___x_1943_);
v___x_1945_ = ((size_t)0ULL);
v___x_1946_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14_spec__16(v_sz_1944_, v___x_1945_, v___x_1943_);
v_msg_1947_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1947_, 0, v_data_1914_);
lean_ctor_set(v_msg_1947_, 1, v_msg_1916_);
lean_ctor_set(v_msg_1947_, 2, v___x_1946_);
v___x_1948_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_1947_, v___y_1917_, v___y_1918_, v___x_1942_, v___y_1920_);
lean_dec_ref(v___x_1942_);
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1951_ = v___x_1948_;
v_isShared_1952_ = v_isSharedCheck_1986_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1948_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1986_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1953_; lean_object* v_traceState_1954_; lean_object* v_env_1955_; lean_object* v_nextMacroScope_1956_; lean_object* v_ngen_1957_; lean_object* v_auxDeclNGen_1958_; lean_object* v_cache_1959_; lean_object* v_messages_1960_; lean_object* v_infoState_1961_; lean_object* v_snapshotTasks_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1985_; 
v___x_1953_ = lean_st_ref_take(v___y_1920_);
v_traceState_1954_ = lean_ctor_get(v___x_1953_, 4);
v_env_1955_ = lean_ctor_get(v___x_1953_, 0);
v_nextMacroScope_1956_ = lean_ctor_get(v___x_1953_, 1);
v_ngen_1957_ = lean_ctor_get(v___x_1953_, 2);
v_auxDeclNGen_1958_ = lean_ctor_get(v___x_1953_, 3);
v_cache_1959_ = lean_ctor_get(v___x_1953_, 5);
v_messages_1960_ = lean_ctor_get(v___x_1953_, 6);
v_infoState_1961_ = lean_ctor_get(v___x_1953_, 7);
v_snapshotTasks_1962_ = lean_ctor_get(v___x_1953_, 8);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1964_ = v___x_1953_;
v_isShared_1965_ = v_isSharedCheck_1985_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_snapshotTasks_1962_);
lean_inc(v_infoState_1961_);
lean_inc(v_messages_1960_);
lean_inc(v_cache_1959_);
lean_inc(v_traceState_1954_);
lean_inc(v_auxDeclNGen_1958_);
lean_inc(v_ngen_1957_);
lean_inc(v_nextMacroScope_1956_);
lean_inc(v_env_1955_);
lean_dec(v___x_1953_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1985_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
uint64_t v_tid_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1983_; 
v_tid_1966_ = lean_ctor_get_uint64(v_traceState_1954_, sizeof(void*)*1);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_traceState_1954_);
if (v_isSharedCheck_1983_ == 0)
{
lean_object* v_unused_1984_; 
v_unused_1984_ = lean_ctor_get(v_traceState_1954_, 0);
lean_dec(v_unused_1984_);
v___x_1968_ = v_traceState_1954_;
v_isShared_1969_ = v_isSharedCheck_1983_;
goto v_resetjp_1967_;
}
else
{
lean_dec(v_traceState_1954_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1983_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1973_; 
v___x_1970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1970_, 0, v_ref_1915_);
lean_ctor_set(v___x_1970_, 1, v_a_1949_);
v___x_1971_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1913_, v___x_1970_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v___x_1971_);
v___x_1973_ = v___x_1968_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1971_);
lean_ctor_set_uint64(v_reuseFailAlloc_1982_, sizeof(void*)*1, v_tid_1966_);
v___x_1973_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
lean_object* v___x_1975_; 
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 4, v___x_1973_);
v___x_1975_ = v___x_1964_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_env_1955_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v_nextMacroScope_1956_);
lean_ctor_set(v_reuseFailAlloc_1981_, 2, v_ngen_1957_);
lean_ctor_set(v_reuseFailAlloc_1981_, 3, v_auxDeclNGen_1958_);
lean_ctor_set(v_reuseFailAlloc_1981_, 4, v___x_1973_);
lean_ctor_set(v_reuseFailAlloc_1981_, 5, v_cache_1959_);
lean_ctor_set(v_reuseFailAlloc_1981_, 6, v_messages_1960_);
lean_ctor_set(v_reuseFailAlloc_1981_, 7, v_infoState_1961_);
lean_ctor_set(v_reuseFailAlloc_1981_, 8, v_snapshotTasks_1962_);
v___x_1975_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1976_ = lean_st_ref_set(v___y_1920_, v___x_1975_);
v___x_1977_ = lean_box(0);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v___x_1977_);
v___x_1979_ = v___x_1951_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1977_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___boxed(lean_object* v_oldTraces_1987_, lean_object* v_data_1988_, lean_object* v_ref_1989_, lean_object* v_msg_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14(v_oldTraces_1987_, v_data_1988_, v_ref_1989_, v_msg_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(lean_object* v_opts_1997_, lean_object* v_opt_1998_){
_start:
{
lean_object* v_name_1999_; lean_object* v_defValue_2000_; lean_object* v_map_2001_; lean_object* v___x_2002_; 
v_name_1999_ = lean_ctor_get(v_opt_1998_, 0);
v_defValue_2000_ = lean_ctor_get(v_opt_1998_, 1);
v_map_2001_ = lean_ctor_get(v_opts_1997_, 0);
v___x_2002_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2001_, v_name_1999_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_inc(v_defValue_2000_);
return v_defValue_2000_;
}
else
{
lean_object* v_val_2003_; 
v_val_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_val_2003_);
lean_dec_ref(v___x_2002_);
if (lean_obj_tag(v_val_2003_) == 3)
{
lean_object* v_v_2004_; 
v_v_2004_ = lean_ctor_get(v_val_2003_, 0);
lean_inc(v_v_2004_);
lean_dec_ref(v_val_2003_);
return v_v_2004_;
}
else
{
lean_dec(v_val_2003_);
lean_inc(v_defValue_2000_);
return v_defValue_2000_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16___boxed(lean_object* v_opts_2005_, lean_object* v_opt_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_2005_, v_opt_2006_);
lean_dec_ref(v_opt_2006_);
lean_dec_ref(v_opts_2005_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___redArg(lean_object* v_x_2008_){
_start:
{
if (lean_obj_tag(v_x_2008_) == 0)
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
v_a_2010_ = lean_ctor_get(v_x_2008_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_x_2008_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v_x_2008_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v_x_2008_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
lean_ctor_set_tag(v___x_2012_, 1);
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
v_a_2018_ = lean_ctor_get(v_x_2008_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v_x_2008_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v_x_2008_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v_x_2008_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
lean_ctor_set_tag(v___x_2020_, 0);
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___redArg___boxed(lean_object* v_x_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___redArg(v_x_2026_);
return v_res_2028_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(lean_object* v_e_2029_){
_start:
{
if (lean_obj_tag(v_e_2029_) == 0)
{
uint8_t v___x_2030_; 
v___x_2030_ = 2;
return v___x_2030_;
}
else
{
uint8_t v___x_2031_; 
v___x_2031_ = 0;
return v___x_2031_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13___boxed(lean_object* v_e_2032_){
_start:
{
uint8_t v_res_2033_; lean_object* v_r_2034_; 
v_res_2033_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(v_e_2032_);
lean_dec_ref(v_e_2032_);
v_r_2034_ = lean_box(v_res_2033_);
return v_r_2034_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1(void){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__0));
v___x_2037_ = l_Lean_stringToMessageData(v___x_2036_);
return v___x_2037_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2(void){
_start:
{
lean_object* v___x_2038_; double v___x_2039_; 
v___x_2038_ = lean_unsigned_to_nat(1000u);
v___x_2039_ = lean_float_of_nat(v___x_2038_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(lean_object* v_cls_2040_, uint8_t v_collapsed_2041_, lean_object* v_tag_2042_, lean_object* v_opts_2043_, uint8_t v_clsEnabled_2044_, lean_object* v_oldTraces_2045_, lean_object* v_msg_2046_, lean_object* v_resStartStop_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v_fst_2053_; lean_object* v_snd_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2152_; 
v_fst_2053_ = lean_ctor_get(v_resStartStop_2047_, 0);
v_snd_2054_ = lean_ctor_get(v_resStartStop_2047_, 1);
v_isSharedCheck_2152_ = !lean_is_exclusive(v_resStartStop_2047_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2056_ = v_resStartStop_2047_;
v_isShared_2057_ = v_isSharedCheck_2152_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_snd_2054_);
lean_inc(v_fst_2053_);
lean_dec(v_resStartStop_2047_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2152_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v_data_2061_; lean_object* v_fst_2072_; lean_object* v_snd_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2151_; 
v_fst_2072_ = lean_ctor_get(v_snd_2054_, 0);
v_snd_2073_ = lean_ctor_get(v_snd_2054_, 1);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_snd_2054_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2075_ = v_snd_2054_;
v_isShared_2076_ = v_isSharedCheck_2151_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_snd_2073_);
lean_inc(v_fst_2072_);
lean_dec(v_snd_2054_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2151_;
goto v_resetjp_2074_;
}
v___jp_2058_:
{
lean_object* v___x_2062_; 
lean_inc(v___y_2059_);
v___x_2062_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14(v_oldTraces_2045_, v_data_2061_, v___y_2059_, v___y_2060_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v___x_2063_; 
lean_dec_ref(v___x_2062_);
v___x_2063_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___redArg(v_fst_2053_);
return v___x_2063_;
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_dec(v_fst_2053_);
v_a_2064_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2062_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2062_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
v_resetjp_2074_:
{
lean_object* v___x_2077_; uint8_t v___x_2078_; lean_object* v___y_2080_; lean_object* v_a_2081_; uint8_t v___y_2105_; double v___y_2136_; 
v___x_2077_ = l_Lean_trace_profiler;
v___x_2078_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_opts_2043_, v___x_2077_);
if (v___x_2078_ == 0)
{
v___y_2105_ = v___x_2078_;
goto v___jp_2104_;
}
else
{
lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2141_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2142_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_opts_2043_, v___x_2141_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2144_; double v___x_2145_; double v___x_2146_; double v___x_2147_; 
v___x_2143_ = l_Lean_trace_profiler_threshold;
v___x_2144_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_2043_, v___x_2143_);
v___x_2145_ = lean_float_of_nat(v___x_2144_);
v___x_2146_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2);
v___x_2147_ = lean_float_div(v___x_2145_, v___x_2146_);
v___y_2136_ = v___x_2147_;
goto v___jp_2135_;
}
else
{
lean_object* v___x_2148_; lean_object* v___x_2149_; double v___x_2150_; 
v___x_2148_ = l_Lean_trace_profiler_threshold;
v___x_2149_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_2043_, v___x_2148_);
v___x_2150_ = lean_float_of_nat(v___x_2149_);
v___y_2136_ = v___x_2150_;
goto v___jp_2135_;
}
}
v___jp_2079_:
{
uint8_t v_result_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2087_; 
v_result_2082_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(v_fst_2053_);
v___x_2083_ = l_Lean_TraceResult_toEmoji(v_result_2082_);
v___x_2084_ = l_Lean_stringToMessageData(v___x_2083_);
v___x_2085_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
if (v_isShared_2076_ == 0)
{
lean_ctor_set_tag(v___x_2075_, 7);
lean_ctor_set(v___x_2075_, 1, v___x_2085_);
lean_ctor_set(v___x_2075_, 0, v___x_2084_);
v___x_2087_ = v___x_2075_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2084_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v___x_2085_);
v___x_2087_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
lean_object* v_m_2089_; 
if (v_isShared_2057_ == 0)
{
lean_ctor_set_tag(v___x_2056_, 7);
lean_ctor_set(v___x_2056_, 1, v_a_2081_);
lean_ctor_set(v___x_2056_, 0, v___x_2087_);
v_m_2089_ = v___x_2056_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_2087_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_a_2081_);
v_m_2089_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; double v___x_2092_; lean_object* v_data_2093_; 
v___x_2090_ = lean_box(v_result_2082_);
v___x_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
v___x_2092_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0);
lean_inc_ref(v_tag_2042_);
lean_inc_ref(v___x_2091_);
lean_inc(v_cls_2040_);
v_data_2093_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2093_, 0, v_cls_2040_);
lean_ctor_set(v_data_2093_, 1, v___x_2091_);
lean_ctor_set(v_data_2093_, 2, v_tag_2042_);
lean_ctor_set_float(v_data_2093_, sizeof(void*)*3, v___x_2092_);
lean_ctor_set_float(v_data_2093_, sizeof(void*)*3 + 8, v___x_2092_);
lean_ctor_set_uint8(v_data_2093_, sizeof(void*)*3 + 16, v_collapsed_2041_);
if (v___x_2078_ == 0)
{
lean_dec_ref(v___x_2091_);
lean_dec(v_snd_2073_);
lean_dec(v_fst_2072_);
lean_dec_ref(v_tag_2042_);
lean_dec(v_cls_2040_);
v___y_2059_ = v___y_2080_;
v___y_2060_ = v_m_2089_;
v_data_2061_ = v_data_2093_;
goto v___jp_2058_;
}
else
{
lean_object* v_data_2094_; double v___x_2095_; double v___x_2096_; 
lean_dec_ref(v_data_2093_);
v_data_2094_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2094_, 0, v_cls_2040_);
lean_ctor_set(v_data_2094_, 1, v___x_2091_);
lean_ctor_set(v_data_2094_, 2, v_tag_2042_);
v___x_2095_ = lean_unbox_float(v_fst_2072_);
lean_dec(v_fst_2072_);
lean_ctor_set_float(v_data_2094_, sizeof(void*)*3, v___x_2095_);
v___x_2096_ = lean_unbox_float(v_snd_2073_);
lean_dec(v_snd_2073_);
lean_ctor_set_float(v_data_2094_, sizeof(void*)*3 + 8, v___x_2096_);
lean_ctor_set_uint8(v_data_2094_, sizeof(void*)*3 + 16, v_collapsed_2041_);
v___y_2059_ = v___y_2080_;
v___y_2060_ = v_m_2089_;
v_data_2061_ = v_data_2094_;
goto v___jp_2058_;
}
}
}
}
v___jp_2099_:
{
lean_object* v_ref_2100_; lean_object* v___x_2101_; 
v_ref_2100_ = lean_ctor_get(v___y_2050_, 5);
lean_inc(v___y_2051_);
lean_inc_ref(v___y_2050_);
lean_inc(v___y_2049_);
lean_inc_ref(v___y_2048_);
lean_inc(v_fst_2053_);
v___x_2101_ = lean_apply_6(v_msg_2046_, v_fst_2053_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, lean_box(0));
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref(v___x_2101_);
v___y_2080_ = v_ref_2100_;
v_a_2081_ = v_a_2102_;
goto v___jp_2079_;
}
else
{
lean_object* v___x_2103_; 
lean_dec_ref(v___x_2101_);
v___x_2103_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1);
v___y_2080_ = v_ref_2100_;
v_a_2081_ = v___x_2103_;
goto v___jp_2079_;
}
}
v___jp_2104_:
{
if (v_clsEnabled_2044_ == 0)
{
if (v___y_2105_ == 0)
{
lean_object* v___x_2106_; lean_object* v_traceState_2107_; lean_object* v_env_2108_; lean_object* v_nextMacroScope_2109_; lean_object* v_ngen_2110_; lean_object* v_auxDeclNGen_2111_; lean_object* v_cache_2112_; lean_object* v_messages_2113_; lean_object* v_infoState_2114_; lean_object* v_snapshotTasks_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2134_; 
lean_del_object(v___x_2075_);
lean_dec(v_snd_2073_);
lean_dec(v_fst_2072_);
lean_del_object(v___x_2056_);
lean_dec_ref(v_msg_2046_);
lean_dec_ref(v_tag_2042_);
lean_dec(v_cls_2040_);
v___x_2106_ = lean_st_ref_take(v___y_2051_);
v_traceState_2107_ = lean_ctor_get(v___x_2106_, 4);
v_env_2108_ = lean_ctor_get(v___x_2106_, 0);
v_nextMacroScope_2109_ = lean_ctor_get(v___x_2106_, 1);
v_ngen_2110_ = lean_ctor_get(v___x_2106_, 2);
v_auxDeclNGen_2111_ = lean_ctor_get(v___x_2106_, 3);
v_cache_2112_ = lean_ctor_get(v___x_2106_, 5);
v_messages_2113_ = lean_ctor_get(v___x_2106_, 6);
v_infoState_2114_ = lean_ctor_get(v___x_2106_, 7);
v_snapshotTasks_2115_ = lean_ctor_get(v___x_2106_, 8);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2117_ = v___x_2106_;
v_isShared_2118_ = v_isSharedCheck_2134_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_snapshotTasks_2115_);
lean_inc(v_infoState_2114_);
lean_inc(v_messages_2113_);
lean_inc(v_cache_2112_);
lean_inc(v_traceState_2107_);
lean_inc(v_auxDeclNGen_2111_);
lean_inc(v_ngen_2110_);
lean_inc(v_nextMacroScope_2109_);
lean_inc(v_env_2108_);
lean_dec(v___x_2106_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2134_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
uint64_t v_tid_2119_; lean_object* v_traces_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2133_; 
v_tid_2119_ = lean_ctor_get_uint64(v_traceState_2107_, sizeof(void*)*1);
v_traces_2120_ = lean_ctor_get(v_traceState_2107_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_traceState_2107_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2122_ = v_traceState_2107_;
v_isShared_2123_ = v_isSharedCheck_2133_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_traces_2120_);
lean_dec(v_traceState_2107_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2133_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2124_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2045_, v_traces_2120_);
lean_dec_ref(v_traces_2120_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 0, v___x_2124_);
v___x_2126_ = v___x_2122_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2124_);
lean_ctor_set_uint64(v_reuseFailAlloc_2132_, sizeof(void*)*1, v_tid_2119_);
v___x_2126_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2128_; 
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 4, v___x_2126_);
v___x_2128_ = v___x_2117_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_env_2108_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_nextMacroScope_2109_);
lean_ctor_set(v_reuseFailAlloc_2131_, 2, v_ngen_2110_);
lean_ctor_set(v_reuseFailAlloc_2131_, 3, v_auxDeclNGen_2111_);
lean_ctor_set(v_reuseFailAlloc_2131_, 4, v___x_2126_);
lean_ctor_set(v_reuseFailAlloc_2131_, 5, v_cache_2112_);
lean_ctor_set(v_reuseFailAlloc_2131_, 6, v_messages_2113_);
lean_ctor_set(v_reuseFailAlloc_2131_, 7, v_infoState_2114_);
lean_ctor_set(v_reuseFailAlloc_2131_, 8, v_snapshotTasks_2115_);
v___x_2128_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = lean_st_ref_set(v___y_2051_, v___x_2128_);
v___x_2130_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___redArg(v_fst_2053_);
return v___x_2130_;
}
}
}
}
}
else
{
goto v___jp_2099_;
}
}
else
{
goto v___jp_2099_;
}
}
v___jp_2135_:
{
double v___x_2137_; double v___x_2138_; double v___x_2139_; uint8_t v___x_2140_; 
v___x_2137_ = lean_unbox_float(v_snd_2073_);
v___x_2138_ = lean_unbox_float(v_fst_2072_);
v___x_2139_ = lean_float_sub(v___x_2137_, v___x_2138_);
v___x_2140_ = lean_float_decLt(v___y_2136_, v___x_2139_);
v___y_2105_ = v___x_2140_;
goto v___jp_2104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___boxed(lean_object* v_cls_2153_, lean_object* v_collapsed_2154_, lean_object* v_tag_2155_, lean_object* v_opts_2156_, lean_object* v_clsEnabled_2157_, lean_object* v_oldTraces_2158_, lean_object* v_msg_2159_, lean_object* v_resStartStop_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
uint8_t v_collapsed_boxed_2166_; uint8_t v_clsEnabled_boxed_2167_; lean_object* v_res_2168_; 
v_collapsed_boxed_2166_ = lean_unbox(v_collapsed_2154_);
v_clsEnabled_boxed_2167_ = lean_unbox(v_clsEnabled_2157_);
v_res_2168_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v_cls_2153_, v_collapsed_boxed_2166_, v_tag_2155_, v_opts_2156_, v_clsEnabled_boxed_2167_, v_oldTraces_2158_, v_msg_2159_, v_resStartStop_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec_ref(v_opts_2156_);
return v_res_2168_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__3(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__2));
v___x_2174_ = l_Lean_stringToMessageData(v___x_2173_);
return v___x_2174_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__5(void){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__4));
v___x_2177_ = l_Lean_stringToMessageData(v___x_2176_);
return v___x_2177_;
}
}
static double _init_l_Lean_Meta_rwMatcher___closed__6(void){
_start:
{
lean_object* v___x_2178_; double v___x_2179_; 
v___x_2178_ = lean_unsigned_to_nat(1000000000u);
v___x_2179_ = lean_float_of_nat(v___x_2178_);
return v___x_2179_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__8(void){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__7));
v___x_2182_ = l_Lean_stringToMessageData(v___x_2181_);
return v___x_2182_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__13(void){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2190_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2191_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
v___x_2192_ = l_Lean_Name_append(v___x_2191_, v___x_2190_);
return v___x_2192_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__15(void){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2194_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__14));
v___x_2195_ = l_Lean_stringToMessageData(v___x_2194_);
return v___x_2195_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__17(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__16));
v___x_2198_ = l_Lean_stringToMessageData(v___x_2197_);
return v___x_2198_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__19(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__18));
v___x_2201_ = l_Lean_stringToMessageData(v___x_2200_);
return v___x_2201_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__21(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__20));
v___x_2204_ = l_Lean_stringToMessageData(v___x_2203_);
return v___x_2204_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__22(void){
_start:
{
lean_object* v___x_2205_; lean_object* v_dummy_2206_; 
v___x_2205_ = lean_box(0);
v_dummy_2206_ = l_Lean_Expr_sort___override(v___x_2205_);
return v_dummy_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher(lean_object* v_altIdx_2216_, lean_object* v_e_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v___y_2224_; uint8_t v___y_2243_; uint8_t v___y_2248_; lean_object* v___y_2253_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; uint8_t v___y_2261_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v_a_2292_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; uint8_t v___y_2302_; lean_object* v___y_2303_; lean_object* v_proof_2304_; uint8_t v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; uint8_t v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; uint8_t v___y_2330_; uint8_t v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; uint8_t v___y_2347_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v___y_2353_; uint8_t v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; uint8_t v___y_2371_; lean_object* v___y_2372_; uint8_t v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v_a_2376_; uint8_t v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; uint8_t v___y_2400_; uint8_t v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; uint8_t v___y_2409_; lean_object* v___y_2410_; size_t v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; uint8_t v___y_2414_; uint8_t v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; uint8_t v___y_2437_; lean_object* v___y_2438_; size_t v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; uint8_t v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; uint8_t v_fst_2445_; lean_object* v_fst_2446_; lean_object* v_snd_2447_; lean_object* v___y_2448_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; uint8_t v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; uint8_t v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v_a_2482_; uint8_t v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; uint8_t v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v_a_2502_; uint8_t v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; uint8_t v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; uint8_t v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; uint8_t v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v_a_2536_; lean_object* v___y_2549_; uint8_t v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; uint8_t v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v_a_2559_; lean_object* v___y_2562_; uint8_t v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___y_2566_; lean_object* v___y_2567_; uint8_t v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; uint8_t v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; uint8_t v___y_2586_; lean_object* v___y_2587_; uint8_t v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; uint8_t v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; uint8_t v___y_2662_; lean_object* v___x_2853_; uint8_t v___x_2854_; 
v___x_2853_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__25));
v___x_2854_ = l_Lean_Expr_isAppOf(v_e_2217_, v___x_2853_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; uint8_t v___x_2856_; 
v___x_2855_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__27));
v___x_2856_ = l_Lean_Expr_isAppOf(v_e_2217_, v___x_2855_);
v___y_2662_ = v___x_2856_;
goto v___jp_2661_;
}
else
{
v___y_2662_ = v___x_2854_;
goto v___jp_2661_;
}
v___jp_2223_:
{
if (lean_obj_tag(v___y_2224_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2233_; 
v_a_2225_ = lean_ctor_get(v___y_2224_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___y_2224_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2227_ = v___y_2224_;
v_isShared_2228_ = v_isSharedCheck_2233_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___y_2224_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2233_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v_a_2229_; lean_object* v___x_2231_; 
v_a_2229_ = lean_ctor_get(v_a_2225_, 0);
lean_inc(v_a_2229_);
lean_dec(v_a_2225_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 0, v_a_2229_);
v___x_2231_ = v___x_2227_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2229_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
v_a_2234_ = lean_ctor_get(v___y_2224_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___y_2224_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___y_2224_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___y_2224_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
v___jp_2242_:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2244_ = lean_box(0);
v___x_2245_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2245_, 0, v_e_2217_);
lean_ctor_set(v___x_2245_, 1, v___x_2244_);
lean_ctor_set_uint8(v___x_2245_, sizeof(void*)*2, v___y_2243_);
v___x_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2245_);
return v___x_2246_;
}
v___jp_2247_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2249_ = lean_box(0);
v___x_2250_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2250_, 0, v_e_2217_);
lean_ctor_set(v___x_2250_, 1, v___x_2249_);
lean_ctor_set_uint8(v___x_2250_, sizeof(void*)*2, v___y_2248_);
v___x_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
return v___x_2251_;
}
v___jp_2252_:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = lean_box(0);
lean_inc(v_a_2221_);
lean_inc_ref(v_a_2220_);
lean_inc(v_a_2219_);
lean_inc_ref(v_a_2218_);
v___x_2255_ = lean_apply_6(v___y_2253_, v___x_2254_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, lean_box(0));
v___y_2224_ = v___x_2255_;
goto v___jp_2223_;
}
v___jp_2256_:
{
if (v___y_2261_ == 0)
{
lean_object* v_options_2262_; uint8_t v_hasTrace_2263_; 
v_options_2262_ = lean_ctor_get(v_a_2220_, 2);
v_hasTrace_2263_ = lean_ctor_get_uint8(v_options_2262_, sizeof(void*)*1);
if (v_hasTrace_2263_ == 0)
{
lean_dec(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
v___y_2253_ = v___y_2260_;
goto v___jp_2252_;
}
else
{
lean_object* v_inheritedTraceOptions_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; uint8_t v___x_2267_; 
v_inheritedTraceOptions_2264_ = lean_ctor_get(v_a_2220_, 13);
v___x_2265_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2258_);
v___x_2266_ = l_Lean_Name_append(v___x_2265_, v___y_2258_);
v___x_2267_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2264_, v_options_2262_, v___x_2266_);
lean_dec(v___x_2266_);
if (v___x_2267_ == 0)
{
lean_dec(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
v___y_2253_ = v___y_2260_;
goto v___jp_2252_;
}
else
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2268_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__3, &l_Lean_Meta_rwMatcher___closed__3_once, _init_l_Lean_Meta_rwMatcher___closed__3);
v___x_2269_ = l_Lean_MessageData_ofConstName(v___y_2259_, v___y_2261_);
v___x_2270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2268_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
v___x_2271_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__5, &l_Lean_Meta_rwMatcher___closed__5_once, _init_l_Lean_Meta_rwMatcher___closed__5);
v___x_2272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2270_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
v___x_2273_ = l_Lean_Exception_toMessageData(v___y_2257_);
v___x_2274_ = l_Lean_indentD(v___x_2273_);
v___x_2275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2272_);
lean_ctor_set(v___x_2275_, 1, v___x_2274_);
v___x_2276_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2258_, v___x_2275_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; lean_object* v___x_2278_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2277_);
lean_dec_ref(v___x_2276_);
lean_inc(v_a_2221_);
lean_inc_ref(v_a_2220_);
lean_inc(v_a_2219_);
lean_inc_ref(v_a_2218_);
v___x_2278_ = lean_apply_6(v___y_2260_, v_a_2277_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, lean_box(0));
v___y_2224_ = v___x_2278_;
goto v___jp_2223_;
}
else
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2286_; 
lean_dec_ref(v___y_2260_);
v_a_2279_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2281_ = v___x_2276_;
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2276_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2286_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2284_; 
if (v_isShared_2282_ == 0)
{
v___x_2284_ = v___x_2281_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_a_2279_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
}
}
else
{
lean_object* v___x_2287_; 
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec(v___y_2258_);
v___x_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2287_, 0, v___y_2257_);
return v___x_2287_;
}
}
v___jp_2288_:
{
uint8_t v___x_2293_; 
v___x_2293_ = l_Lean_Exception_isInterrupt(v_a_2292_);
if (v___x_2293_ == 0)
{
uint8_t v___x_2294_; 
lean_inc_ref(v_a_2292_);
v___x_2294_ = l_Lean_Exception_isRuntime(v_a_2292_);
v___y_2257_ = v_a_2292_;
v___y_2258_ = v___y_2289_;
v___y_2259_ = v___y_2290_;
v___y_2260_ = v___y_2291_;
v___y_2261_ = v___x_2294_;
goto v___jp_2256_;
}
else
{
v___y_2257_ = v_a_2292_;
v___y_2258_ = v___y_2289_;
v___y_2259_ = v___y_2290_;
v___y_2260_ = v___y_2291_;
v___y_2261_ = v___x_2293_;
goto v___jp_2256_;
}
}
v___jp_2295_:
{
if (lean_obj_tag(v___y_2299_) == 0)
{
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec(v___y_2296_);
return v___y_2299_;
}
else
{
lean_object* v_a_2300_; 
v_a_2300_ = lean_ctor_get(v___y_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref(v___y_2299_);
v___y_2289_ = v___y_2296_;
v___y_2290_ = v___y_2297_;
v___y_2291_ = v___y_2298_;
v_a_2292_ = v_a_2300_;
goto v___jp_2288_;
}
}
v___jp_2301_:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2305_, 0, v_proof_2304_);
v___x_2306_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2306_, 0, v___y_2303_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
lean_ctor_set_uint8(v___x_2306_, sizeof(void*)*2, v___y_2302_);
v___x_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
return v___x_2307_;
}
v___jp_2308_:
{
if (lean_obj_tag(v___y_2314_) == 0)
{
lean_object* v_a_2315_; 
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec(v___y_2310_);
v_a_2315_ = lean_ctor_get(v___y_2314_, 0);
lean_inc(v_a_2315_);
lean_dec_ref(v___y_2314_);
v___y_2302_ = v___y_2309_;
v___y_2303_ = v___y_2311_;
v_proof_2304_ = v_a_2315_;
goto v___jp_2301_;
}
else
{
lean_object* v_a_2316_; 
lean_dec_ref(v___y_2311_);
v_a_2316_ = lean_ctor_get(v___y_2314_, 0);
lean_inc(v_a_2316_);
lean_dec_ref(v___y_2314_);
v___y_2289_ = v___y_2310_;
v___y_2290_ = v___y_2312_;
v___y_2291_ = v___y_2313_;
v_a_2292_ = v_a_2316_;
goto v___jp_2288_;
}
}
v___jp_2317_:
{
if (v___y_2330_ == 0)
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
lean_dec_ref(v___y_2323_);
v___x_2331_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_2332_ = l_Lean_MessageData_ofExpr(v___y_2327_);
v___x_2333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2331_);
lean_ctor_set(v___x_2333_, 1, v___x_2332_);
v___x_2334_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_2335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2333_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
v___x_2336_ = l_Lean_Exception_toMessageData(v___y_2319_);
v___x_2337_ = l_Lean_indentD(v___x_2336_);
v___x_2338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2335_);
lean_ctor_set(v___x_2338_, 1, v___x_2337_);
v___x_2339_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_2340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2338_);
lean_ctor_set(v___x_2340_, 1, v___x_2339_);
v___x_2341_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2340_, v___y_2324_, v___y_2321_, v___y_2329_, v___y_2318_);
v___y_2309_ = v___y_2322_;
v___y_2310_ = v___y_2320_;
v___y_2311_ = v___y_2325_;
v___y_2312_ = v___y_2326_;
v___y_2313_ = v___y_2328_;
v___y_2314_ = v___x_2341_;
goto v___jp_2308_;
}
else
{
lean_dec_ref(v___y_2327_);
lean_dec_ref(v___y_2319_);
v___y_2309_ = v___y_2322_;
v___y_2310_ = v___y_2320_;
v___y_2311_ = v___y_2325_;
v___y_2312_ = v___y_2326_;
v___y_2313_ = v___y_2328_;
v___y_2314_ = v___y_2323_;
goto v___jp_2308_;
}
}
v___jp_2342_:
{
lean_object* v___x_2354_; lean_object* v_a_2355_; lean_object* v___x_2356_; 
v___x_2354_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_2349_, v___y_2351_);
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc(v_a_2355_);
lean_dec_ref(v___x_2354_);
v___x_2356_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_2348_, v___y_2351_);
if (v___y_2347_ == 0)
{
lean_object* v_a_2357_; 
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec(v___y_2344_);
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
lean_inc(v_a_2357_);
lean_dec_ref(v___x_2356_);
v___y_2302_ = v___y_2343_;
v___y_2303_ = v_a_2355_;
v_proof_2304_ = v_a_2357_;
goto v___jp_2301_;
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2359_; 
v_a_2358_ = lean_ctor_get(v___x_2356_, 0);
lean_inc_n(v_a_2358_, 2);
lean_dec_ref(v___x_2356_);
v___x_2359_ = l_Lean_Meta_mkEqOfHEq(v_a_2358_, v___y_2343_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_dec(v_a_2358_);
v___y_2309_ = v___y_2343_;
v___y_2310_ = v___y_2344_;
v___y_2311_ = v_a_2355_;
v___y_2312_ = v___y_2345_;
v___y_2313_ = v___y_2346_;
v___y_2314_ = v___x_2359_;
goto v___jp_2308_;
}
else
{
lean_object* v_a_2360_; uint8_t v___x_2361_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_a_2360_);
v___x_2361_ = l_Lean_Exception_isInterrupt(v_a_2360_);
if (v___x_2361_ == 0)
{
uint8_t v___x_2362_; 
lean_inc(v_a_2360_);
v___x_2362_ = l_Lean_Exception_isRuntime(v_a_2360_);
v___y_2318_ = v___y_2353_;
v___y_2319_ = v_a_2360_;
v___y_2320_ = v___y_2344_;
v___y_2321_ = v___y_2351_;
v___y_2322_ = v___y_2343_;
v___y_2323_ = v___x_2359_;
v___y_2324_ = v___y_2350_;
v___y_2325_ = v_a_2355_;
v___y_2326_ = v___y_2345_;
v___y_2327_ = v_a_2358_;
v___y_2328_ = v___y_2346_;
v___y_2329_ = v___y_2352_;
v___y_2330_ = v___x_2362_;
goto v___jp_2317_;
}
else
{
v___y_2318_ = v___y_2353_;
v___y_2319_ = v_a_2360_;
v___y_2320_ = v___y_2344_;
v___y_2321_ = v___y_2351_;
v___y_2322_ = v___y_2343_;
v___y_2323_ = v___x_2359_;
v___y_2324_ = v___y_2350_;
v___y_2325_ = v_a_2355_;
v___y_2326_ = v___y_2345_;
v___y_2327_ = v_a_2358_;
v___y_2328_ = v___y_2346_;
v___y_2329_ = v___y_2352_;
v___y_2330_ = v___x_2361_;
goto v___jp_2317_;
}
}
}
}
v___jp_2363_:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; uint8_t v___x_2379_; 
v___x_2377_ = lean_array_get_size(v_a_2376_);
v___x_2378_ = lean_unsigned_to_nat(0u);
v___x_2379_ = lean_nat_dec_eq(v___x_2377_, v___x_2378_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v_a_2391_; 
lean_dec_ref(v___y_2374_);
lean_dec_ref(v___y_2372_);
v___x_2380_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
lean_inc(v___y_2368_);
v___x_2381_ = l_Lean_MessageData_ofConstName(v___y_2368_, v___y_2373_);
v___x_2382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2380_);
lean_ctor_set(v___x_2382_, 1, v___x_2381_);
v___x_2383_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_2384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2382_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
v___x_2385_ = lean_array_to_list(v_a_2376_);
v___x_2386_ = lean_box(0);
v___x_2387_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_2385_, v___x_2386_);
v___x_2388_ = l_Lean_MessageData_ofList(v___x_2387_);
v___x_2389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2384_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
v___x_2390_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2389_, v___y_2375_, v___y_2367_, v___y_2370_, v___y_2366_);
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
lean_dec_ref(v___x_2390_);
v___y_2289_ = v___y_2365_;
v___y_2290_ = v___y_2368_;
v___y_2291_ = v___y_2369_;
v_a_2292_ = v_a_2391_;
goto v___jp_2288_;
}
else
{
lean_dec_ref(v_a_2376_);
v___y_2343_ = v___y_2364_;
v___y_2344_ = v___y_2365_;
v___y_2345_ = v___y_2368_;
v___y_2346_ = v___y_2369_;
v___y_2347_ = v___y_2371_;
v___y_2348_ = v___y_2372_;
v___y_2349_ = v___y_2374_;
v___y_2350_ = v___y_2375_;
v___y_2351_ = v___y_2367_;
v___y_2352_ = v___y_2370_;
v___y_2353_ = v___y_2366_;
goto v___jp_2342_;
}
}
v___jp_2392_:
{
if (lean_obj_tag(v___y_2405_) == 0)
{
lean_object* v_a_2406_; 
v_a_2406_ = lean_ctor_get(v___y_2405_, 0);
lean_inc(v_a_2406_);
lean_dec_ref(v___y_2405_);
v___y_2364_ = v___y_2393_;
v___y_2365_ = v___y_2394_;
v___y_2366_ = v___y_2395_;
v___y_2367_ = v___y_2396_;
v___y_2368_ = v___y_2397_;
v___y_2369_ = v___y_2399_;
v___y_2370_ = v___y_2398_;
v___y_2371_ = v___y_2400_;
v___y_2372_ = v___y_2402_;
v___y_2373_ = v___y_2401_;
v___y_2374_ = v___y_2403_;
v___y_2375_ = v___y_2404_;
v_a_2376_ = v_a_2406_;
goto v___jp_2363_;
}
else
{
lean_object* v_a_2407_; 
lean_dec_ref(v___y_2403_);
lean_dec_ref(v___y_2402_);
v_a_2407_ = lean_ctor_get(v___y_2405_, 0);
lean_inc(v_a_2407_);
lean_dec_ref(v___y_2405_);
v___y_2289_ = v___y_2394_;
v___y_2290_ = v___y_2397_;
v___y_2291_ = v___y_2399_;
v_a_2292_ = v_a_2407_;
goto v___jp_2288_;
}
}
v___jp_2408_:
{
lean_object* v___x_2423_; size_t v_sz_2424_; lean_object* v___x_2425_; 
v___x_2423_ = lean_box(0);
v_sz_2424_ = lean_array_size(v___y_2418_);
v___x_2425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___y_2418_, v_sz_2424_, v___y_2411_, v___x_2423_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; uint8_t v___x_2429_; 
lean_dec_ref(v___x_2425_);
v___x_2426_ = lean_unsigned_to_nat(0u);
v___x_2427_ = lean_array_get_size(v___y_2418_);
v___x_2428_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_2429_ = lean_nat_dec_lt(v___x_2426_, v___x_2427_);
if (v___x_2429_ == 0)
{
lean_dec_ref(v___y_2418_);
v___y_2364_ = v___y_2409_;
v___y_2365_ = v___y_2410_;
v___y_2366_ = v___y_2422_;
v___y_2367_ = v___y_2420_;
v___y_2368_ = v___y_2412_;
v___y_2369_ = v___y_2413_;
v___y_2370_ = v___y_2421_;
v___y_2371_ = v___y_2414_;
v___y_2372_ = v___y_2416_;
v___y_2373_ = v___y_2415_;
v___y_2374_ = v___y_2417_;
v___y_2375_ = v___y_2419_;
v_a_2376_ = v___x_2428_;
goto v___jp_2363_;
}
else
{
uint8_t v___x_2430_; 
v___x_2430_ = lean_nat_dec_le(v___x_2427_, v___x_2427_);
if (v___x_2430_ == 0)
{
if (v___x_2429_ == 0)
{
lean_dec_ref(v___y_2418_);
v___y_2364_ = v___y_2409_;
v___y_2365_ = v___y_2410_;
v___y_2366_ = v___y_2422_;
v___y_2367_ = v___y_2420_;
v___y_2368_ = v___y_2412_;
v___y_2369_ = v___y_2413_;
v___y_2370_ = v___y_2421_;
v___y_2371_ = v___y_2414_;
v___y_2372_ = v___y_2416_;
v___y_2373_ = v___y_2415_;
v___y_2374_ = v___y_2417_;
v___y_2375_ = v___y_2419_;
v_a_2376_ = v___x_2428_;
goto v___jp_2363_;
}
else
{
size_t v___x_2431_; lean_object* v___x_2432_; 
v___x_2431_ = lean_usize_of_nat(v___x_2427_);
v___x_2432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___y_2418_, v___y_2411_, v___x_2431_, v___x_2428_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
lean_dec_ref(v___y_2418_);
v___y_2393_ = v___y_2409_;
v___y_2394_ = v___y_2410_;
v___y_2395_ = v___y_2422_;
v___y_2396_ = v___y_2420_;
v___y_2397_ = v___y_2412_;
v___y_2398_ = v___y_2421_;
v___y_2399_ = v___y_2413_;
v___y_2400_ = v___y_2414_;
v___y_2401_ = v___y_2415_;
v___y_2402_ = v___y_2416_;
v___y_2403_ = v___y_2417_;
v___y_2404_ = v___y_2419_;
v___y_2405_ = v___x_2432_;
goto v___jp_2392_;
}
}
else
{
size_t v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = lean_usize_of_nat(v___x_2427_);
v___x_2434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___y_2418_, v___y_2411_, v___x_2433_, v___x_2428_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
lean_dec_ref(v___y_2418_);
v___y_2393_ = v___y_2409_;
v___y_2394_ = v___y_2410_;
v___y_2395_ = v___y_2422_;
v___y_2396_ = v___y_2420_;
v___y_2397_ = v___y_2412_;
v___y_2398_ = v___y_2421_;
v___y_2399_ = v___y_2413_;
v___y_2400_ = v___y_2414_;
v___y_2401_ = v___y_2415_;
v___y_2402_ = v___y_2416_;
v___y_2403_ = v___y_2417_;
v___y_2404_ = v___y_2419_;
v___y_2405_ = v___x_2434_;
goto v___jp_2392_;
}
}
}
else
{
lean_object* v_a_2435_; 
lean_dec_ref(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec_ref(v___y_2416_);
v_a_2435_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_a_2435_);
lean_dec_ref(v___x_2425_);
v___y_2289_ = v___y_2410_;
v___y_2290_ = v___y_2412_;
v___y_2291_ = v___y_2413_;
v_a_2292_ = v_a_2435_;
goto v___jp_2288_;
}
}
v___jp_2436_:
{
lean_object* v___x_2452_; 
lean_inc_ref(v_fst_2446_);
lean_inc_ref(v_e_2217_);
v___x_2452_ = l_Lean_Meta_isExprDefEq(v_e_2217_, v_fst_2446_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; uint8_t v___x_2454_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_a_2453_);
lean_dec_ref(v___x_2452_);
v___x_2454_ = lean_unbox(v_a_2453_);
lean_dec(v_a_2453_);
if (v___x_2454_ == 0)
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v_a_2469_; 
lean_dec_ref(v_snd_2447_);
lean_dec_ref(v___y_2444_);
lean_dec_ref(v___y_2443_);
v___x_2455_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_2456_ = l_Lean_MessageData_ofExpr(v_fst_2446_);
v___x_2457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2455_);
lean_ctor_set(v___x_2457_, 1, v___x_2456_);
v___x_2458_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_2459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2457_);
lean_ctor_set(v___x_2459_, 1, v___x_2458_);
lean_inc(v___y_2440_);
v___x_2460_ = l_Lean_MessageData_ofConstName(v___y_2440_, v___y_2442_);
v___x_2461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2459_);
lean_ctor_set(v___x_2461_, 1, v___x_2460_);
v___x_2462_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_2463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2461_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
v___x_2464_ = l_Lean_MessageData_ofExpr(v_e_2217_);
v___x_2465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2463_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
v___x_2466_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_2467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2465_);
lean_ctor_set(v___x_2467_, 1, v___x_2466_);
v___x_2468_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2467_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_a_2469_);
lean_dec_ref(v___x_2468_);
v___y_2289_ = v___y_2438_;
v___y_2290_ = v___y_2440_;
v___y_2291_ = v___y_2441_;
v_a_2292_ = v_a_2469_;
goto v___jp_2288_;
}
else
{
lean_dec_ref(v_fst_2446_);
lean_dec_ref(v_e_2217_);
v___y_2409_ = v___y_2437_;
v___y_2410_ = v___y_2438_;
v___y_2411_ = v___y_2439_;
v___y_2412_ = v___y_2440_;
v___y_2413_ = v___y_2441_;
v___y_2414_ = v_fst_2445_;
v___y_2415_ = v___y_2442_;
v___y_2416_ = v___y_2443_;
v___y_2417_ = v_snd_2447_;
v___y_2418_ = v___y_2444_;
v___y_2419_ = v___y_2448_;
v___y_2420_ = v___y_2449_;
v___y_2421_ = v___y_2450_;
v___y_2422_ = v___y_2451_;
goto v___jp_2408_;
}
}
else
{
lean_object* v_a_2470_; 
lean_dec_ref(v_snd_2447_);
lean_dec_ref(v_fst_2446_);
lean_dec_ref(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec_ref(v_e_2217_);
v_a_2470_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_a_2470_);
lean_dec_ref(v___x_2452_);
v___y_2289_ = v___y_2438_;
v___y_2290_ = v___y_2440_;
v___y_2291_ = v___y_2441_;
v_a_2292_ = v_a_2470_;
goto v___jp_2288_;
}
}
v___jp_2471_:
{
lean_object* v___x_2483_; double v___x_2484_; double v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2483_ = lean_io_get_num_heartbeats();
v___x_2484_ = lean_float_of_nat(v___y_2475_);
v___x_2485_ = lean_float_of_nat(v___x_2483_);
v___x_2486_ = lean_box_float(v___x_2484_);
v___x_2487_ = lean_box_float(v___x_2485_);
v___x_2488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2486_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2489_, 0, v_a_2482_);
lean_ctor_set(v___x_2489_, 1, v___x_2488_);
lean_inc_ref(v___y_2480_);
lean_inc(v___y_2474_);
v___x_2490_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v___y_2474_, v___y_2472_, v___y_2480_, v___y_2477_, v___y_2479_, v___y_2473_, v___y_2481_, v___x_2489_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
v___y_2296_ = v___y_2474_;
v___y_2297_ = v___y_2476_;
v___y_2298_ = v___y_2478_;
v___y_2299_ = v___x_2490_;
goto v___jp_2295_;
}
v___jp_2491_:
{
lean_object* v___x_2503_; 
v___x_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2503_, 0, v_a_2502_);
v___y_2472_ = v___y_2492_;
v___y_2473_ = v___y_2493_;
v___y_2474_ = v___y_2495_;
v___y_2475_ = v___y_2494_;
v___y_2476_ = v___y_2497_;
v___y_2477_ = v___y_2496_;
v___y_2478_ = v___y_2499_;
v___y_2479_ = v___y_2498_;
v___y_2480_ = v___y_2500_;
v___y_2481_ = v___y_2501_;
v_a_2482_ = v___x_2503_;
goto v___jp_2471_;
}
v___jp_2504_:
{
if (lean_obj_tag(v___y_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
v_a_2516_ = lean_ctor_get(v___y_2515_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___y_2515_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___y_2515_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___y_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
lean_ctor_set_tag(v___x_2518_, 1);
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
v___y_2472_ = v___y_2505_;
v___y_2473_ = v___y_2506_;
v___y_2474_ = v___y_2508_;
v___y_2475_ = v___y_2507_;
v___y_2476_ = v___y_2510_;
v___y_2477_ = v___y_2509_;
v___y_2478_ = v___y_2512_;
v___y_2479_ = v___y_2511_;
v___y_2480_ = v___y_2513_;
v___y_2481_ = v___y_2514_;
v_a_2482_ = v___x_2521_;
goto v___jp_2471_;
}
}
}
else
{
lean_object* v_a_2524_; 
v_a_2524_ = lean_ctor_get(v___y_2515_, 0);
lean_inc(v_a_2524_);
lean_dec_ref(v___y_2515_);
v___y_2492_ = v___y_2505_;
v___y_2493_ = v___y_2506_;
v___y_2494_ = v___y_2507_;
v___y_2495_ = v___y_2508_;
v___y_2496_ = v___y_2509_;
v___y_2497_ = v___y_2510_;
v___y_2498_ = v___y_2511_;
v___y_2499_ = v___y_2512_;
v___y_2500_ = v___y_2513_;
v___y_2501_ = v___y_2514_;
v_a_2502_ = v_a_2524_;
goto v___jp_2491_;
}
}
v___jp_2525_:
{
lean_object* v___x_2537_; double v___x_2538_; double v___x_2539_; double v___x_2540_; double v___x_2541_; double v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2537_ = lean_io_mono_nanos_now();
v___x_2538_ = lean_float_of_nat(v___y_2527_);
v___x_2539_ = lean_float_once(&l_Lean_Meta_rwMatcher___closed__6, &l_Lean_Meta_rwMatcher___closed__6_once, _init_l_Lean_Meta_rwMatcher___closed__6);
v___x_2540_ = lean_float_div(v___x_2538_, v___x_2539_);
v___x_2541_ = lean_float_of_nat(v___x_2537_);
v___x_2542_ = lean_float_div(v___x_2541_, v___x_2539_);
v___x_2543_ = lean_box_float(v___x_2540_);
v___x_2544_ = lean_box_float(v___x_2542_);
v___x_2545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2543_);
lean_ctor_set(v___x_2545_, 1, v___x_2544_);
v___x_2546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2546_, 0, v_a_2536_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
lean_inc_ref(v___y_2534_);
lean_inc(v___y_2529_);
v___x_2547_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v___y_2529_, v___y_2526_, v___y_2534_, v___y_2531_, v___y_2533_, v___y_2528_, v___y_2535_, v___x_2546_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
v___y_2296_ = v___y_2529_;
v___y_2297_ = v___y_2530_;
v___y_2298_ = v___y_2532_;
v___y_2299_ = v___x_2547_;
goto v___jp_2295_;
}
v___jp_2548_:
{
lean_object* v___x_2560_; 
v___x_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2560_, 0, v_a_2559_);
v___y_2526_ = v___y_2550_;
v___y_2527_ = v___y_2549_;
v___y_2528_ = v___y_2551_;
v___y_2529_ = v___y_2552_;
v___y_2530_ = v___y_2554_;
v___y_2531_ = v___y_2553_;
v___y_2532_ = v___y_2556_;
v___y_2533_ = v___y_2555_;
v___y_2534_ = v___y_2557_;
v___y_2535_ = v___y_2558_;
v_a_2536_ = v___x_2560_;
goto v___jp_2525_;
}
v___jp_2561_:
{
if (lean_obj_tag(v___y_2572_) == 0)
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
v_a_2573_ = lean_ctor_get(v___y_2572_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___y_2572_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2575_ = v___y_2572_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___y_2572_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
lean_ctor_set_tag(v___x_2575_, 1);
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
v___y_2526_ = v___y_2563_;
v___y_2527_ = v___y_2562_;
v___y_2528_ = v___y_2564_;
v___y_2529_ = v___y_2565_;
v___y_2530_ = v___y_2567_;
v___y_2531_ = v___y_2566_;
v___y_2532_ = v___y_2569_;
v___y_2533_ = v___y_2568_;
v___y_2534_ = v___y_2570_;
v___y_2535_ = v___y_2571_;
v_a_2536_ = v___x_2578_;
goto v___jp_2525_;
}
}
}
else
{
lean_object* v_a_2581_; 
v_a_2581_ = lean_ctor_get(v___y_2572_, 0);
lean_inc(v_a_2581_);
lean_dec_ref(v___y_2572_);
v___y_2549_ = v___y_2562_;
v___y_2550_ = v___y_2563_;
v___y_2551_ = v___y_2564_;
v___y_2552_ = v___y_2565_;
v___y_2553_ = v___y_2566_;
v___y_2554_ = v___y_2567_;
v___y_2555_ = v___y_2568_;
v___y_2556_ = v___y_2569_;
v___y_2557_ = v___y_2570_;
v___y_2558_ = v___y_2571_;
v_a_2559_ = v_a_2581_;
goto v___jp_2548_;
}
}
v___jp_2582_:
{
lean_object* v___x_2597_; lean_object* v_a_2598_; lean_object* v___x_2599_; uint8_t v___x_2600_; 
v___x_2597_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg(v_a_2221_);
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2598_);
lean_dec_ref(v___x_2597_);
v___x_2599_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2600_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v___y_2592_, v___x_2599_);
if (v___x_2600_ == 0)
{
lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2601_ = lean_io_mono_nanos_now();
lean_inc(v_a_2221_);
lean_inc_ref(v_a_2220_);
lean_inc(v_a_2219_);
lean_inc_ref(v_a_2218_);
v___x_2602_ = lean_infer_type(v___y_2590_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_a_2603_; uint8_t v___x_2604_; lean_object* v___x_2605_; 
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
lean_inc(v_a_2603_);
lean_dec_ref(v___x_2602_);
v___x_2604_ = 0;
v___x_2605_ = l_Lean_Meta_forallMetaTelescope(v_a_2603_, v___x_2604_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; lean_object* v_snd_2607_; lean_object* v_fst_2608_; lean_object* v_snd_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2627_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
lean_inc(v_a_2606_);
lean_dec_ref(v___x_2605_);
v_snd_2607_ = lean_ctor_get(v_a_2606_, 1);
lean_inc(v_snd_2607_);
v_fst_2608_ = lean_ctor_get(v_a_2606_, 0);
lean_inc(v_fst_2608_);
lean_dec(v_a_2606_);
v_snd_2609_ = lean_ctor_get(v_snd_2607_, 1);
v_isSharedCheck_2627_ = !lean_is_exclusive(v_snd_2607_);
if (v_isSharedCheck_2627_ == 0)
{
lean_object* v_unused_2628_; 
v_unused_2628_ = lean_ctor_get(v_snd_2607_, 0);
lean_dec(v_unused_2628_);
v___x_2611_ = v_snd_2607_;
v_isShared_2612_ = v_isSharedCheck_2627_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_snd_2609_);
lean_dec(v_snd_2607_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2627_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; uint8_t v___x_2615_; 
v___x_2613_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2589_);
v___x_2614_ = l_Lean_Name_append(v___x_2613_, v___y_2589_);
v___x_2615_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2596_, v___y_2592_, v___x_2614_);
lean_dec(v___x_2614_);
if (v___x_2615_ == 0)
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
lean_del_object(v___x_2611_);
v___x_2616_ = lean_box(0);
v___x_2617_ = l_Lean_Meta_rwMatcher___lam__2(v___y_2583_, v___y_2584_, v_fst_2608_, v___y_2585_, v___x_2600_, v_e_2217_, v_snd_2609_, v___x_2616_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
lean_dec(v_snd_2609_);
v___y_2562_ = v___x_2601_;
v___y_2563_ = v___y_2588_;
v___y_2564_ = v_a_2598_;
v___y_2565_ = v___y_2589_;
v___y_2566_ = v___y_2592_;
v___y_2567_ = v___y_2591_;
v___y_2568_ = v___y_2593_;
v___y_2569_ = v___y_2594_;
v___y_2570_ = v___y_2595_;
v___y_2571_ = v___y_2587_;
v___y_2572_ = v___x_2617_;
goto v___jp_2561_;
}
else
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2621_; 
v___x_2618_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2609_);
v___x_2619_ = l_Lean_indentExpr(v_snd_2609_);
if (v_isShared_2612_ == 0)
{
lean_ctor_set_tag(v___x_2611_, 7);
lean_ctor_set(v___x_2611_, 1, v___x_2619_);
lean_ctor_set(v___x_2611_, 0, v___x_2618_);
v___x_2621_ = v___x_2611_;
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
lean_inc(v___y_2589_);
v___x_2622_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2589_, v___x_2621_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2623_; lean_object* v___x_2624_; 
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
lean_inc(v_a_2623_);
lean_dec_ref(v___x_2622_);
v___x_2624_ = l_Lean_Meta_rwMatcher___lam__2(v___y_2583_, v___y_2584_, v_fst_2608_, v___y_2585_, v___x_2600_, v_e_2217_, v_snd_2609_, v_a_2623_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
lean_dec(v_snd_2609_);
v___y_2562_ = v___x_2601_;
v___y_2563_ = v___y_2588_;
v___y_2564_ = v_a_2598_;
v___y_2565_ = v___y_2589_;
v___y_2566_ = v___y_2592_;
v___y_2567_ = v___y_2591_;
v___y_2568_ = v___y_2593_;
v___y_2569_ = v___y_2594_;
v___y_2570_ = v___y_2595_;
v___y_2571_ = v___y_2587_;
v___y_2572_ = v___x_2624_;
goto v___jp_2561_;
}
else
{
lean_object* v_a_2625_; 
lean_dec(v_snd_2609_);
lean_dec(v_fst_2608_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec_ref(v_e_2217_);
v_a_2625_ = lean_ctor_get(v___x_2622_, 0);
lean_inc(v_a_2625_);
lean_dec_ref(v___x_2622_);
v___y_2549_ = v___x_2601_;
v___y_2550_ = v___y_2588_;
v___y_2551_ = v_a_2598_;
v___y_2552_ = v___y_2589_;
v___y_2553_ = v___y_2592_;
v___y_2554_ = v___y_2591_;
v___y_2555_ = v___y_2593_;
v___y_2556_ = v___y_2594_;
v___y_2557_ = v___y_2595_;
v___y_2558_ = v___y_2587_;
v_a_2559_ = v_a_2625_;
goto v___jp_2548_;
}
}
}
}
}
else
{
lean_object* v_a_2629_; 
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec_ref(v_e_2217_);
v_a_2629_ = lean_ctor_get(v___x_2605_, 0);
lean_inc(v_a_2629_);
lean_dec_ref(v___x_2605_);
v___y_2549_ = v___x_2601_;
v___y_2550_ = v___y_2588_;
v___y_2551_ = v_a_2598_;
v___y_2552_ = v___y_2589_;
v___y_2553_ = v___y_2592_;
v___y_2554_ = v___y_2591_;
v___y_2555_ = v___y_2593_;
v___y_2556_ = v___y_2594_;
v___y_2557_ = v___y_2595_;
v___y_2558_ = v___y_2587_;
v_a_2559_ = v_a_2629_;
goto v___jp_2548_;
}
}
else
{
lean_object* v_a_2630_; 
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec_ref(v_e_2217_);
v_a_2630_ = lean_ctor_get(v___x_2602_, 0);
lean_inc(v_a_2630_);
lean_dec_ref(v___x_2602_);
v___y_2549_ = v___x_2601_;
v___y_2550_ = v___y_2588_;
v___y_2551_ = v_a_2598_;
v___y_2552_ = v___y_2589_;
v___y_2553_ = v___y_2592_;
v___y_2554_ = v___y_2591_;
v___y_2555_ = v___y_2593_;
v___y_2556_ = v___y_2594_;
v___y_2557_ = v___y_2595_;
v___y_2558_ = v___y_2587_;
v_a_2559_ = v_a_2630_;
goto v___jp_2548_;
}
}
else
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2631_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2221_);
lean_inc_ref(v_a_2220_);
lean_inc(v_a_2219_);
lean_inc_ref(v_a_2218_);
v___x_2632_ = lean_infer_type(v___y_2590_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; uint8_t v___x_2634_; lean_object* v___x_2635_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_a_2633_);
lean_dec_ref(v___x_2632_);
v___x_2634_ = 0;
v___x_2635_ = l_Lean_Meta_forallMetaTelescope(v_a_2633_, v___x_2634_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v_a_2636_; lean_object* v_snd_2637_; lean_object* v_fst_2638_; lean_object* v_snd_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2657_; 
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_a_2636_);
lean_dec_ref(v___x_2635_);
v_snd_2637_ = lean_ctor_get(v_a_2636_, 1);
lean_inc(v_snd_2637_);
v_fst_2638_ = lean_ctor_get(v_a_2636_, 0);
lean_inc(v_fst_2638_);
lean_dec(v_a_2636_);
v_snd_2639_ = lean_ctor_get(v_snd_2637_, 1);
v_isSharedCheck_2657_ = !lean_is_exclusive(v_snd_2637_);
if (v_isSharedCheck_2657_ == 0)
{
lean_object* v_unused_2658_; 
v_unused_2658_ = lean_ctor_get(v_snd_2637_, 0);
lean_dec(v_unused_2658_);
v___x_2641_ = v_snd_2637_;
v_isShared_2642_ = v_isSharedCheck_2657_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_snd_2639_);
lean_dec(v_snd_2637_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2657_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; uint8_t v___x_2645_; 
v___x_2643_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2589_);
v___x_2644_ = l_Lean_Name_append(v___x_2643_, v___y_2589_);
v___x_2645_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2596_, v___y_2592_, v___x_2644_);
lean_dec(v___x_2644_);
if (v___x_2645_ == 0)
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
lean_del_object(v___x_2641_);
v___x_2646_ = lean_box(0);
v___x_2647_ = l_Lean_Meta_rwMatcher___lam__3(v___y_2583_, v___y_2584_, v_fst_2638_, v___y_2585_, v___x_2600_, v_e_2217_, v___y_2586_, v_snd_2639_, v___x_2646_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
lean_dec(v_snd_2639_);
v___y_2505_ = v___y_2588_;
v___y_2506_ = v_a_2598_;
v___y_2507_ = v___x_2631_;
v___y_2508_ = v___y_2589_;
v___y_2509_ = v___y_2592_;
v___y_2510_ = v___y_2591_;
v___y_2511_ = v___y_2593_;
v___y_2512_ = v___y_2594_;
v___y_2513_ = v___y_2595_;
v___y_2514_ = v___y_2587_;
v___y_2515_ = v___x_2647_;
goto v___jp_2504_;
}
else
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2648_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2639_);
v___x_2649_ = l_Lean_indentExpr(v_snd_2639_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set_tag(v___x_2641_, 7);
lean_ctor_set(v___x_2641_, 1, v___x_2649_);
lean_ctor_set(v___x_2641_, 0, v___x_2648_);
v___x_2651_ = v___x_2641_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2648_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v___x_2649_);
v___x_2651_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
lean_object* v___x_2652_; 
lean_inc(v___y_2589_);
v___x_2652_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2589_, v___x_2651_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v___x_2654_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
lean_dec_ref(v___x_2652_);
v___x_2654_ = l_Lean_Meta_rwMatcher___lam__3(v___y_2583_, v___y_2584_, v_fst_2638_, v___y_2585_, v___x_2600_, v_e_2217_, v___y_2586_, v_snd_2639_, v_a_2653_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
lean_dec(v_snd_2639_);
v___y_2505_ = v___y_2588_;
v___y_2506_ = v_a_2598_;
v___y_2507_ = v___x_2631_;
v___y_2508_ = v___y_2589_;
v___y_2509_ = v___y_2592_;
v___y_2510_ = v___y_2591_;
v___y_2511_ = v___y_2593_;
v___y_2512_ = v___y_2594_;
v___y_2513_ = v___y_2595_;
v___y_2514_ = v___y_2587_;
v___y_2515_ = v___x_2654_;
goto v___jp_2504_;
}
else
{
lean_object* v_a_2655_; 
lean_dec(v_snd_2639_);
lean_dec(v_fst_2638_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec_ref(v_e_2217_);
v_a_2655_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2655_);
lean_dec_ref(v___x_2652_);
v___y_2492_ = v___y_2588_;
v___y_2493_ = v_a_2598_;
v___y_2494_ = v___x_2631_;
v___y_2495_ = v___y_2589_;
v___y_2496_ = v___y_2592_;
v___y_2497_ = v___y_2591_;
v___y_2498_ = v___y_2593_;
v___y_2499_ = v___y_2594_;
v___y_2500_ = v___y_2595_;
v___y_2501_ = v___y_2587_;
v_a_2502_ = v_a_2655_;
goto v___jp_2491_;
}
}
}
}
}
else
{
lean_object* v_a_2659_; 
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec_ref(v_e_2217_);
v_a_2659_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_a_2659_);
lean_dec_ref(v___x_2635_);
v___y_2492_ = v___y_2588_;
v___y_2493_ = v_a_2598_;
v___y_2494_ = v___x_2631_;
v___y_2495_ = v___y_2589_;
v___y_2496_ = v___y_2592_;
v___y_2497_ = v___y_2591_;
v___y_2498_ = v___y_2593_;
v___y_2499_ = v___y_2594_;
v___y_2500_ = v___y_2595_;
v___y_2501_ = v___y_2587_;
v_a_2502_ = v_a_2659_;
goto v___jp_2491_;
}
}
else
{
lean_object* v_a_2660_; 
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec_ref(v_e_2217_);
v_a_2660_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_a_2660_);
lean_dec_ref(v___x_2632_);
v___y_2492_ = v___y_2588_;
v___y_2493_ = v_a_2598_;
v___y_2494_ = v___x_2631_;
v___y_2495_ = v___y_2589_;
v___y_2496_ = v___y_2592_;
v___y_2497_ = v___y_2591_;
v___y_2498_ = v___y_2593_;
v___y_2499_ = v___y_2594_;
v___y_2500_ = v___y_2595_;
v___y_2501_ = v___y_2587_;
v_a_2502_ = v_a_2660_;
goto v___jp_2491_;
}
}
}
v___jp_2661_:
{
uint8_t v___x_2663_; 
v___x_2663_ = 1;
if (v___y_2662_ == 0)
{
lean_object* v___x_2664_; lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2833_; 
v___x_2664_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(v_e_2217_, v_a_2221_);
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2667_ = v___x_2664_;
v_isShared_2668_ = v_isSharedCheck_2833_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2664_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2833_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
uint8_t v___x_2669_; 
v___x_2669_ = lean_unbox(v_a_2665_);
lean_dec(v_a_2665_);
if (v___x_2669_ == 0)
{
lean_object* v_options_2670_; uint8_t v_hasTrace_2671_; 
lean_del_object(v___x_2667_);
lean_dec(v_altIdx_2216_);
v_options_2670_ = lean_ctor_get(v_a_2220_, 2);
v_hasTrace_2671_ = lean_ctor_get_uint8(v_options_2670_, sizeof(void*)*1);
if (v_hasTrace_2671_ == 0)
{
v___y_2243_ = v___x_2663_;
goto v___jp_2242_;
}
else
{
lean_object* v_inheritedTraceOptions_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; 
v_inheritedTraceOptions_2672_ = lean_ctor_get(v_a_2220_, 13);
v___x_2673_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2674_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2675_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2672_, v_options_2670_, v___x_2674_);
if (v___x_2675_ == 0)
{
v___y_2243_ = v___x_2663_;
goto v___jp_2242_;
}
else
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2676_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__15, &l_Lean_Meta_rwMatcher___closed__15_once, _init_l_Lean_Meta_rwMatcher___closed__15);
lean_inc_ref(v_e_2217_);
v___x_2677_ = l_Lean_indentExpr(v_e_2217_);
v___x_2678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2676_);
lean_ctor_set(v___x_2678_, 1, v___x_2677_);
v___x_2679_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2673_, v___x_2678_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_dec_ref(v___x_2679_);
v___y_2243_ = v___x_2663_;
goto v___jp_2242_;
}
else
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
lean_dec_ref(v_e_2217_);
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2682_ = v___x_2679_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2679_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2680_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
}
}
else
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2688_ = l_Lean_Expr_getAppFn(v_e_2217_);
v___x_2689_ = l_Lean_Expr_constName_x21(v___x_2688_);
lean_inc(v_a_2221_);
lean_inc_ref(v_a_2220_);
lean_inc(v_a_2219_);
lean_inc_ref(v_a_2218_);
lean_inc(v___x_2689_);
v___x_2690_ = lean_get_congr_match_equations_for(v___x_2689_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v_a_2691_; lean_object* v___x_2692_; uint8_t v___x_2693_; 
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_a_2691_);
lean_dec_ref(v___x_2690_);
v___x_2692_ = lean_array_get_size(v_a_2691_);
v___x_2693_ = lean_nat_dec_lt(v_altIdx_2216_, v___x_2692_);
if (v___x_2693_ == 0)
{
lean_object* v_options_2694_; uint8_t v_hasTrace_2695_; 
lean_dec(v_a_2691_);
lean_dec_ref(v___x_2688_);
v_options_2694_ = lean_ctor_get(v_a_2220_, 2);
v_hasTrace_2695_ = lean_ctor_get_uint8(v_options_2694_, sizeof(void*)*1);
if (v_hasTrace_2695_ == 0)
{
lean_dec(v___x_2689_);
lean_del_object(v___x_2667_);
lean_dec(v_altIdx_2216_);
v___y_2248_ = v___x_2663_;
goto v___jp_2247_;
}
else
{
lean_object* v_inheritedTraceOptions_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; uint8_t v___x_2699_; 
v_inheritedTraceOptions_2696_ = lean_ctor_get(v_a_2220_, 13);
v___x_2697_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2698_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2699_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2696_, v_options_2694_, v___x_2698_);
if (v___x_2699_ == 0)
{
lean_dec(v___x_2689_);
lean_del_object(v___x_2667_);
lean_dec(v_altIdx_2216_);
v___y_2248_ = v___x_2663_;
goto v___jp_2247_;
}
else
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2703_; 
v___x_2700_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__17, &l_Lean_Meta_rwMatcher___closed__17_once, _init_l_Lean_Meta_rwMatcher___closed__17);
v___x_2701_ = l_Nat_reprFast(v_altIdx_2216_);
if (v_isShared_2668_ == 0)
{
lean_ctor_set_tag(v___x_2667_, 3);
lean_ctor_set(v___x_2667_, 0, v___x_2701_);
v___x_2703_ = v___x_2667_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2701_);
v___x_2703_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2704_ = l_Lean_MessageData_ofFormat(v___x_2703_);
v___x_2705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2700_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
v___x_2706_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__19, &l_Lean_Meta_rwMatcher___closed__19_once, _init_l_Lean_Meta_rwMatcher___closed__19);
v___x_2707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2705_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
v___x_2708_ = l_Nat_reprFast(v___x_2692_);
v___x_2709_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
v___x_2710_ = l_Lean_MessageData_ofFormat(v___x_2709_);
v___x_2711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2707_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
v___x_2712_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__21, &l_Lean_Meta_rwMatcher___closed__21_once, _init_l_Lean_Meta_rwMatcher___closed__21);
v___x_2713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2711_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
v___x_2714_ = l_Lean_MessageData_ofConstName(v___x_2689_, v___y_2662_);
v___x_2715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2713_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v___x_2716_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2697_, v___x_2715_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_dec_ref(v___x_2716_);
v___y_2248_ = v___x_2663_;
goto v___jp_2247_;
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
lean_dec_ref(v_e_2217_);
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2719_ = v___x_2716_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2716_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
}
}
}
else
{
lean_object* v_options_2726_; lean_object* v_inheritedTraceOptions_2727_; uint8_t v_hasTrace_2728_; lean_object* v_nargs_2729_; lean_object* v___x_2730_; lean_object* v___f_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v_dummy_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
lean_dec(v___x_2689_);
lean_del_object(v___x_2667_);
v_options_2726_ = lean_ctor_get(v_a_2220_, 2);
v_inheritedTraceOptions_2727_ = lean_ctor_get(v_a_2220_, 13);
v_hasTrace_2728_ = lean_ctor_get_uint8(v_options_2726_, sizeof(void*)*1);
v_nargs_2729_ = l_Lean_Expr_getAppNumArgs(v_e_2217_);
v___x_2730_ = lean_box(v___x_2663_);
lean_inc_ref_n(v_e_2217_, 2);
v___f_2731_ = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2731_, 0, v_e_2217_);
lean_closure_set(v___f_2731_, 1, v___x_2730_);
v___x_2732_ = lean_box(0);
v___x_2733_ = lean_array_get(v___x_2732_, v_a_2691_, v_altIdx_2216_);
lean_dec(v_altIdx_2216_);
lean_dec(v_a_2691_);
v___x_2734_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2735_ = l_Lean_Expr_constLevels_x21(v___x_2688_);
lean_dec_ref(v___x_2688_);
lean_inc(v___x_2733_);
v___x_2736_ = l_Lean_mkConst(v___x_2733_, v___x_2735_);
v_dummy_2737_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__22, &l_Lean_Meta_rwMatcher___closed__22_once, _init_l_Lean_Meta_rwMatcher___closed__22);
lean_inc(v_nargs_2729_);
v___x_2738_ = lean_mk_array(v_nargs_2729_, v_dummy_2737_);
v___x_2739_ = lean_unsigned_to_nat(1u);
v___x_2740_ = lean_nat_sub(v_nargs_2729_, v___x_2739_);
lean_dec(v_nargs_2729_);
v___x_2741_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2217_, v___x_2738_, v___x_2740_);
v___x_2742_ = l_Lean_mkAppN(v___x_2736_, v___x_2741_);
lean_dec_ref(v___x_2741_);
if (v_hasTrace_2728_ == 0)
{
lean_object* v___x_2743_; 
lean_inc(v_a_2221_);
lean_inc_ref(v_a_2220_);
lean_inc(v_a_2219_);
lean_inc_ref(v_a_2218_);
lean_inc_ref(v___x_2742_);
v___x_2743_ = lean_infer_type(v___x_2742_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v_a_2744_; uint8_t v___x_2745_; lean_object* v___x_2746_; 
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
lean_inc(v_a_2744_);
lean_dec_ref(v___x_2743_);
v___x_2745_ = 0;
v___x_2746_ = l_Lean_Meta_forallMetaTelescope(v_a_2744_, v___x_2745_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v_snd_2748_; lean_object* v_fst_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2787_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2747_);
lean_dec_ref(v___x_2746_);
v_snd_2748_ = lean_ctor_get(v_a_2747_, 1);
v_fst_2749_ = lean_ctor_get(v_a_2747_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v_a_2747_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2751_ = v_a_2747_;
v_isShared_2752_ = v_isSharedCheck_2787_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_snd_2748_);
lean_inc(v_fst_2749_);
lean_dec(v_a_2747_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2787_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v_snd_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2785_; 
v_snd_2753_ = lean_ctor_get(v_snd_2748_, 1);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_snd_2748_);
if (v_isSharedCheck_2785_ == 0)
{
lean_object* v_unused_2786_; 
v_unused_2786_ = lean_ctor_get(v_snd_2748_, 0);
lean_dec(v_unused_2786_);
v___x_2755_ = v_snd_2748_;
v_isShared_2756_ = v_isSharedCheck_2785_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_snd_2753_);
lean_dec(v_snd_2748_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2785_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2757_; size_t v_sz_2758_; size_t v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; uint8_t v___x_2763_; 
v___x_2757_ = l_Lean_mkAppN(v___x_2742_, v_fst_2749_);
v_sz_2758_ = lean_array_size(v_fst_2749_);
v___x_2759_ = ((size_t)0ULL);
v___x_2760_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_2758_, v___x_2759_, v_fst_2749_);
v___x_2761_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_2762_ = lean_unsigned_to_nat(4u);
v___x_2763_ = l_Lean_Expr_isAppOfArity(v_snd_2753_, v___x_2761_, v___x_2762_);
if (v___x_2763_ == 0)
{
lean_object* v___x_2764_; lean_object* v___x_2765_; uint8_t v___x_2766_; 
v___x_2764_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_2765_ = lean_unsigned_to_nat(3u);
v___x_2766_ = l_Lean_Expr_isAppOfArity(v_snd_2753_, v___x_2764_, v___x_2765_);
if (v___x_2766_ == 0)
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2770_; 
lean_dec_ref(v___x_2760_);
lean_dec_ref(v___x_2757_);
lean_dec(v_snd_2753_);
lean_dec_ref(v_e_2217_);
v___x_2767_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
lean_inc(v___x_2733_);
v___x_2768_ = l_Lean_MessageData_ofConstName(v___x_2733_, v_hasTrace_2728_);
if (v_isShared_2756_ == 0)
{
lean_ctor_set_tag(v___x_2755_, 7);
lean_ctor_set(v___x_2755_, 1, v___x_2768_);
lean_ctor_set(v___x_2755_, 0, v___x_2767_);
v___x_2770_ = v___x_2755_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2767_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v___x_2768_);
v___x_2770_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
lean_object* v___x_2771_; lean_object* v___x_2773_; 
v___x_2771_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
if (v_isShared_2752_ == 0)
{
lean_ctor_set_tag(v___x_2751_, 7);
lean_ctor_set(v___x_2751_, 1, v___x_2771_);
lean_ctor_set(v___x_2751_, 0, v___x_2770_);
v___x_2773_ = v___x_2751_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2770_);
lean_ctor_set(v_reuseFailAlloc_2776_, 1, v___x_2771_);
v___x_2773_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
lean_object* v___x_2774_; lean_object* v_a_2775_; 
v___x_2774_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2773_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_a_2775_);
lean_dec_ref(v___x_2774_);
v___y_2289_ = v___x_2734_;
v___y_2290_ = v___x_2733_;
v___y_2291_ = v___f_2731_;
v_a_2292_ = v_a_2775_;
goto v___jp_2288_;
}
}
}
else
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
lean_del_object(v___x_2755_);
lean_del_object(v___x_2751_);
v___x_2778_ = l_Lean_Expr_appFn_x21(v_snd_2753_);
v___x_2779_ = l_Lean_Expr_appArg_x21(v___x_2778_);
lean_dec_ref(v___x_2778_);
v___x_2780_ = l_Lean_Expr_appArg_x21(v_snd_2753_);
lean_dec(v_snd_2753_);
v___y_2437_ = v___x_2663_;
v___y_2438_ = v___x_2734_;
v___y_2439_ = v___x_2759_;
v___y_2440_ = v___x_2733_;
v___y_2441_ = v___f_2731_;
v___y_2442_ = v_hasTrace_2728_;
v___y_2443_ = v___x_2757_;
v___y_2444_ = v___x_2760_;
v_fst_2445_ = v_hasTrace_2728_;
v_fst_2446_ = v___x_2779_;
v_snd_2447_ = v___x_2780_;
v___y_2448_ = v_a_2218_;
v___y_2449_ = v_a_2219_;
v___y_2450_ = v_a_2220_;
v___y_2451_ = v_a_2221_;
goto v___jp_2436_;
}
}
else
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
lean_del_object(v___x_2755_);
lean_del_object(v___x_2751_);
v___x_2781_ = l_Lean_Expr_appFn_x21(v_snd_2753_);
v___x_2782_ = l_Lean_Expr_appFn_x21(v___x_2781_);
lean_dec_ref(v___x_2781_);
v___x_2783_ = l_Lean_Expr_appArg_x21(v___x_2782_);
lean_dec_ref(v___x_2782_);
v___x_2784_ = l_Lean_Expr_appArg_x21(v_snd_2753_);
lean_dec(v_snd_2753_);
v___y_2437_ = v___x_2663_;
v___y_2438_ = v___x_2734_;
v___y_2439_ = v___x_2759_;
v___y_2440_ = v___x_2733_;
v___y_2441_ = v___f_2731_;
v___y_2442_ = v_hasTrace_2728_;
v___y_2443_ = v___x_2757_;
v___y_2444_ = v___x_2760_;
v_fst_2445_ = v___x_2663_;
v_fst_2446_ = v___x_2783_;
v_snd_2447_ = v___x_2784_;
v___y_2448_ = v_a_2218_;
v___y_2449_ = v_a_2219_;
v___y_2450_ = v_a_2220_;
v___y_2451_ = v_a_2221_;
goto v___jp_2436_;
}
}
}
}
else
{
lean_object* v_a_2788_; 
lean_dec_ref(v___x_2742_);
lean_dec_ref(v_e_2217_);
v_a_2788_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2788_);
lean_dec_ref(v___x_2746_);
v___y_2289_ = v___x_2734_;
v___y_2290_ = v___x_2733_;
v___y_2291_ = v___f_2731_;
v_a_2292_ = v_a_2788_;
goto v___jp_2288_;
}
}
else
{
lean_object* v_a_2789_; 
lean_dec_ref(v___x_2742_);
lean_dec_ref(v_e_2217_);
v_a_2789_ = lean_ctor_get(v___x_2743_, 0);
lean_inc(v_a_2789_);
lean_dec_ref(v___x_2743_);
v___y_2289_ = v___x_2734_;
v___y_2290_ = v___x_2733_;
v___y_2291_ = v___f_2731_;
v_a_2292_ = v_a_2789_;
goto v___jp_2288_;
}
}
else
{
lean_object* v___x_2790_; lean_object* v___f_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; uint8_t v___x_2794_; 
v___x_2790_ = lean_box(v___y_2662_);
lean_inc_ref(v_e_2217_);
lean_inc(v___x_2733_);
v___f_2791_ = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__1___boxed), 9, 3);
lean_closure_set(v___f_2791_, 0, v___x_2733_);
lean_closure_set(v___f_2791_, 1, v___x_2790_);
lean_closure_set(v___f_2791_, 2, v_e_2217_);
v___x_2792_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1));
v___x_2793_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2794_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2727_, v_options_2726_, v___x_2793_);
if (v___x_2794_ == 0)
{
lean_object* v___x_2795_; uint8_t v___x_2796_; 
v___x_2795_ = l_Lean_trace_profiler;
v___x_2796_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_options_2726_, v___x_2795_);
if (v___x_2796_ == 0)
{
lean_object* v___x_2797_; 
lean_dec_ref(v___f_2791_);
lean_inc(v_a_2221_);
lean_inc_ref(v_a_2220_);
lean_inc(v_a_2219_);
lean_inc_ref(v_a_2218_);
lean_inc_ref(v___x_2742_);
v___x_2797_ = lean_infer_type(v___x_2742_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; uint8_t v___x_2799_; lean_object* v___x_2800_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2798_);
lean_dec_ref(v___x_2797_);
v___x_2799_ = 0;
v___x_2800_ = l_Lean_Meta_forallMetaTelescope(v_a_2798_, v___x_2799_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_a_2801_; lean_object* v_snd_2802_; 
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
lean_inc(v_a_2801_);
lean_dec_ref(v___x_2800_);
v_snd_2802_ = lean_ctor_get(v_a_2801_, 1);
lean_inc(v_snd_2802_);
if (v___x_2794_ == 0)
{
lean_object* v_fst_2803_; lean_object* v_snd_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v_fst_2803_ = lean_ctor_get(v_a_2801_, 0);
lean_inc(v_fst_2803_);
lean_dec(v_a_2801_);
v_snd_2804_ = lean_ctor_get(v_snd_2802_, 1);
lean_inc(v_snd_2804_);
lean_dec(v_snd_2802_);
v___x_2805_ = lean_box(0);
lean_inc(v___x_2733_);
v___x_2806_ = l_Lean_Meta_rwMatcher___lam__4(v___x_2663_, v___x_2742_, v_fst_2803_, v___x_2733_, v___x_2796_, v_e_2217_, v_snd_2804_, v___x_2805_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
lean_dec(v_snd_2804_);
v___y_2296_ = v___x_2734_;
v___y_2297_ = v___x_2733_;
v___y_2298_ = v___f_2731_;
v___y_2299_ = v___x_2806_;
goto v___jp_2295_;
}
else
{
lean_object* v_fst_2807_; lean_object* v_snd_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2821_; 
v_fst_2807_ = lean_ctor_get(v_a_2801_, 0);
lean_inc(v_fst_2807_);
lean_dec(v_a_2801_);
v_snd_2808_ = lean_ctor_get(v_snd_2802_, 1);
v_isSharedCheck_2821_ = !lean_is_exclusive(v_snd_2802_);
if (v_isSharedCheck_2821_ == 0)
{
lean_object* v_unused_2822_; 
v_unused_2822_ = lean_ctor_get(v_snd_2802_, 0);
lean_dec(v_unused_2822_);
v___x_2810_ = v_snd_2802_;
v_isShared_2811_ = v_isSharedCheck_2821_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_snd_2808_);
lean_dec(v_snd_2802_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2821_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2815_; 
v___x_2812_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2808_);
v___x_2813_ = l_Lean_indentExpr(v_snd_2808_);
if (v_isShared_2811_ == 0)
{
lean_ctor_set_tag(v___x_2810_, 7);
lean_ctor_set(v___x_2810_, 1, v___x_2813_);
lean_ctor_set(v___x_2810_, 0, v___x_2812_);
v___x_2815_ = v___x_2810_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v___x_2812_);
lean_ctor_set(v_reuseFailAlloc_2820_, 1, v___x_2813_);
v___x_2815_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
lean_object* v___x_2816_; 
v___x_2816_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2734_, v___x_2815_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; lean_object* v___x_2818_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2817_);
lean_dec_ref(v___x_2816_);
lean_inc(v___x_2733_);
v___x_2818_ = l_Lean_Meta_rwMatcher___lam__4(v___x_2663_, v___x_2742_, v_fst_2807_, v___x_2733_, v___x_2796_, v_e_2217_, v_snd_2808_, v_a_2817_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
lean_dec(v_snd_2808_);
v___y_2296_ = v___x_2734_;
v___y_2297_ = v___x_2733_;
v___y_2298_ = v___f_2731_;
v___y_2299_ = v___x_2818_;
goto v___jp_2295_;
}
else
{
lean_object* v_a_2819_; 
lean_dec(v_snd_2808_);
lean_dec(v_fst_2807_);
lean_dec_ref(v___x_2742_);
lean_dec_ref(v_e_2217_);
v_a_2819_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2819_);
lean_dec_ref(v___x_2816_);
v___y_2289_ = v___x_2734_;
v___y_2290_ = v___x_2733_;
v___y_2291_ = v___f_2731_;
v_a_2292_ = v_a_2819_;
goto v___jp_2288_;
}
}
}
}
}
else
{
lean_object* v_a_2823_; 
lean_dec_ref(v___x_2742_);
lean_dec_ref(v_e_2217_);
v_a_2823_ = lean_ctor_get(v___x_2800_, 0);
lean_inc(v_a_2823_);
lean_dec_ref(v___x_2800_);
v___y_2289_ = v___x_2734_;
v___y_2290_ = v___x_2733_;
v___y_2291_ = v___f_2731_;
v_a_2292_ = v_a_2823_;
goto v___jp_2288_;
}
}
else
{
lean_object* v_a_2824_; 
lean_dec_ref(v___x_2742_);
lean_dec_ref(v_e_2217_);
v_a_2824_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2824_);
lean_dec_ref(v___x_2797_);
v___y_2289_ = v___x_2734_;
v___y_2290_ = v___x_2733_;
v___y_2291_ = v___f_2731_;
v_a_2292_ = v_a_2824_;
goto v___jp_2288_;
}
}
else
{
lean_inc(v___x_2733_);
lean_inc_ref(v___x_2742_);
v___y_2583_ = v___x_2663_;
v___y_2584_ = v___x_2742_;
v___y_2585_ = v___x_2733_;
v___y_2586_ = v___y_2662_;
v___y_2587_ = v___f_2791_;
v___y_2588_ = v___x_2663_;
v___y_2589_ = v___x_2734_;
v___y_2590_ = v___x_2742_;
v___y_2591_ = v___x_2733_;
v___y_2592_ = v_options_2726_;
v___y_2593_ = v___x_2794_;
v___y_2594_ = v___f_2731_;
v___y_2595_ = v___x_2792_;
v___y_2596_ = v_inheritedTraceOptions_2727_;
goto v___jp_2582_;
}
}
else
{
lean_inc(v___x_2733_);
lean_inc_ref(v___x_2742_);
v___y_2583_ = v___x_2663_;
v___y_2584_ = v___x_2742_;
v___y_2585_ = v___x_2733_;
v___y_2586_ = v___y_2662_;
v___y_2587_ = v___f_2791_;
v___y_2588_ = v___x_2663_;
v___y_2589_ = v___x_2734_;
v___y_2590_ = v___x_2742_;
v___y_2591_ = v___x_2733_;
v___y_2592_ = v_options_2726_;
v___y_2593_ = v___x_2794_;
v___y_2594_ = v___f_2731_;
v___y_2595_ = v___x_2792_;
v___y_2596_ = v_inheritedTraceOptions_2727_;
goto v___jp_2582_;
}
}
}
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
lean_dec(v___x_2689_);
lean_dec_ref(v___x_2688_);
lean_del_object(v___x_2667_);
lean_dec_ref(v_e_2217_);
lean_dec(v_altIdx_2216_);
v_a_2825_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2690_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2690_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
}
}
else
{
lean_object* v___x_2834_; 
lean_dec(v_altIdx_2216_);
v___x_2834_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Meta_rwMatcher_spec__14(v_e_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2844_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2837_ = v___x_2834_;
v_isShared_2838_ = v_isSharedCheck_2844_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2834_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2844_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2842_; 
v___x_2839_ = lean_box(0);
v___x_2840_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2840_, 0, v_a_2835_);
lean_ctor_set(v___x_2840_, 1, v___x_2839_);
lean_ctor_set_uint8(v___x_2840_, sizeof(void*)*2, v___x_2663_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 0, v___x_2840_);
v___x_2842_ = v___x_2837_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2840_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
else
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
v_a_2845_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2834_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2834_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___boxed(lean_object* v_altIdx_2857_, lean_object* v_e_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Lean_Meta_rwMatcher(v_altIdx_2857_, v_e_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_);
lean_dec(v_a_2862_);
lean_dec_ref(v_a_2861_);
lean_dec(v_a_2860_);
lean_dec_ref(v_a_2859_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(lean_object* v_mvarId_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v___x_2871_; 
v___x_2871_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_mvarId_2865_, v___y_2867_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___boxed(lean_object* v_mvarId_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(v_mvarId_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v_mvarId_2872_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5(lean_object* v_00_u03b1_2879_, lean_object* v_msg_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v___x_2886_; 
v___x_2886_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v_msg_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___boxed(lean_object* v_00_u03b1_2887_, lean_object* v_msg_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5(v_00_u03b1_2887_, v_msg_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(lean_object* v_00_u03b1_2895_, lean_object* v_x_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
lean_object* v___x_2902_; 
v___x_2902_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___redArg(v_x_2896_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___boxed(lean_object* v_00_u03b1_2903_, lean_object* v_x_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(v_00_u03b1_2903_, v_x_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
return v_res_2910_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(lean_object* v_00_u03b2_2911_, lean_object* v_x_2912_, lean_object* v_x_2913_){
_start:
{
uint8_t v___x_2914_; 
v___x_2914_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_x_2912_, v_x_2913_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2915_, lean_object* v_x_2916_, lean_object* v_x_2917_){
_start:
{
uint8_t v_res_2918_; lean_object* v_r_2919_; 
v_res_2918_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(v_00_u03b2_2915_, v_x_2916_, v_x_2917_);
lean_dec(v_x_2917_);
lean_dec_ref(v_x_2916_);
v_r_2919_ = lean_box(v_res_2918_);
return v_r_2919_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5(lean_object* v_00_u03b2_2920_, lean_object* v_x_2921_, size_t v_x_2922_, lean_object* v_x_2923_){
_start:
{
uint8_t v___x_2924_; 
v___x_2924_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_2921_, v_x_2922_, v_x_2923_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b2_2925_, lean_object* v_x_2926_, lean_object* v_x_2927_, lean_object* v_x_2928_){
_start:
{
size_t v_x_111993__boxed_2929_; uint8_t v_res_2930_; lean_object* v_r_2931_; 
v_x_111993__boxed_2929_ = lean_unbox_usize(v_x_2927_);
lean_dec(v_x_2927_);
v_res_2930_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5(v_00_u03b2_2925_, v_x_2926_, v_x_111993__boxed_2929_, v_x_2928_);
lean_dec(v_x_2928_);
lean_dec_ref(v_x_2926_);
v_r_2931_ = lean_box(v_res_2930_);
return v_r_2931_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20(lean_object* v_00_u03b2_2932_, lean_object* v_keys_2933_, lean_object* v_vals_2934_, lean_object* v_heq_2935_, lean_object* v_i_2936_, lean_object* v_k_2937_){
_start:
{
uint8_t v___x_2938_; 
v___x_2938_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20___redArg(v_keys_2933_, v_i_2936_, v_k_2937_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20___boxed(lean_object* v_00_u03b2_2939_, lean_object* v_keys_2940_, lean_object* v_vals_2941_, lean_object* v_heq_2942_, lean_object* v_i_2943_, lean_object* v_k_2944_){
_start:
{
uint8_t v_res_2945_; lean_object* v_r_2946_; 
v_res_2945_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20(v_00_u03b2_2939_, v_keys_2940_, v_vals_2941_, v_heq_2942_, v_i_2943_, v_k_2944_);
lean_dec(v_k_2944_);
lean_dec_ref(v_vals_2941_);
lean_dec_ref(v_keys_2940_);
v_r_2946_ = lean_box(v_res_2945_);
return v_r_2946_;
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
