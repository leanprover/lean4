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
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_rwMatcher_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_rwMatcher_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_rwMatcher_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_rwMatcher_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_456_; lean_object* v_traceState_457_; lean_object* v_traces_458_; lean_object* v___x_459_; lean_object* v_traceState_460_; lean_object* v_env_461_; lean_object* v_nextMacroScope_462_; lean_object* v_ngen_463_; lean_object* v_auxDeclNGen_464_; lean_object* v_cache_465_; lean_object* v_messages_466_; lean_object* v_infoState_467_; lean_object* v_snapshotTasks_468_; lean_object* v_newDecls_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_488_; 
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
v_newDecls_469_ = lean_ctor_get(v___x_459_, 9);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_488_ == 0)
{
v___x_471_ = v___x_459_;
v_isShared_472_ = v_isSharedCheck_488_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_newDecls_469_);
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
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_488_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
uint64_t v_tid_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_486_; 
v_tid_473_ = lean_ctor_get_uint64(v_traceState_460_, sizeof(void*)*1);
v_isSharedCheck_486_ = !lean_is_exclusive(v_traceState_460_);
if (v_isSharedCheck_486_ == 0)
{
lean_object* v_unused_487_; 
v_unused_487_ = lean_ctor_get(v_traceState_460_, 0);
lean_dec(v_unused_487_);
v___x_475_ = v_traceState_460_;
v_isShared_476_ = v_isSharedCheck_486_;
goto v_resetjp_474_;
}
else
{
lean_dec(v_traceState_460_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_486_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_477_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__1);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v___x_477_);
v___x_479_ = v___x_475_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_477_);
lean_ctor_set_uint64(v_reuseFailAlloc_485_, sizeof(void*)*1, v_tid_473_);
v___x_479_ = v_reuseFailAlloc_485_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
lean_object* v___x_481_; 
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 4, v___x_479_);
v___x_481_ = v___x_471_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_env_461_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_nextMacroScope_462_);
lean_ctor_set(v_reuseFailAlloc_484_, 2, v_ngen_463_);
lean_ctor_set(v_reuseFailAlloc_484_, 3, v_auxDeclNGen_464_);
lean_ctor_set(v_reuseFailAlloc_484_, 4, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_484_, 5, v_cache_465_);
lean_ctor_set(v_reuseFailAlloc_484_, 6, v_messages_466_);
lean_ctor_set(v_reuseFailAlloc_484_, 7, v_infoState_467_);
lean_ctor_set(v_reuseFailAlloc_484_, 8, v_snapshotTasks_468_);
lean_ctor_set(v_reuseFailAlloc_484_, 9, v_newDecls_469_);
v___x_481_ = v_reuseFailAlloc_484_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_st_ref_set(v___y_454_, v___x_481_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v_traces_458_);
return v___x_483_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___boxed(lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg(v___y_489_);
lean_dec(v___y_489_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9(lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg(v___y_495_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___boxed(lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9(v___y_498_, v___y_499_, v___y_500_, v___y_501_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
return v_res_503_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(lean_object* v_opts_504_, lean_object* v_opt_505_){
_start:
{
lean_object* v_name_506_; lean_object* v_defValue_507_; lean_object* v_map_508_; lean_object* v___x_509_; 
v_name_506_ = lean_ctor_get(v_opt_505_, 0);
v_defValue_507_ = lean_ctor_get(v_opt_505_, 1);
v_map_508_ = lean_ctor_get(v_opts_504_, 0);
v___x_509_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_508_, v_name_506_);
if (lean_obj_tag(v___x_509_) == 0)
{
uint8_t v___x_510_; 
v___x_510_ = lean_unbox(v_defValue_507_);
return v___x_510_;
}
else
{
lean_object* v_val_511_; 
v_val_511_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_val_511_);
lean_dec_ref(v___x_509_);
if (lean_obj_tag(v_val_511_) == 1)
{
uint8_t v_v_512_; 
v_v_512_ = lean_ctor_get_uint8(v_val_511_, 0);
lean_dec_ref(v_val_511_);
return v_v_512_;
}
else
{
uint8_t v___x_513_; 
lean_dec(v_val_511_);
v___x_513_ = lean_unbox(v_defValue_507_);
return v___x_513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10___boxed(lean_object* v_opts_514_, lean_object* v_opt_515_){
_start:
{
uint8_t v_res_516_; lean_object* v_r_517_; 
v_res_516_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_opts_514_, v_opt_515_);
lean_dec_ref(v_opt_515_);
lean_dec_ref(v_opts_514_);
v_r_517_ = lean_box(v_res_516_);
return v_r_517_;
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
uint8_t v___x_107911__boxed_538_; lean_object* v_res_539_; 
v___x_107911__boxed_538_ = lean_unbox(v___x_531_);
v_res_539_ = l_Lean_Meta_rwMatcher___lam__0(v_e_530_, v___x_107911__boxed_538_, v_____r_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
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
uint8_t v___y_107953__boxed_572_; lean_object* v_res_573_; 
v___y_107953__boxed_572_ = lean_unbox(v___y_564_);
v_res_573_ = l_Lean_Meta_rwMatcher___lam__1(v___x_563_, v___y_107953__boxed_572_, v_e_565_, v_x_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec_ref(v_x_566_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(size_t v_sz_574_, size_t v_i_575_, lean_object* v_bs_576_){
_start:
{
uint8_t v___x_577_; 
v___x_577_ = lean_usize_dec_lt(v_i_575_, v_sz_574_);
if (v___x_577_ == 0)
{
return v_bs_576_;
}
else
{
lean_object* v_v_578_; lean_object* v___x_579_; lean_object* v_bs_x27_580_; lean_object* v___x_581_; size_t v___x_582_; size_t v___x_583_; lean_object* v___x_584_; 
v_v_578_ = lean_array_uget(v_bs_576_, v_i_575_);
v___x_579_ = lean_unsigned_to_nat(0u);
v_bs_x27_580_ = lean_array_uset(v_bs_576_, v_i_575_, v___x_579_);
v___x_581_ = l_Lean_Expr_mvarId_x21(v_v_578_);
lean_dec(v_v_578_);
v___x_582_ = ((size_t)1ULL);
v___x_583_ = lean_usize_add(v_i_575_, v___x_582_);
v___x_584_ = lean_array_uset(v_bs_x27_580_, v_i_575_, v___x_581_);
v_i_575_ = v___x_583_;
v_bs_576_ = v___x_584_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3___boxed(lean_object* v_sz_586_, lean_object* v_i_587_, lean_object* v_bs_588_){
_start:
{
size_t v_sz_boxed_589_; size_t v_i_boxed_590_; lean_object* v_res_591_; 
v_sz_boxed_589_ = lean_unbox_usize(v_sz_586_);
lean_dec(v_sz_586_);
v_i_boxed_590_ = lean_unbox_usize(v_i_587_);
lean_dec(v_i_587_);
v_res_591_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_boxed_589_, v_i_boxed_590_, v_bs_588_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(lean_object* v_msgData_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v___x_598_; lean_object* v_env_599_; lean_object* v___x_600_; lean_object* v_mctx_601_; lean_object* v_lctx_602_; lean_object* v_options_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_598_ = lean_st_ref_get(v___y_596_);
v_env_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc_ref(v_env_599_);
lean_dec(v___x_598_);
v___x_600_ = lean_st_ref_get(v___y_594_);
v_mctx_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc_ref(v_mctx_601_);
lean_dec(v___x_600_);
v_lctx_602_ = lean_ctor_get(v___y_593_, 2);
v_options_603_ = lean_ctor_get(v___y_595_, 2);
lean_inc_ref(v_options_603_);
lean_inc_ref(v_lctx_602_);
v___x_604_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_604_, 0, v_env_599_);
lean_ctor_set(v___x_604_, 1, v_mctx_601_);
lean_ctor_set(v___x_604_, 2, v_lctx_602_);
lean_ctor_set(v___x_604_, 3, v_options_603_);
v___x_605_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v_msgData_592_);
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3___boxed(lean_object* v_msgData_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msgData_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(lean_object* v_msg_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v_ref_620_; lean_object* v___x_621_; lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_630_; 
v_ref_620_ = lean_ctor_get(v___y_617_, 5);
v___x_621_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
v_a_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_630_ == 0)
{
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_630_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_630_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v___x_628_; 
lean_inc(v_ref_620_);
v___x_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_626_, 0, v_ref_620_);
lean_ctor_set(v___x_626_, 1, v_a_622_);
if (v_isShared_625_ == 0)
{
lean_ctor_set_tag(v___x_624_, 1);
lean_ctor_set(v___x_624_, 0, v___x_626_);
v___x_628_ = v___x_624_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg___boxed(lean_object* v_msg_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v_msg_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
return v_res_637_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20___redArg(lean_object* v_keys_638_, lean_object* v_i_639_, lean_object* v_k_640_){
_start:
{
lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_641_ = lean_array_get_size(v_keys_638_);
v___x_642_ = lean_nat_dec_lt(v_i_639_, v___x_641_);
if (v___x_642_ == 0)
{
lean_dec(v_i_639_);
return v___x_642_;
}
else
{
lean_object* v_k_x27_643_; uint8_t v___x_644_; 
v_k_x27_643_ = lean_array_fget_borrowed(v_keys_638_, v_i_639_);
v___x_644_ = l_Lean_instBEqMVarId_beq(v_k_640_, v_k_x27_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_unsigned_to_nat(1u);
v___x_646_ = lean_nat_add(v_i_639_, v___x_645_);
lean_dec(v_i_639_);
v_i_639_ = v___x_646_;
goto _start;
}
else
{
lean_dec(v_i_639_);
return v___x_644_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20___redArg___boxed(lean_object* v_keys_648_, lean_object* v_i_649_, lean_object* v_k_650_){
_start:
{
uint8_t v_res_651_; lean_object* v_r_652_; 
v_res_651_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20___redArg(v_keys_648_, v_i_649_, v_k_650_);
lean_dec(v_k_650_);
lean_dec_ref(v_keys_648_);
v_r_652_ = lean_box(v_res_651_);
return v_r_652_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__0(void){
_start:
{
size_t v___x_653_; size_t v___x_654_; size_t v___x_655_; 
v___x_653_ = ((size_t)5ULL);
v___x_654_ = ((size_t)1ULL);
v___x_655_ = lean_usize_shift_left(v___x_654_, v___x_653_);
return v___x_655_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_656_; size_t v___x_657_; size_t v___x_658_; 
v___x_656_ = ((size_t)1ULL);
v___x_657_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__0);
v___x_658_ = lean_usize_sub(v___x_657_, v___x_656_);
return v___x_658_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(lean_object* v_x_659_, size_t v_x_660_, lean_object* v_x_661_){
_start:
{
if (lean_obj_tag(v_x_659_) == 0)
{
lean_object* v_es_662_; lean_object* v___x_663_; size_t v___x_664_; size_t v___x_665_; size_t v___x_666_; lean_object* v_j_667_; lean_object* v___x_668_; 
v_es_662_ = lean_ctor_get(v_x_659_, 0);
v___x_663_ = lean_box(2);
v___x_664_ = ((size_t)5ULL);
v___x_665_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___closed__1);
v___x_666_ = lean_usize_land(v_x_660_, v___x_665_);
v_j_667_ = lean_usize_to_nat(v___x_666_);
v___x_668_ = lean_array_get_borrowed(v___x_663_, v_es_662_, v_j_667_);
lean_dec(v_j_667_);
switch(lean_obj_tag(v___x_668_))
{
case 0:
{
lean_object* v_key_669_; uint8_t v___x_670_; 
v_key_669_ = lean_ctor_get(v___x_668_, 0);
v___x_670_ = l_Lean_instBEqMVarId_beq(v_x_661_, v_key_669_);
return v___x_670_;
}
case 1:
{
lean_object* v_node_671_; size_t v___x_672_; 
v_node_671_ = lean_ctor_get(v___x_668_, 0);
v___x_672_ = lean_usize_shift_right(v_x_660_, v___x_664_);
v_x_659_ = v_node_671_;
v_x_660_ = v___x_672_;
goto _start;
}
default: 
{
uint8_t v___x_674_; 
v___x_674_ = 0;
return v___x_674_;
}
}
}
else
{
lean_object* v_ks_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v_ks_675_ = lean_ctor_get(v_x_659_, 0);
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20___redArg(v_ks_675_, v___x_676_, v_x_661_);
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_678_, lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
size_t v_x_108098__boxed_681_; uint8_t v_res_682_; lean_object* v_r_683_; 
v_x_108098__boxed_681_ = lean_unbox_usize(v_x_679_);
lean_dec(v_x_679_);
v_res_682_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_678_, v_x_108098__boxed_681_, v_x_680_);
lean_dec(v_x_680_);
lean_dec_ref(v_x_678_);
v_r_683_ = lean_box(v_res_682_);
return v_r_683_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(lean_object* v_x_684_, lean_object* v_x_685_){
_start:
{
uint64_t v___x_686_; size_t v___x_687_; uint8_t v___x_688_; 
v___x_686_ = l_Lean_instHashableMVarId_hash(v_x_685_);
v___x_687_ = lean_uint64_to_usize(v___x_686_);
v___x_688_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_684_, v___x_687_, v_x_685_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg___boxed(lean_object* v_x_689_, lean_object* v_x_690_){
_start:
{
uint8_t v_res_691_; lean_object* v_r_692_; 
v_res_691_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_x_689_, v_x_690_);
lean_dec(v_x_690_);
lean_dec_ref(v_x_689_);
v_r_692_ = lean_box(v_res_691_);
return v_r_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(lean_object* v_mvarId_693_, lean_object* v___y_694_){
_start:
{
lean_object* v___x_696_; lean_object* v_mctx_697_; lean_object* v_eAssignment_698_; uint8_t v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_696_ = lean_st_ref_get(v___y_694_);
v_mctx_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc_ref(v_mctx_697_);
lean_dec(v___x_696_);
v_eAssignment_698_ = lean_ctor_get(v_mctx_697_, 8);
lean_inc_ref(v_eAssignment_698_);
lean_dec_ref(v_mctx_697_);
v___x_699_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_eAssignment_698_, v_mvarId_693_);
lean_dec_ref(v_eAssignment_698_);
v___x_700_ = lean_box(v___x_699_);
v___x_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg___boxed(lean_object* v_mvarId_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_mvarId_702_, v___y_703_);
lean_dec(v___y_703_);
lean_dec(v_mvarId_702_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12(uint8_t v___x_706_, lean_object* v_as_707_, size_t v_i_708_, size_t v_stop_709_, lean_object* v_b_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v_a_717_; uint8_t v___x_721_; 
v___x_721_ = lean_usize_dec_eq(v_i_708_, v_stop_709_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; uint8_t v_a_726_; lean_object* v___x_727_; 
v___x_722_ = lean_array_uget_borrowed(v_as_707_, v_i_708_);
v___x_727_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v___x_722_, v___y_712_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; uint8_t v___x_729_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_728_);
lean_dec_ref(v___x_727_);
v___x_729_ = lean_unbox(v_a_728_);
lean_dec(v_a_728_);
if (v___x_729_ == 0)
{
goto v___jp_723_;
}
else
{
v_a_726_ = v___x_706_;
goto v___jp_725_;
}
}
else
{
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_730_; uint8_t v___x_731_; 
v_a_730_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_730_);
lean_dec_ref(v___x_727_);
v___x_731_ = lean_unbox(v_a_730_);
lean_dec(v_a_730_);
v_a_726_ = v___x_731_;
goto v___jp_725_;
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec_ref(v_b_710_);
v_a_732_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_727_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_727_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
v___jp_723_:
{
lean_object* v___x_724_; 
lean_inc(v___x_722_);
v___x_724_ = lean_array_push(v_b_710_, v___x_722_);
v_a_717_ = v___x_724_;
goto v___jp_716_;
}
v___jp_725_:
{
if (v_a_726_ == 0)
{
v_a_717_ = v_b_710_;
goto v___jp_716_;
}
else
{
goto v___jp_723_;
}
}
}
else
{
lean_object* v___x_740_; 
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v_b_710_);
return v___x_740_;
}
v___jp_716_:
{
size_t v___x_718_; size_t v___x_719_; 
v___x_718_ = ((size_t)1ULL);
v___x_719_ = lean_usize_add(v_i_708_, v___x_718_);
v_i_708_ = v___x_719_;
v_b_710_ = v_a_717_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12___boxed(lean_object* v___x_741_, lean_object* v_as_742_, lean_object* v_i_743_, lean_object* v_stop_744_, lean_object* v_b_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
uint8_t v___x_108170__boxed_751_; size_t v_i_boxed_752_; size_t v_stop_boxed_753_; lean_object* v_res_754_; 
v___x_108170__boxed_751_ = lean_unbox(v___x_741_);
v_i_boxed_752_ = lean_unbox_usize(v_i_743_);
lean_dec(v_i_743_);
v_stop_boxed_753_ = lean_unbox_usize(v_stop_744_);
lean_dec(v_stop_744_);
v_res_754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12(v___x_108170__boxed_751_, v_as_742_, v_i_boxed_752_, v_stop_boxed_753_, v_b_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec_ref(v_as_742_);
return v_res_754_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__0));
v___x_757_ = l_Lean_stringToMessageData(v___x_756_);
return v___x_757_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__2));
v___x_760_ = l_Lean_stringToMessageData(v___x_759_);
return v___x_760_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__4));
v___x_763_ = l_Lean_stringToMessageData(v___x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(lean_object* v_as_764_, size_t v_sz_765_, size_t v_i_766_, lean_object* v_b_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v_a_774_; uint8_t v___x_778_; 
v___x_778_ = lean_usize_dec_lt(v_i_766_, v_sz_765_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; 
v___x_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_779_, 0, v_b_767_);
return v___x_779_;
}
else
{
lean_object* v_a_780_; lean_object* v___x_781_; 
v_a_780_ = lean_array_uget_borrowed(v_as_764_, v_i_766_);
v___x_781_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_a_780_, v___y_769_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_783_; lean_object* v___y_785_; lean_object* v___y_787_; lean_object* v___y_788_; uint8_t v___y_789_; lean_object* v___y_805_; lean_object* v___y_807_; lean_object* v___y_808_; uint8_t v___y_809_; lean_object* v___y_825_; uint8_t v___x_826_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref(v___x_781_);
v___x_783_ = lean_box(0);
v___x_826_ = lean_unbox(v_a_782_);
lean_dec(v_a_782_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; 
lean_inc(v_a_780_);
v___x_827_ = l_Lean_MVarId_getType(v_a_780_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; uint8_t v___x_829_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc_n(v_a_828_, 2);
lean_dec_ref(v___x_827_);
v___x_829_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_a_828_);
if (v___x_829_ == 0)
{
uint8_t v___x_830_; 
v___x_830_ = l_Lean_Expr_isEq(v_a_828_);
if (v___x_830_ == 0)
{
uint8_t v___x_831_; 
v___x_831_ = l_Lean_Expr_isHEq(v_a_828_);
lean_dec(v_a_828_);
if (v___x_831_ == 0)
{
v_a_774_ = v___x_783_;
goto v___jp_773_;
}
else
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_Meta_saveState___redArg(v___y_769_, v___y_771_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v___x_834_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
lean_dec_ref(v___x_832_);
lean_inc(v_a_780_);
v___x_834_ = l_Lean_MVarId_assumption(v_a_780_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_dec(v_a_833_);
v___y_805_ = v___x_834_;
goto v___jp_804_;
}
else
{
lean_object* v_a_835_; uint8_t v___y_837_; uint8_t v___x_853_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_a_835_);
v___x_853_ = l_Lean_Exception_isInterrupt(v_a_835_);
if (v___x_853_ == 0)
{
uint8_t v___x_854_; 
v___x_854_ = l_Lean_Exception_isRuntime(v_a_835_);
v___y_837_ = v___x_854_;
goto v___jp_836_;
}
else
{
lean_dec(v_a_835_);
v___y_837_ = v___x_853_;
goto v___jp_836_;
}
v___jp_836_:
{
if (v___y_837_ == 0)
{
lean_object* v___x_838_; 
lean_dec_ref(v___x_834_);
v___x_838_ = l_Lean_Meta_SavedState_restore___redArg(v_a_833_, v___y_769_, v___y_771_);
lean_dec(v_a_833_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v___x_839_; 
lean_dec_ref(v___x_838_);
v___x_839_ = l_Lean_Meta_saveState___redArg(v___y_769_, v___y_771_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_841_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
lean_dec_ref(v___x_839_);
lean_inc(v_a_780_);
v___x_841_ = l_Lean_MVarId_hrefl(v_a_780_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_dec(v_a_840_);
v___y_805_ = v___x_841_;
goto v___jp_804_;
}
else
{
lean_object* v_a_842_; uint8_t v___x_843_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_842_);
v___x_843_ = l_Lean_Exception_isInterrupt(v_a_842_);
if (v___x_843_ == 0)
{
uint8_t v___x_844_; 
v___x_844_ = l_Lean_Exception_isRuntime(v_a_842_);
v___y_807_ = v_a_840_;
v___y_808_ = v___x_841_;
v___y_809_ = v___x_844_;
goto v___jp_806_;
}
else
{
lean_dec(v_a_842_);
v___y_807_ = v_a_840_;
v___y_808_ = v___x_841_;
v___y_809_ = v___x_843_;
goto v___jp_806_;
}
}
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
v_a_845_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_839_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_839_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
else
{
v___y_805_ = v___x_838_;
goto v___jp_804_;
}
}
else
{
lean_dec(v_a_833_);
v___y_805_ = v___x_834_;
goto v___jp_804_;
}
}
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
v_a_855_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_832_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_832_);
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
}
else
{
lean_object* v___x_863_; 
lean_dec(v_a_828_);
v___x_863_ = l_Lean_Meta_saveState___redArg(v___y_769_, v___y_771_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_865_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref(v___x_863_);
lean_inc(v_a_780_);
v___x_865_ = l_Lean_MVarId_assumption(v_a_780_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_dec(v_a_864_);
v___y_785_ = v___x_865_;
goto v___jp_784_;
}
else
{
lean_object* v_a_866_; uint8_t v___y_868_; uint8_t v___x_884_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_866_);
v___x_884_ = l_Lean_Exception_isInterrupt(v_a_866_);
if (v___x_884_ == 0)
{
uint8_t v___x_885_; 
v___x_885_ = l_Lean_Exception_isRuntime(v_a_866_);
v___y_868_ = v___x_885_;
goto v___jp_867_;
}
else
{
lean_dec(v_a_866_);
v___y_868_ = v___x_884_;
goto v___jp_867_;
}
v___jp_867_:
{
if (v___y_868_ == 0)
{
lean_object* v___x_869_; 
lean_dec_ref(v___x_865_);
v___x_869_ = l_Lean_Meta_SavedState_restore___redArg(v_a_864_, v___y_769_, v___y_771_);
lean_dec(v_a_864_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v___x_870_; 
lean_dec_ref(v___x_869_);
v___x_870_ = l_Lean_Meta_saveState___redArg(v___y_769_, v___y_771_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_872_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_a_871_);
lean_dec_ref(v___x_870_);
lean_inc(v_a_780_);
v___x_872_ = l_Lean_MVarId_refl(v_a_780_, v___x_830_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_dec(v_a_871_);
v___y_785_ = v___x_872_;
goto v___jp_784_;
}
else
{
lean_object* v_a_873_; uint8_t v___x_874_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_a_873_);
v___x_874_ = l_Lean_Exception_isInterrupt(v_a_873_);
if (v___x_874_ == 0)
{
uint8_t v___x_875_; 
v___x_875_ = l_Lean_Exception_isRuntime(v_a_873_);
v___y_787_ = v_a_871_;
v___y_788_ = v___x_872_;
v___y_789_ = v___x_875_;
goto v___jp_786_;
}
else
{
lean_dec(v_a_873_);
v___y_787_ = v_a_871_;
v___y_788_ = v___x_872_;
v___y_789_ = v___x_874_;
goto v___jp_786_;
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
v_a_876_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_870_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_870_);
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
v___y_785_ = v___x_869_;
goto v___jp_784_;
}
}
else
{
lean_dec(v_a_864_);
v___y_785_ = v___x_865_;
goto v___jp_784_;
}
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
v_a_886_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_863_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_863_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
else
{
lean_object* v___x_894_; 
lean_dec(v_a_828_);
v___x_894_ = l_Lean_Meta_saveState___redArg(v___y_769_, v___y_771_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_896_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
lean_dec_ref(v___x_894_);
lean_inc(v_a_780_);
v___x_896_ = l_Lean_MVarId_assumption(v_a_780_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_dec(v_a_895_);
v___y_825_ = v___x_896_;
goto v___jp_824_;
}
else
{
lean_object* v_a_897_; uint8_t v___y_899_; uint8_t v___x_914_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_897_);
v___x_914_ = l_Lean_Exception_isInterrupt(v_a_897_);
if (v___x_914_ == 0)
{
uint8_t v___x_915_; 
v___x_915_ = l_Lean_Exception_isRuntime(v_a_897_);
v___y_899_ = v___x_915_;
goto v___jp_898_;
}
else
{
lean_dec(v_a_897_);
v___y_899_ = v___x_914_;
goto v___jp_898_;
}
v___jp_898_:
{
if (v___y_899_ == 0)
{
lean_object* v___x_900_; 
lean_dec_ref(v___x_896_);
v___x_900_ = l_Lean_Meta_SavedState_restore___redArg(v_a_895_, v___y_769_, v___y_771_);
lean_dec(v_a_895_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_912_; 
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_912_ == 0)
{
lean_object* v_unused_913_; 
v_unused_913_ = lean_ctor_get(v___x_900_, 0);
lean_dec(v_unused_913_);
v___x_902_ = v___x_900_;
v_isShared_903_ = v_isSharedCheck_912_;
goto v_resetjp_901_;
}
else
{
lean_dec(v___x_900_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_912_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_904_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5);
lean_inc(v_a_780_);
if (v_isShared_903_ == 0)
{
lean_ctor_set_tag(v___x_902_, 1);
lean_ctor_set(v___x_902_, 0, v_a_780_);
v___x_906_ = v___x_902_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_780_);
v___x_906_ = v_reuseFailAlloc_911_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_904_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_909_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
v___y_825_ = v___x_910_;
goto v___jp_824_;
}
}
}
else
{
v___y_825_ = v___x_900_;
goto v___jp_824_;
}
}
else
{
lean_dec(v_a_895_);
v___y_825_ = v___x_896_;
goto v___jp_824_;
}
}
}
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
v_a_916_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_894_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_894_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
v_a_924_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_827_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_827_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
else
{
v_a_774_ = v___x_783_;
goto v___jp_773_;
}
v___jp_784_:
{
if (lean_obj_tag(v___y_785_) == 0)
{
lean_dec_ref(v___y_785_);
v_a_774_ = v___x_783_;
goto v___jp_773_;
}
else
{
return v___y_785_;
}
}
v___jp_786_:
{
if (v___y_789_ == 0)
{
lean_object* v___x_790_; 
lean_dec_ref(v___y_788_);
v___x_790_ = l_Lean_Meta_SavedState_restore___redArg(v___y_787_, v___y_769_, v___y_771_);
lean_dec_ref(v___y_787_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_802_; 
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v___x_790_, 0);
lean_dec(v_unused_803_);
v___x_792_ = v___x_790_;
v_isShared_793_ = v_isSharedCheck_802_;
goto v_resetjp_791_;
}
else
{
lean_dec(v___x_790_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_802_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_794_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1);
lean_inc(v_a_780_);
if (v_isShared_793_ == 0)
{
lean_ctor_set_tag(v___x_792_, 1);
lean_ctor_set(v___x_792_, 0, v_a_780_);
v___x_796_ = v___x_792_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_780_);
v___x_796_ = v_reuseFailAlloc_801_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_794_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_797_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_799_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
v___y_785_ = v___x_800_;
goto v___jp_784_;
}
}
}
else
{
v___y_785_ = v___x_790_;
goto v___jp_784_;
}
}
else
{
lean_dec_ref(v___y_787_);
v___y_785_ = v___y_788_;
goto v___jp_784_;
}
}
v___jp_804_:
{
if (lean_obj_tag(v___y_805_) == 0)
{
lean_dec_ref(v___y_805_);
v_a_774_ = v___x_783_;
goto v___jp_773_;
}
else
{
return v___y_805_;
}
}
v___jp_806_:
{
if (v___y_809_ == 0)
{
lean_object* v___x_810_; 
lean_dec_ref(v___y_808_);
v___x_810_ = l_Lean_Meta_SavedState_restore___redArg(v___y_807_, v___y_769_, v___y_771_);
lean_dec_ref(v___y_807_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_822_; 
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v___x_810_, 0);
lean_dec(v_unused_823_);
v___x_812_ = v___x_810_;
v_isShared_813_ = v_isSharedCheck_822_;
goto v_resetjp_811_;
}
else
{
lean_dec(v___x_810_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_822_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_814_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1);
lean_inc(v_a_780_);
if (v_isShared_813_ == 0)
{
lean_ctor_set_tag(v___x_812_, 1);
lean_ctor_set(v___x_812_, 0, v_a_780_);
v___x_816_ = v___x_812_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_780_);
v___x_816_ = v_reuseFailAlloc_821_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_814_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_817_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_819_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
v___y_805_ = v___x_820_;
goto v___jp_804_;
}
}
}
else
{
v___y_805_ = v___x_810_;
goto v___jp_804_;
}
}
else
{
lean_dec_ref(v___y_807_);
v___y_805_ = v___y_808_;
goto v___jp_804_;
}
}
v___jp_824_:
{
if (lean_obj_tag(v___y_825_) == 0)
{
lean_dec_ref(v___y_825_);
v_a_774_ = v___x_783_;
goto v___jp_773_;
}
else
{
return v___y_825_;
}
}
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
v_a_932_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_781_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_781_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
v___jp_773_:
{
size_t v___x_775_; size_t v___x_776_; 
v___x_775_ = ((size_t)1ULL);
v___x_776_ = lean_usize_add(v_i_766_, v___x_775_);
v_i_766_ = v___x_776_;
v_b_767_ = v_a_774_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___boxed(lean_object* v_as_940_, lean_object* v_sz_941_, lean_object* v_i_942_, lean_object* v_b_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
size_t v_sz_boxed_949_; size_t v_i_boxed_950_; lean_object* v_res_951_; 
v_sz_boxed_949_ = lean_unbox_usize(v_sz_941_);
lean_dec(v_sz_941_);
v_i_boxed_950_ = lean_unbox_usize(v_i_942_);
lean_dec(v_i_942_);
v_res_951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v_as_940_, v_sz_boxed_949_, v_i_boxed_950_, v_b_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec_ref(v_as_940_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
if (lean_obj_tag(v_a_952_) == 0)
{
lean_object* v___x_954_; 
v___x_954_ = l_List_reverse___redArg(v_a_953_);
return v___x_954_;
}
else
{
lean_object* v_head_955_; lean_object* v_tail_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_965_; 
v_head_955_ = lean_ctor_get(v_a_952_, 0);
v_tail_956_ = lean_ctor_get(v_a_952_, 1);
v_isSharedCheck_965_ = !lean_is_exclusive(v_a_952_);
if (v_isSharedCheck_965_ == 0)
{
v___x_958_ = v_a_952_;
v_isShared_959_ = v_isSharedCheck_965_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_tail_956_);
lean_inc(v_head_955_);
lean_dec(v_a_952_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_965_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v___x_962_; 
v___x_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_960_, 0, v_head_955_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 1, v_a_953_);
lean_ctor_set(v___x_958_, 0, v___x_960_);
v___x_962_ = v___x_958_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_a_953_);
v___x_962_ = v_reuseFailAlloc_964_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
v_a_952_ = v_tail_956_;
v_a_953_ = v___x_962_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__1(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__0));
v___x_968_ = l_Lean_stringToMessageData(v___x_967_);
return v___x_968_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__3(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__2));
v___x_971_ = l_Lean_stringToMessageData(v___x_970_);
return v___x_971_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__5(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__4));
v___x_974_ = l_Lean_stringToMessageData(v___x_973_);
return v___x_974_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__7(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__6));
v___x_977_ = l_Lean_stringToMessageData(v___x_976_);
return v___x_977_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__9(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__8));
v___x_980_ = l_Lean_stringToMessageData(v___x_979_);
return v___x_980_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__12(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__11));
v___x_985_ = l_Lean_stringToMessageData(v___x_984_);
return v___x_985_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__14(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__13));
v___x_988_ = l_Lean_stringToMessageData(v___x_987_);
return v___x_988_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__16(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__15));
v___x_991_ = l_Lean_stringToMessageData(v___x_990_);
return v___x_991_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__22(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__21));
v___x_1000_ = l_Lean_stringToMessageData(v___x_999_);
return v___x_1000_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__24(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__23));
v___x_1003_ = l_Lean_stringToMessageData(v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2(uint8_t v___x_1004_, lean_object* v___x_1005_, lean_object* v_fst_1006_, lean_object* v___x_1007_, uint8_t v___x_1008_, lean_object* v_e_1009_, lean_object* v_snd_1010_, lean_object* v_____r_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v___y_1018_; lean_object* v_proof_1019_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1036_; lean_object* v___y_1037_; lean_object* v___y_1038_; lean_object* v___y_1039_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; uint8_t v___y_1044_; lean_object* v___x_1056_; lean_object* v___y_1058_; uint8_t v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; uint8_t v___y_1079_; lean_object* v_a_1080_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; uint8_t v___y_1109_; lean_object* v___y_1110_; size_t v_sz_1120_; size_t v___x_1121_; lean_object* v___x_1122_; lean_object* v___y_1124_; uint8_t v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; uint8_t v___y_1157_; uint8_t v_fst_1181_; lean_object* v_fst_1182_; lean_object* v_snd_1183_; lean_object* v___x_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1056_ = l_Lean_mkAppN(v___x_1005_, v_fst_1006_);
v_sz_1120_ = lean_array_size(v_fst_1006_);
v___x_1121_ = ((size_t)0ULL);
v___x_1122_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_1120_, v___x_1121_, v_fst_1006_);
v___x_1195_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1196_ = lean_unsigned_to_nat(4u);
v___x_1197_ = l_Lean_Expr_isAppOfArity(v_snd_1010_, v___x_1195_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; 
v___x_1198_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1199_ = lean_unsigned_to_nat(3u);
v___x_1200_ = l_Lean_Expr_isAppOfArity(v_snd_1010_, v___x_1198_, v___x_1199_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
lean_dec_ref(v___x_1122_);
lean_dec_ref(v___x_1056_);
lean_dec_ref(v_e_1009_);
v___x_1201_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1202_ = l_Lean_MessageData_ofConstName(v___x_1007_, v___x_1008_);
v___x_1203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1201_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
v___x_1204_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1203_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1205_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1206_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1206_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
else
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1215_ = l_Lean_Expr_appFn_x21(v_snd_1010_);
v___x_1216_ = l_Lean_Expr_appArg_x21(v___x_1215_);
lean_dec_ref(v___x_1215_);
v___x_1217_ = l_Lean_Expr_appArg_x21(v_snd_1010_);
v_fst_1181_ = v___x_1008_;
v_fst_1182_ = v___x_1216_;
v_snd_1183_ = v___x_1217_;
goto v___jp_1180_;
}
}
else
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1218_ = l_Lean_Expr_appFn_x21(v_snd_1010_);
v___x_1219_ = l_Lean_Expr_appFn_x21(v___x_1218_);
lean_dec_ref(v___x_1218_);
v___x_1220_ = l_Lean_Expr_appArg_x21(v___x_1219_);
lean_dec_ref(v___x_1219_);
v___x_1221_ = l_Lean_Expr_appArg_x21(v_snd_1010_);
v_fst_1181_ = v___x_1004_;
v_fst_1182_ = v___x_1220_;
v_snd_1183_ = v___x_1221_;
goto v___jp_1180_;
}
v___jp_1017_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1020_, 0, v_proof_1019_);
v___x_1021_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1021_, 0, v___y_1018_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
lean_ctor_set_uint8(v___x_1021_, sizeof(void*)*2, v___x_1004_);
v___x_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
return v___x_1022_;
}
v___jp_1023_:
{
if (lean_obj_tag(v___y_1025_) == 0)
{
lean_object* v_a_1026_; 
v_a_1026_ = lean_ctor_get(v___y_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref(v___y_1025_);
v___y_1018_ = v___y_1024_;
v_proof_1019_ = v_a_1026_;
goto v___jp_1017_;
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec_ref(v___y_1024_);
v_a_1027_ = lean_ctor_get(v___y_1025_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___y_1025_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___y_1025_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___y_1025_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
v___jp_1035_:
{
if (v___y_1044_ == 0)
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_dec_ref(v___y_1038_);
v___x_1045_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1046_ = l_Lean_MessageData_ofExpr(v___y_1042_);
v___x_1047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1045_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = l_Lean_Exception_toMessageData(v___y_1036_);
v___x_1051_ = l_Lean_indentD(v___x_1050_);
v___x_1052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1049_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1054_, v___y_1040_, v___y_1043_, v___y_1039_, v___y_1041_);
v___y_1024_ = v___y_1037_;
v___y_1025_ = v___x_1055_;
goto v___jp_1023_;
}
else
{
lean_dec_ref(v___y_1042_);
lean_dec_ref(v___y_1036_);
v___y_1024_ = v___y_1037_;
v___y_1025_ = v___y_1038_;
goto v___jp_1023_;
}
}
v___jp_1057_:
{
lean_object* v___x_1064_; lean_object* v_a_1065_; lean_object* v___x_1066_; 
v___x_1064_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_1058_, v___y_1061_);
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1065_);
lean_dec_ref(v___x_1064_);
v___x_1066_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___x_1056_, v___y_1061_);
if (v___y_1059_ == 0)
{
lean_object* v_a_1067_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1067_);
lean_dec_ref(v___x_1066_);
v___y_1018_ = v_a_1065_;
v_proof_1019_ = v_a_1067_;
goto v___jp_1017_;
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1069_; 
v_a_1068_ = lean_ctor_get(v___x_1066_, 0);
lean_inc_n(v_a_1068_, 2);
lean_dec_ref(v___x_1066_);
v___x_1069_ = l_Lean_Meta_mkEqOfHEq(v_a_1068_, v___x_1004_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_dec(v_a_1068_);
v___y_1024_ = v_a_1065_;
v___y_1025_ = v___x_1069_;
goto v___jp_1023_;
}
else
{
lean_object* v_a_1070_; uint8_t v___x_1071_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
v___x_1071_ = l_Lean_Exception_isInterrupt(v_a_1070_);
if (v___x_1071_ == 0)
{
uint8_t v___x_1072_; 
lean_inc(v_a_1070_);
v___x_1072_ = l_Lean_Exception_isRuntime(v_a_1070_);
v___y_1036_ = v_a_1070_;
v___y_1037_ = v_a_1065_;
v___y_1038_ = v___x_1069_;
v___y_1039_ = v___y_1062_;
v___y_1040_ = v___y_1060_;
v___y_1041_ = v___y_1063_;
v___y_1042_ = v_a_1068_;
v___y_1043_ = v___y_1061_;
v___y_1044_ = v___x_1072_;
goto v___jp_1035_;
}
else
{
v___y_1036_ = v_a_1070_;
v___y_1037_ = v_a_1065_;
v___y_1038_ = v___x_1069_;
v___y_1039_ = v___y_1062_;
v___y_1040_ = v___y_1060_;
v___y_1041_ = v___y_1063_;
v___y_1042_ = v_a_1068_;
v___y_1043_ = v___y_1061_;
v___y_1044_ = v___x_1071_;
goto v___jp_1035_;
}
}
}
}
v___jp_1073_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1081_ = lean_array_get_size(v_a_1080_);
v___x_1082_ = lean_unsigned_to_nat(0u);
v___x_1083_ = lean_nat_dec_eq(v___x_1081_, v___x_1082_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_dec_ref(v___y_1074_);
lean_dec_ref(v___x_1056_);
v___x_1084_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1085_ = l_Lean_MessageData_ofConstName(v___x_1007_, v___x_1008_);
v___x_1086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1086_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
v___x_1089_ = lean_array_to_list(v_a_1080_);
v___x_1090_ = lean_box(0);
v___x_1091_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_1089_, v___x_1090_);
v___x_1092_ = l_Lean_MessageData_ofList(v___x_1091_);
v___x_1093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1088_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1093_, v___y_1075_, v___y_1077_, v___y_1078_, v___y_1076_);
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1094_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1094_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
else
{
lean_dec_ref(v_a_1080_);
lean_dec(v___x_1007_);
v___y_1058_ = v___y_1074_;
v___y_1059_ = v___y_1079_;
v___y_1060_ = v___y_1075_;
v___y_1061_ = v___y_1077_;
v___y_1062_ = v___y_1078_;
v___y_1063_ = v___y_1076_;
goto v___jp_1057_;
}
}
v___jp_1103_:
{
if (lean_obj_tag(v___y_1110_) == 0)
{
lean_object* v_a_1111_; 
v_a_1111_ = lean_ctor_get(v___y_1110_, 0);
lean_inc(v_a_1111_);
lean_dec_ref(v___y_1110_);
v___y_1074_ = v___y_1104_;
v___y_1075_ = v___y_1105_;
v___y_1076_ = v___y_1106_;
v___y_1077_ = v___y_1107_;
v___y_1078_ = v___y_1108_;
v___y_1079_ = v___y_1109_;
v_a_1080_ = v_a_1111_;
goto v___jp_1073_;
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_dec_ref(v___y_1104_);
lean_dec_ref(v___x_1056_);
lean_dec(v___x_1007_);
v_a_1112_ = lean_ctor_get(v___y_1110_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___y_1110_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___y_1110_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___y_1110_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
v___jp_1123_:
{
lean_object* v___x_1130_; size_t v_sz_1131_; lean_object* v___x_1132_; 
v___x_1130_ = lean_box(0);
v_sz_1131_ = lean_array_size(v___x_1122_);
v___x_1132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1122_, v_sz_1131_, v___x_1121_, v___x_1130_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; uint8_t v___x_1136_; 
lean_dec_ref(v___x_1132_);
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = lean_array_get_size(v___x_1122_);
v___x_1135_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1136_ = lean_nat_dec_lt(v___x_1133_, v___x_1134_);
if (v___x_1136_ == 0)
{
lean_dec_ref(v___x_1122_);
v___y_1074_ = v___y_1124_;
v___y_1075_ = v___y_1126_;
v___y_1076_ = v___y_1129_;
v___y_1077_ = v___y_1127_;
v___y_1078_ = v___y_1128_;
v___y_1079_ = v___y_1125_;
v_a_1080_ = v___x_1135_;
goto v___jp_1073_;
}
else
{
uint8_t v___x_1137_; 
v___x_1137_ = lean_nat_dec_le(v___x_1134_, v___x_1134_);
if (v___x_1137_ == 0)
{
if (v___x_1136_ == 0)
{
lean_dec_ref(v___x_1122_);
v___y_1074_ = v___y_1124_;
v___y_1075_ = v___y_1126_;
v___y_1076_ = v___y_1129_;
v___y_1077_ = v___y_1127_;
v___y_1078_ = v___y_1128_;
v___y_1079_ = v___y_1125_;
v_a_1080_ = v___x_1135_;
goto v___jp_1073_;
}
else
{
size_t v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = lean_usize_of_nat(v___x_1134_);
v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12(v___x_1008_, v___x_1122_, v___x_1121_, v___x_1138_, v___x_1135_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec_ref(v___x_1122_);
v___y_1104_ = v___y_1124_;
v___y_1105_ = v___y_1126_;
v___y_1106_ = v___y_1129_;
v___y_1107_ = v___y_1127_;
v___y_1108_ = v___y_1128_;
v___y_1109_ = v___y_1125_;
v___y_1110_ = v___x_1139_;
goto v___jp_1103_;
}
}
else
{
size_t v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = lean_usize_of_nat(v___x_1134_);
v___x_1141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12(v___x_1008_, v___x_1122_, v___x_1121_, v___x_1140_, v___x_1135_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec_ref(v___x_1122_);
v___y_1104_ = v___y_1124_;
v___y_1105_ = v___y_1126_;
v___y_1106_ = v___y_1129_;
v___y_1107_ = v___y_1127_;
v___y_1108_ = v___y_1128_;
v___y_1109_ = v___y_1125_;
v___y_1110_ = v___x_1141_;
goto v___jp_1103_;
}
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_dec_ref(v___y_1124_);
lean_dec_ref(v___x_1122_);
lean_dec_ref(v___x_1056_);
lean_dec(v___x_1007_);
v_a_1142_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1132_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1132_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
v___jp_1150_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec_ref(v___y_1151_);
v___x_1158_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1159_ = l_Lean_MessageData_ofExpr(v___y_1152_);
v___x_1160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1158_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1160_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v___x_1163_ = l_Lean_MessageData_ofConstName(v___x_1007_, v___x_1008_);
v___x_1164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1162_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
v___x_1165_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1164_);
lean_ctor_set(v___x_1166_, 1, v___x_1165_);
v___x_1167_ = l_Lean_MessageData_ofExpr(v_e_1009_);
v___x_1168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1166_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
v___x_1169_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_1170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1170_, v___y_1154_, v___y_1153_, v___y_1156_, v___y_1155_);
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1171_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1171_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
v___jp_1180_:
{
lean_object* v___x_1184_; 
lean_inc_ref(v_fst_1182_);
lean_inc_ref(v_e_1009_);
v___x_1184_ = l_Lean_Meta_isExprDefEq(v_e_1009_, v_fst_1182_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; uint8_t v___x_1186_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_a_1185_);
lean_dec_ref(v___x_1184_);
v___x_1186_ = lean_unbox(v_a_1185_);
lean_dec(v_a_1185_);
if (v___x_1186_ == 0)
{
lean_dec_ref(v___x_1122_);
lean_dec_ref(v___x_1056_);
v___y_1151_ = v_snd_1183_;
v___y_1152_ = v_fst_1182_;
v___y_1153_ = v___y_1013_;
v___y_1154_ = v___y_1012_;
v___y_1155_ = v___y_1015_;
v___y_1156_ = v___y_1014_;
v___y_1157_ = v_fst_1181_;
goto v___jp_1150_;
}
else
{
if (v___x_1008_ == 0)
{
lean_dec_ref(v_fst_1182_);
lean_dec_ref(v_e_1009_);
v___y_1124_ = v_snd_1183_;
v___y_1125_ = v_fst_1181_;
v___y_1126_ = v___y_1012_;
v___y_1127_ = v___y_1013_;
v___y_1128_ = v___y_1014_;
v___y_1129_ = v___y_1015_;
goto v___jp_1123_;
}
else
{
lean_dec_ref(v___x_1122_);
lean_dec_ref(v___x_1056_);
v___y_1151_ = v_snd_1183_;
v___y_1152_ = v_fst_1182_;
v___y_1153_ = v___y_1013_;
v___y_1154_ = v___y_1012_;
v___y_1155_ = v___y_1015_;
v___y_1156_ = v___y_1014_;
v___y_1157_ = v_fst_1181_;
goto v___jp_1150_;
}
}
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_dec_ref(v_snd_1183_);
lean_dec_ref(v_fst_1182_);
lean_dec_ref(v___x_1122_);
lean_dec_ref(v___x_1056_);
lean_dec_ref(v_e_1009_);
lean_dec(v___x_1007_);
v_a_1187_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1184_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1184_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2___boxed(lean_object* v___x_1222_, lean_object* v___x_1223_, lean_object* v_fst_1224_, lean_object* v___x_1225_, lean_object* v___x_1226_, lean_object* v_e_1227_, lean_object* v_snd_1228_, lean_object* v_____r_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
uint8_t v___x_108749__boxed_1235_; uint8_t v___x_108753__boxed_1236_; lean_object* v_res_1237_; 
v___x_108749__boxed_1235_ = lean_unbox(v___x_1222_);
v___x_108753__boxed_1236_ = lean_unbox(v___x_1226_);
v_res_1237_ = l_Lean_Meta_rwMatcher___lam__2(v___x_108749__boxed_1235_, v___x_1223_, v_fst_1224_, v___x_1225_, v___x_108753__boxed_1236_, v_e_1227_, v_snd_1228_, v_____r_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec_ref(v_snd_1228_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(uint8_t v___x_1238_, lean_object* v_as_1239_, size_t v_i_1240_, size_t v_stop_1241_, lean_object* v_b_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v_a_1249_; uint8_t v___x_1253_; 
v___x_1253_ = lean_usize_dec_eq(v_i_1240_, v_stop_1241_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; uint8_t v_a_1256_; lean_object* v___x_1258_; 
v___x_1254_ = lean_array_uget_borrowed(v_as_1239_, v_i_1240_);
v___x_1258_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v___x_1254_, v___y_1244_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; uint8_t v___x_1260_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1259_);
lean_dec_ref(v___x_1258_);
v___x_1260_ = lean_unbox(v_a_1259_);
lean_dec(v_a_1259_);
if (v___x_1260_ == 0)
{
v_a_1256_ = v___x_1238_;
goto v___jp_1255_;
}
else
{
v_a_1249_ = v_b_1242_;
goto v___jp_1248_;
}
}
else
{
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1261_; uint8_t v___x_1262_; 
v_a_1261_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_a_1261_);
lean_dec_ref(v___x_1258_);
v___x_1262_ = lean_unbox(v_a_1261_);
lean_dec(v_a_1261_);
v_a_1256_ = v___x_1262_;
goto v___jp_1255_;
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
lean_dec_ref(v_b_1242_);
v_a_1263_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1258_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1258_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
v___jp_1255_:
{
if (v_a_1256_ == 0)
{
v_a_1249_ = v_b_1242_;
goto v___jp_1248_;
}
else
{
lean_object* v___x_1257_; 
lean_inc(v___x_1254_);
v___x_1257_ = lean_array_push(v_b_1242_, v___x_1254_);
v_a_1249_ = v___x_1257_;
goto v___jp_1248_;
}
}
}
else
{
lean_object* v___x_1271_; 
v___x_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1271_, 0, v_b_1242_);
return v___x_1271_;
}
v___jp_1248_:
{
size_t v___x_1250_; size_t v___x_1251_; 
v___x_1250_ = ((size_t)1ULL);
v___x_1251_ = lean_usize_add(v_i_1240_, v___x_1250_);
v_i_1240_ = v___x_1251_;
v_b_1242_ = v_a_1249_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13___boxed(lean_object* v___x_1272_, lean_object* v_as_1273_, lean_object* v_i_1274_, lean_object* v_stop_1275_, lean_object* v_b_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
uint8_t v___x_109234__boxed_1282_; size_t v_i_boxed_1283_; size_t v_stop_boxed_1284_; lean_object* v_res_1285_; 
v___x_109234__boxed_1282_ = lean_unbox(v___x_1272_);
v_i_boxed_1283_ = lean_unbox_usize(v_i_1274_);
lean_dec(v_i_1274_);
v_stop_boxed_1284_ = lean_unbox_usize(v_stop_1275_);
lean_dec(v_stop_1275_);
v_res_1285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(v___x_109234__boxed_1282_, v_as_1273_, v_i_boxed_1283_, v_stop_boxed_1284_, v_b_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec_ref(v_as_1273_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3(uint8_t v___x_1286_, lean_object* v___x_1287_, lean_object* v_fst_1288_, lean_object* v___x_1289_, uint8_t v___x_1290_, lean_object* v_e_1291_, uint8_t v___y_1292_, lean_object* v_snd_1293_, lean_object* v_____r_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v___y_1301_; lean_object* v_proof_1302_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; uint8_t v___y_1327_; lean_object* v___x_1339_; uint8_t v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1357_; uint8_t v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v_a_1363_; lean_object* v___y_1387_; uint8_t v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; size_t v_sz_1403_; size_t v___x_1404_; lean_object* v___x_1405_; uint8_t v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; uint8_t v_fst_1434_; lean_object* v_fst_1435_; lean_object* v_snd_1436_; lean_object* v___x_1470_; lean_object* v___x_1471_; uint8_t v___x_1472_; 
v___x_1339_ = l_Lean_mkAppN(v___x_1287_, v_fst_1288_);
v_sz_1403_ = lean_array_size(v_fst_1288_);
v___x_1404_ = ((size_t)0ULL);
v___x_1405_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_1403_, v___x_1404_, v_fst_1288_);
v___x_1470_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1471_ = lean_unsigned_to_nat(4u);
v___x_1472_ = l_Lean_Expr_isAppOfArity(v_snd_1293_, v___x_1470_, v___x_1471_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; lean_object* v___x_1474_; uint8_t v___x_1475_; 
v___x_1473_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1474_ = lean_unsigned_to_nat(3u);
v___x_1475_ = l_Lean_Expr_isAppOfArity(v_snd_1293_, v___x_1473_, v___x_1474_);
if (v___x_1475_ == 0)
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec_ref(v___x_1405_);
lean_dec_ref(v___x_1339_);
lean_dec_ref(v_e_1291_);
v___x_1476_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1477_ = l_Lean_MessageData_ofConstName(v___x_1289_, v___x_1475_);
v___x_1478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1476_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1478_);
lean_ctor_set(v___x_1480_, 1, v___x_1479_);
v___x_1481_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1480_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1481_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1481_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
else
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1490_ = l_Lean_Expr_appFn_x21(v_snd_1293_);
v___x_1491_ = l_Lean_Expr_appArg_x21(v___x_1490_);
lean_dec_ref(v___x_1490_);
v___x_1492_ = l_Lean_Expr_appArg_x21(v_snd_1293_);
v_fst_1434_ = v___x_1472_;
v_fst_1435_ = v___x_1491_;
v_snd_1436_ = v___x_1492_;
goto v___jp_1433_;
}
}
else
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1493_ = l_Lean_Expr_appFn_x21(v_snd_1293_);
v___x_1494_ = l_Lean_Expr_appFn_x21(v___x_1493_);
lean_dec_ref(v___x_1493_);
v___x_1495_ = l_Lean_Expr_appArg_x21(v___x_1494_);
lean_dec_ref(v___x_1494_);
v___x_1496_ = l_Lean_Expr_appArg_x21(v_snd_1293_);
v_fst_1434_ = v___x_1286_;
v_fst_1435_ = v___x_1495_;
v_snd_1436_ = v___x_1496_;
goto v___jp_1433_;
}
v___jp_1300_:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1303_, 0, v_proof_1302_);
v___x_1304_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1304_, 0, v___y_1301_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
lean_ctor_set_uint8(v___x_1304_, sizeof(void*)*2, v___x_1286_);
v___x_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
return v___x_1305_;
}
v___jp_1306_:
{
if (lean_obj_tag(v___y_1308_) == 0)
{
lean_object* v_a_1309_; 
v_a_1309_ = lean_ctor_get(v___y_1308_, 0);
lean_inc(v_a_1309_);
lean_dec_ref(v___y_1308_);
v___y_1301_ = v___y_1307_;
v_proof_1302_ = v_a_1309_;
goto v___jp_1300_;
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
lean_dec_ref(v___y_1307_);
v_a_1310_ = lean_ctor_get(v___y_1308_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___y_1308_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___y_1308_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___y_1308_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
v___jp_1318_:
{
if (v___y_1327_ == 0)
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
lean_dec_ref(v___y_1326_);
v___x_1328_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1329_ = l_Lean_MessageData_ofExpr(v___y_1323_);
v___x_1330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1328_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
v___x_1331_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1330_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
v___x_1333_ = l_Lean_Exception_toMessageData(v___y_1325_);
v___x_1334_ = l_Lean_indentD(v___x_1333_);
v___x_1335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1332_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
v___x_1336_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1335_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
v___x_1338_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1337_, v___y_1322_, v___y_1321_, v___y_1324_, v___y_1320_);
v___y_1307_ = v___y_1319_;
v___y_1308_ = v___x_1338_;
goto v___jp_1306_;
}
else
{
lean_dec_ref(v___y_1325_);
lean_dec_ref(v___y_1323_);
v___y_1307_ = v___y_1319_;
v___y_1308_ = v___y_1326_;
goto v___jp_1306_;
}
}
v___jp_1340_:
{
lean_object* v___x_1347_; lean_object* v_a_1348_; lean_object* v___x_1349_; 
v___x_1347_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_1342_, v___y_1344_);
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref(v___x_1347_);
v___x_1349_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___x_1339_, v___y_1344_);
if (v___y_1341_ == 0)
{
lean_object* v_a_1350_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref(v___x_1349_);
v___y_1301_ = v_a_1348_;
v_proof_1302_ = v_a_1350_;
goto v___jp_1300_;
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1352_; 
v_a_1351_ = lean_ctor_get(v___x_1349_, 0);
lean_inc_n(v_a_1351_, 2);
lean_dec_ref(v___x_1349_);
v___x_1352_ = l_Lean_Meta_mkEqOfHEq(v_a_1351_, v___x_1286_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_dec(v_a_1351_);
v___y_1307_ = v_a_1348_;
v___y_1308_ = v___x_1352_;
goto v___jp_1306_;
}
else
{
lean_object* v_a_1353_; uint8_t v___x_1354_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_a_1353_);
v___x_1354_ = l_Lean_Exception_isInterrupt(v_a_1353_);
if (v___x_1354_ == 0)
{
uint8_t v___x_1355_; 
lean_inc(v_a_1353_);
v___x_1355_ = l_Lean_Exception_isRuntime(v_a_1353_);
v___y_1319_ = v_a_1348_;
v___y_1320_ = v___y_1346_;
v___y_1321_ = v___y_1344_;
v___y_1322_ = v___y_1343_;
v___y_1323_ = v_a_1351_;
v___y_1324_ = v___y_1345_;
v___y_1325_ = v_a_1353_;
v___y_1326_ = v___x_1352_;
v___y_1327_ = v___x_1355_;
goto v___jp_1318_;
}
else
{
v___y_1319_ = v_a_1348_;
v___y_1320_ = v___y_1346_;
v___y_1321_ = v___y_1344_;
v___y_1322_ = v___y_1343_;
v___y_1323_ = v_a_1351_;
v___y_1324_ = v___y_1345_;
v___y_1325_ = v_a_1353_;
v___y_1326_ = v___x_1352_;
v___y_1327_ = v___x_1354_;
goto v___jp_1318_;
}
}
}
}
v___jp_1356_:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v___x_1364_ = lean_array_get_size(v_a_1363_);
v___x_1365_ = lean_unsigned_to_nat(0u);
v___x_1366_ = lean_nat_dec_eq(v___x_1364_, v___x_1365_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_dec_ref(v___y_1359_);
lean_dec_ref(v___x_1339_);
v___x_1367_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1368_ = l_Lean_MessageData_ofConstName(v___x_1289_, v___x_1366_);
v___x_1369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1367_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
v___x_1370_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1369_);
lean_ctor_set(v___x_1371_, 1, v___x_1370_);
v___x_1372_ = lean_array_to_list(v_a_1363_);
v___x_1373_ = lean_box(0);
v___x_1374_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_1372_, v___x_1373_);
v___x_1375_ = l_Lean_MessageData_ofList(v___x_1374_);
v___x_1376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1371_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
v___x_1377_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1376_, v___y_1361_, v___y_1360_, v___y_1357_, v___y_1362_);
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1377_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1377_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
else
{
lean_dec_ref(v_a_1363_);
lean_dec(v___x_1289_);
v___y_1341_ = v___y_1358_;
v___y_1342_ = v___y_1359_;
v___y_1343_ = v___y_1361_;
v___y_1344_ = v___y_1360_;
v___y_1345_ = v___y_1357_;
v___y_1346_ = v___y_1362_;
goto v___jp_1340_;
}
}
v___jp_1386_:
{
if (lean_obj_tag(v___y_1393_) == 0)
{
lean_object* v_a_1394_; 
v_a_1394_ = lean_ctor_get(v___y_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref(v___y_1393_);
v___y_1357_ = v___y_1387_;
v___y_1358_ = v___y_1388_;
v___y_1359_ = v___y_1389_;
v___y_1360_ = v___y_1391_;
v___y_1361_ = v___y_1390_;
v___y_1362_ = v___y_1392_;
v_a_1363_ = v_a_1394_;
goto v___jp_1356_;
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
lean_dec_ref(v___y_1389_);
lean_dec_ref(v___x_1339_);
lean_dec(v___x_1289_);
v_a_1395_ = lean_ctor_get(v___y_1393_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___y_1393_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___y_1393_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___y_1393_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
v___jp_1406_:
{
lean_object* v___x_1413_; size_t v_sz_1414_; lean_object* v___x_1415_; 
v___x_1413_ = lean_box(0);
v_sz_1414_ = lean_array_size(v___x_1405_);
v___x_1415_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1405_, v_sz_1414_, v___x_1404_, v___x_1413_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
lean_dec_ref(v___x_1415_);
v___x_1416_ = lean_unsigned_to_nat(0u);
v___x_1417_ = lean_array_get_size(v___x_1405_);
v___x_1418_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1419_ = lean_nat_dec_lt(v___x_1416_, v___x_1417_);
if (v___x_1419_ == 0)
{
lean_dec_ref(v___x_1405_);
v___y_1357_ = v___y_1411_;
v___y_1358_ = v___y_1407_;
v___y_1359_ = v___y_1408_;
v___y_1360_ = v___y_1410_;
v___y_1361_ = v___y_1409_;
v___y_1362_ = v___y_1412_;
v_a_1363_ = v___x_1418_;
goto v___jp_1356_;
}
else
{
uint8_t v___x_1420_; 
v___x_1420_ = lean_nat_dec_le(v___x_1417_, v___x_1417_);
if (v___x_1420_ == 0)
{
if (v___x_1419_ == 0)
{
lean_dec_ref(v___x_1405_);
v___y_1357_ = v___y_1411_;
v___y_1358_ = v___y_1407_;
v___y_1359_ = v___y_1408_;
v___y_1360_ = v___y_1410_;
v___y_1361_ = v___y_1409_;
v___y_1362_ = v___y_1412_;
v_a_1363_ = v___x_1418_;
goto v___jp_1356_;
}
else
{
size_t v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = lean_usize_of_nat(v___x_1417_);
v___x_1422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(v___x_1290_, v___x_1405_, v___x_1404_, v___x_1421_, v___x_1418_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
lean_dec_ref(v___x_1405_);
v___y_1387_ = v___y_1411_;
v___y_1388_ = v___y_1407_;
v___y_1389_ = v___y_1408_;
v___y_1390_ = v___y_1409_;
v___y_1391_ = v___y_1410_;
v___y_1392_ = v___y_1412_;
v___y_1393_ = v___x_1422_;
goto v___jp_1386_;
}
}
else
{
size_t v___x_1423_; lean_object* v___x_1424_; 
v___x_1423_ = lean_usize_of_nat(v___x_1417_);
v___x_1424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(v___x_1290_, v___x_1405_, v___x_1404_, v___x_1423_, v___x_1418_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
lean_dec_ref(v___x_1405_);
v___y_1387_ = v___y_1411_;
v___y_1388_ = v___y_1407_;
v___y_1389_ = v___y_1408_;
v___y_1390_ = v___y_1409_;
v___y_1391_ = v___y_1410_;
v___y_1392_ = v___y_1412_;
v___y_1393_ = v___x_1424_;
goto v___jp_1386_;
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec_ref(v___y_1408_);
lean_dec_ref(v___x_1405_);
lean_dec_ref(v___x_1339_);
lean_dec(v___x_1289_);
v_a_1425_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1415_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1415_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
v___jp_1433_:
{
lean_object* v___x_1437_; 
lean_inc_ref(v_fst_1435_);
lean_inc_ref(v_e_1291_);
v___x_1437_ = l_Lean_Meta_isExprDefEq(v_e_1291_, v_fst_1435_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; uint8_t v___x_1439_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref(v___x_1437_);
v___x_1439_ = lean_unbox(v_a_1438_);
lean_dec(v_a_1438_);
if (v___x_1439_ == 0)
{
if (v___x_1290_ == 0)
{
lean_dec_ref(v_fst_1435_);
lean_dec_ref(v_e_1291_);
v___y_1407_ = v_fst_1434_;
v___y_1408_ = v_snd_1436_;
v___y_1409_ = v___y_1295_;
v___y_1410_ = v___y_1296_;
v___y_1411_ = v___y_1297_;
v___y_1412_ = v___y_1298_;
goto v___jp_1406_;
}
else
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec_ref(v_snd_1436_);
lean_dec_ref(v___x_1405_);
lean_dec_ref(v___x_1339_);
v___x_1440_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1441_ = l_Lean_MessageData_ofExpr(v_fst_1435_);
v___x_1442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1440_);
lean_ctor_set(v___x_1442_, 1, v___x_1441_);
v___x_1443_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1442_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
v___x_1445_ = l_Lean_MessageData_ofConstName(v___x_1289_, v___y_1292_);
v___x_1446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1444_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
v___x_1447_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1446_);
lean_ctor_set(v___x_1448_, 1, v___x_1447_);
v___x_1449_ = l_Lean_MessageData_ofExpr(v_e_1291_);
v___x_1450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1448_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
v___x_1451_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_1452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1450_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
v___x_1453_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1452_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1453_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1453_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
else
{
lean_dec_ref(v_fst_1435_);
lean_dec_ref(v_e_1291_);
v___y_1407_ = v_fst_1434_;
v___y_1408_ = v_snd_1436_;
v___y_1409_ = v___y_1295_;
v___y_1410_ = v___y_1296_;
v___y_1411_ = v___y_1297_;
v___y_1412_ = v___y_1298_;
goto v___jp_1406_;
}
}
else
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
lean_dec_ref(v_snd_1436_);
lean_dec_ref(v_fst_1435_);
lean_dec_ref(v___x_1405_);
lean_dec_ref(v___x_1339_);
lean_dec_ref(v_e_1291_);
lean_dec(v___x_1289_);
v_a_1462_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1437_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1437_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3___boxed(lean_object* v___x_1497_, lean_object* v___x_1498_, lean_object* v_fst_1499_, lean_object* v___x_1500_, lean_object* v___x_1501_, lean_object* v_e_1502_, lean_object* v___y_1503_, lean_object* v_snd_1504_, lean_object* v_____r_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
uint8_t v___x_109341__boxed_1511_; uint8_t v___x_109345__boxed_1512_; uint8_t v___y_109346__boxed_1513_; lean_object* v_res_1514_; 
v___x_109341__boxed_1511_ = lean_unbox(v___x_1497_);
v___x_109345__boxed_1512_ = lean_unbox(v___x_1501_);
v___y_109346__boxed_1513_ = lean_unbox(v___y_1503_);
v_res_1514_ = l_Lean_Meta_rwMatcher___lam__3(v___x_109341__boxed_1511_, v___x_1498_, v_fst_1499_, v___x_1500_, v___x_109345__boxed_1512_, v_e_1502_, v___y_109346__boxed_1513_, v_snd_1504_, v_____r_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec_ref(v_snd_1504_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4(uint8_t v___x_1515_, lean_object* v___x_1516_, lean_object* v_fst_1517_, lean_object* v___x_1518_, uint8_t v___x_1519_, lean_object* v_e_1520_, lean_object* v_snd_1521_, lean_object* v_____r_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v___y_1529_; lean_object* v_proof_1530_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; uint8_t v___y_1555_; lean_object* v___x_1567_; uint8_t v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1585_; lean_object* v___y_1586_; uint8_t v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v_a_1591_; lean_object* v___y_1615_; lean_object* v___y_1616_; uint8_t v___y_1617_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; size_t v_sz_1631_; size_t v___x_1632_; lean_object* v___x_1633_; uint8_t v___y_1635_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1662_; lean_object* v___y_1663_; uint8_t v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; uint8_t v_fst_1692_; lean_object* v_fst_1693_; lean_object* v_snd_1694_; lean_object* v___x_1706_; lean_object* v___x_1707_; uint8_t v___x_1708_; 
v___x_1567_ = l_Lean_mkAppN(v___x_1516_, v_fst_1517_);
v_sz_1631_ = lean_array_size(v_fst_1517_);
v___x_1632_ = ((size_t)0ULL);
v___x_1633_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_1631_, v___x_1632_, v_fst_1517_);
v___x_1706_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1707_ = lean_unsigned_to_nat(4u);
v___x_1708_ = l_Lean_Expr_isAppOfArity(v_snd_1521_, v___x_1706_, v___x_1707_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; 
v___x_1709_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1710_ = lean_unsigned_to_nat(3u);
v___x_1711_ = l_Lean_Expr_isAppOfArity(v_snd_1521_, v___x_1709_, v___x_1710_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec_ref(v___x_1633_);
lean_dec_ref(v___x_1567_);
lean_dec_ref(v_e_1520_);
v___x_1712_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1713_ = l_Lean_MessageData_ofConstName(v___x_1518_, v___x_1519_);
v___x_1714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1712_);
lean_ctor_set(v___x_1714_, 1, v___x_1713_);
v___x_1715_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1714_);
lean_ctor_set(v___x_1716_, 1, v___x_1715_);
v___x_1717_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1716_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1717_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1717_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
else
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1726_ = l_Lean_Expr_appFn_x21(v_snd_1521_);
v___x_1727_ = l_Lean_Expr_appArg_x21(v___x_1726_);
lean_dec_ref(v___x_1726_);
v___x_1728_ = l_Lean_Expr_appArg_x21(v_snd_1521_);
v_fst_1692_ = v___x_1519_;
v_fst_1693_ = v___x_1727_;
v_snd_1694_ = v___x_1728_;
goto v___jp_1691_;
}
}
else
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1729_ = l_Lean_Expr_appFn_x21(v_snd_1521_);
v___x_1730_ = l_Lean_Expr_appFn_x21(v___x_1729_);
lean_dec_ref(v___x_1729_);
v___x_1731_ = l_Lean_Expr_appArg_x21(v___x_1730_);
lean_dec_ref(v___x_1730_);
v___x_1732_ = l_Lean_Expr_appArg_x21(v_snd_1521_);
v_fst_1692_ = v___x_1515_;
v_fst_1693_ = v___x_1731_;
v_snd_1694_ = v___x_1732_;
goto v___jp_1691_;
}
v___jp_1528_:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1531_, 0, v_proof_1530_);
v___x_1532_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1532_, 0, v___y_1529_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
lean_ctor_set_uint8(v___x_1532_, sizeof(void*)*2, v___x_1515_);
v___x_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
return v___x_1533_;
}
v___jp_1534_:
{
if (lean_obj_tag(v___y_1536_) == 0)
{
lean_object* v_a_1537_; 
v_a_1537_ = lean_ctor_get(v___y_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref(v___y_1536_);
v___y_1529_ = v___y_1535_;
v_proof_1530_ = v_a_1537_;
goto v___jp_1528_;
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
lean_dec_ref(v___y_1535_);
v_a_1538_ = lean_ctor_get(v___y_1536_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___y_1536_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___y_1536_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___y_1536_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
v___jp_1546_:
{
if (v___y_1555_ == 0)
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
lean_dec_ref(v___y_1550_);
v___x_1556_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1557_ = l_Lean_MessageData_ofExpr(v___y_1551_);
v___x_1558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1556_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1558_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
v___x_1561_ = l_Lean_Exception_toMessageData(v___y_1548_);
v___x_1562_ = l_Lean_indentD(v___x_1561_);
v___x_1563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1560_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1563_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1565_, v___y_1554_, v___y_1552_, v___y_1547_, v___y_1549_);
v___y_1535_ = v___y_1553_;
v___y_1536_ = v___x_1566_;
goto v___jp_1534_;
}
else
{
lean_dec_ref(v___y_1551_);
lean_dec_ref(v___y_1548_);
v___y_1535_ = v___y_1553_;
v___y_1536_ = v___y_1550_;
goto v___jp_1534_;
}
}
v___jp_1568_:
{
lean_object* v___x_1575_; lean_object* v_a_1576_; lean_object* v___x_1577_; 
v___x_1575_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_1570_, v___y_1572_);
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref(v___x_1575_);
v___x_1577_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___x_1567_, v___y_1572_);
if (v___y_1569_ == 0)
{
lean_object* v_a_1578_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref(v___x_1577_);
v___y_1529_ = v_a_1576_;
v_proof_1530_ = v_a_1578_;
goto v___jp_1528_;
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1580_; 
v_a_1579_ = lean_ctor_get(v___x_1577_, 0);
lean_inc_n(v_a_1579_, 2);
lean_dec_ref(v___x_1577_);
v___x_1580_ = l_Lean_Meta_mkEqOfHEq(v_a_1579_, v___x_1515_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_dec(v_a_1579_);
v___y_1535_ = v_a_1576_;
v___y_1536_ = v___x_1580_;
goto v___jp_1534_;
}
else
{
lean_object* v_a_1581_; uint8_t v___x_1582_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
v___x_1582_ = l_Lean_Exception_isInterrupt(v_a_1581_);
if (v___x_1582_ == 0)
{
uint8_t v___x_1583_; 
lean_inc(v_a_1581_);
v___x_1583_ = l_Lean_Exception_isRuntime(v_a_1581_);
v___y_1547_ = v___y_1573_;
v___y_1548_ = v_a_1581_;
v___y_1549_ = v___y_1574_;
v___y_1550_ = v___x_1580_;
v___y_1551_ = v_a_1579_;
v___y_1552_ = v___y_1572_;
v___y_1553_ = v_a_1576_;
v___y_1554_ = v___y_1571_;
v___y_1555_ = v___x_1583_;
goto v___jp_1546_;
}
else
{
v___y_1547_ = v___y_1573_;
v___y_1548_ = v_a_1581_;
v___y_1549_ = v___y_1574_;
v___y_1550_ = v___x_1580_;
v___y_1551_ = v_a_1579_;
v___y_1552_ = v___y_1572_;
v___y_1553_ = v_a_1576_;
v___y_1554_ = v___y_1571_;
v___y_1555_ = v___x_1582_;
goto v___jp_1546_;
}
}
}
}
v___jp_1584_:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; uint8_t v___x_1594_; 
v___x_1592_ = lean_array_get_size(v_a_1591_);
v___x_1593_ = lean_unsigned_to_nat(0u);
v___x_1594_ = lean_nat_dec_eq(v___x_1592_, v___x_1593_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
lean_dec_ref(v___y_1589_);
lean_dec_ref(v___x_1567_);
v___x_1595_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1596_ = l_Lean_MessageData_ofConstName(v___x_1518_, v___x_1519_);
v___x_1597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1595_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1597_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
v___x_1600_ = lean_array_to_list(v_a_1591_);
v___x_1601_ = lean_box(0);
v___x_1602_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_1600_, v___x_1601_);
v___x_1603_ = l_Lean_MessageData_ofList(v___x_1602_);
v___x_1604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1599_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
v___x_1605_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1604_, v___y_1586_, v___y_1585_, v___y_1590_, v___y_1588_);
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1605_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1605_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
else
{
lean_dec_ref(v_a_1591_);
lean_dec(v___x_1518_);
v___y_1569_ = v___y_1587_;
v___y_1570_ = v___y_1589_;
v___y_1571_ = v___y_1586_;
v___y_1572_ = v___y_1585_;
v___y_1573_ = v___y_1590_;
v___y_1574_ = v___y_1588_;
goto v___jp_1568_;
}
}
v___jp_1614_:
{
if (lean_obj_tag(v___y_1621_) == 0)
{
lean_object* v_a_1622_; 
v_a_1622_ = lean_ctor_get(v___y_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref(v___y_1621_);
v___y_1585_ = v___y_1615_;
v___y_1586_ = v___y_1616_;
v___y_1587_ = v___y_1617_;
v___y_1588_ = v___y_1618_;
v___y_1589_ = v___y_1620_;
v___y_1590_ = v___y_1619_;
v_a_1591_ = v_a_1622_;
goto v___jp_1584_;
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec_ref(v___y_1620_);
lean_dec_ref(v___x_1567_);
lean_dec(v___x_1518_);
v_a_1623_ = lean_ctor_get(v___y_1621_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___y_1621_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___y_1621_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___y_1621_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
v___jp_1634_:
{
lean_object* v___x_1641_; size_t v_sz_1642_; lean_object* v___x_1643_; 
v___x_1641_ = lean_box(0);
v_sz_1642_ = lean_array_size(v___x_1633_);
v___x_1643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1633_, v_sz_1642_, v___x_1632_, v___x_1641_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
lean_dec_ref(v___x_1643_);
v___x_1644_ = lean_unsigned_to_nat(0u);
v___x_1645_ = lean_array_get_size(v___x_1633_);
v___x_1646_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1647_ = lean_nat_dec_lt(v___x_1644_, v___x_1645_);
if (v___x_1647_ == 0)
{
lean_dec_ref(v___x_1633_);
v___y_1585_ = v___y_1638_;
v___y_1586_ = v___y_1637_;
v___y_1587_ = v___y_1635_;
v___y_1588_ = v___y_1640_;
v___y_1589_ = v___y_1636_;
v___y_1590_ = v___y_1639_;
v_a_1591_ = v___x_1646_;
goto v___jp_1584_;
}
else
{
uint8_t v___x_1648_; 
v___x_1648_ = lean_nat_dec_le(v___x_1645_, v___x_1645_);
if (v___x_1648_ == 0)
{
if (v___x_1647_ == 0)
{
lean_dec_ref(v___x_1633_);
v___y_1585_ = v___y_1638_;
v___y_1586_ = v___y_1637_;
v___y_1587_ = v___y_1635_;
v___y_1588_ = v___y_1640_;
v___y_1589_ = v___y_1636_;
v___y_1590_ = v___y_1639_;
v_a_1591_ = v___x_1646_;
goto v___jp_1584_;
}
else
{
size_t v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = lean_usize_of_nat(v___x_1645_);
v___x_1650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12(v___x_1519_, v___x_1633_, v___x_1632_, v___x_1649_, v___x_1646_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
lean_dec_ref(v___x_1633_);
v___y_1615_ = v___y_1638_;
v___y_1616_ = v___y_1637_;
v___y_1617_ = v___y_1635_;
v___y_1618_ = v___y_1640_;
v___y_1619_ = v___y_1639_;
v___y_1620_ = v___y_1636_;
v___y_1621_ = v___x_1650_;
goto v___jp_1614_;
}
}
else
{
size_t v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = lean_usize_of_nat(v___x_1645_);
v___x_1652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12(v___x_1519_, v___x_1633_, v___x_1632_, v___x_1651_, v___x_1646_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
lean_dec_ref(v___x_1633_);
v___y_1615_ = v___y_1638_;
v___y_1616_ = v___y_1637_;
v___y_1617_ = v___y_1635_;
v___y_1618_ = v___y_1640_;
v___y_1619_ = v___y_1639_;
v___y_1620_ = v___y_1636_;
v___y_1621_ = v___x_1652_;
goto v___jp_1614_;
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec_ref(v___y_1636_);
lean_dec_ref(v___x_1633_);
lean_dec_ref(v___x_1567_);
lean_dec(v___x_1518_);
v_a_1653_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1643_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1643_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
v___jp_1661_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_dec_ref(v___y_1668_);
v___x_1669_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1670_ = l_Lean_MessageData_ofExpr(v___y_1665_);
v___x_1671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1671_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v___x_1674_ = l_Lean_MessageData_ofConstName(v___x_1518_, v___x_1519_);
v___x_1675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1673_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
v___x_1676_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1675_);
lean_ctor_set(v___x_1677_, 1, v___x_1676_);
v___x_1678_ = l_Lean_MessageData_ofExpr(v_e_1520_);
v___x_1679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1677_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_1681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1679_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
v___x_1682_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1681_, v___y_1663_, v___y_1667_, v___y_1666_, v___y_1662_);
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1682_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1682_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
v___jp_1691_:
{
lean_object* v___x_1695_; 
lean_inc_ref(v_fst_1693_);
lean_inc_ref(v_e_1520_);
v___x_1695_ = l_Lean_Meta_isExprDefEq(v_e_1520_, v_fst_1693_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; uint8_t v___x_1697_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1696_);
lean_dec_ref(v___x_1695_);
v___x_1697_ = lean_unbox(v_a_1696_);
lean_dec(v_a_1696_);
if (v___x_1697_ == 0)
{
lean_dec_ref(v___x_1633_);
lean_dec_ref(v___x_1567_);
v___y_1662_ = v___y_1526_;
v___y_1663_ = v___y_1523_;
v___y_1664_ = v_fst_1692_;
v___y_1665_ = v_fst_1693_;
v___y_1666_ = v___y_1525_;
v___y_1667_ = v___y_1524_;
v___y_1668_ = v_snd_1694_;
goto v___jp_1661_;
}
else
{
if (v___x_1519_ == 0)
{
lean_dec_ref(v_fst_1693_);
lean_dec_ref(v_e_1520_);
v___y_1635_ = v_fst_1692_;
v___y_1636_ = v_snd_1694_;
v___y_1637_ = v___y_1523_;
v___y_1638_ = v___y_1524_;
v___y_1639_ = v___y_1525_;
v___y_1640_ = v___y_1526_;
goto v___jp_1634_;
}
else
{
lean_dec_ref(v___x_1633_);
lean_dec_ref(v___x_1567_);
v___y_1662_ = v___y_1526_;
v___y_1663_ = v___y_1523_;
v___y_1664_ = v_fst_1692_;
v___y_1665_ = v_fst_1693_;
v___y_1666_ = v___y_1525_;
v___y_1667_ = v___y_1524_;
v___y_1668_ = v_snd_1694_;
goto v___jp_1661_;
}
}
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
lean_dec_ref(v_snd_1694_);
lean_dec_ref(v_fst_1693_);
lean_dec_ref(v___x_1633_);
lean_dec_ref(v___x_1567_);
lean_dec_ref(v_e_1520_);
lean_dec(v___x_1518_);
v_a_1698_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1695_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1695_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4___boxed(lean_object* v___x_1733_, lean_object* v___x_1734_, lean_object* v_fst_1735_, lean_object* v___x_1736_, lean_object* v___x_1737_, lean_object* v_e_1738_, lean_object* v_snd_1739_, lean_object* v_____r_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
uint8_t v___x_109829__boxed_1746_; uint8_t v___x_109833__boxed_1747_; lean_object* v_res_1748_; 
v___x_109829__boxed_1746_ = lean_unbox(v___x_1733_);
v___x_109833__boxed_1747_ = lean_unbox(v___x_1737_);
v_res_1748_ = l_Lean_Meta_rwMatcher___lam__4(v___x_109829__boxed_1746_, v___x_1734_, v_fst_1735_, v___x_1736_, v___x_109833__boxed_1747_, v_e_1738_, v_snd_1739_, v_____r_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec_ref(v_snd_1739_);
return v_res_1748_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1749_; double v___x_1750_; 
v___x_1749_ = lean_unsigned_to_nat(0u);
v___x_1750_ = lean_float_of_nat(v___x_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(lean_object* v_cls_1754_, lean_object* v_msg_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v_ref_1761_; lean_object* v___x_1762_; lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1808_; 
v_ref_1761_ = lean_ctor_get(v___y_1758_, 5);
v___x_1762_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1765_ = v___x_1762_;
v_isShared_1766_ = v_isSharedCheck_1808_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1762_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1808_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1767_; lean_object* v_traceState_1768_; lean_object* v_env_1769_; lean_object* v_nextMacroScope_1770_; lean_object* v_ngen_1771_; lean_object* v_auxDeclNGen_1772_; lean_object* v_cache_1773_; lean_object* v_messages_1774_; lean_object* v_infoState_1775_; lean_object* v_snapshotTasks_1776_; lean_object* v_newDecls_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1807_; 
v___x_1767_ = lean_st_ref_take(v___y_1759_);
v_traceState_1768_ = lean_ctor_get(v___x_1767_, 4);
v_env_1769_ = lean_ctor_get(v___x_1767_, 0);
v_nextMacroScope_1770_ = lean_ctor_get(v___x_1767_, 1);
v_ngen_1771_ = lean_ctor_get(v___x_1767_, 2);
v_auxDeclNGen_1772_ = lean_ctor_get(v___x_1767_, 3);
v_cache_1773_ = lean_ctor_get(v___x_1767_, 5);
v_messages_1774_ = lean_ctor_get(v___x_1767_, 6);
v_infoState_1775_ = lean_ctor_get(v___x_1767_, 7);
v_snapshotTasks_1776_ = lean_ctor_get(v___x_1767_, 8);
v_newDecls_1777_ = lean_ctor_get(v___x_1767_, 9);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1779_ = v___x_1767_;
v_isShared_1780_ = v_isSharedCheck_1807_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_newDecls_1777_);
lean_inc(v_snapshotTasks_1776_);
lean_inc(v_infoState_1775_);
lean_inc(v_messages_1774_);
lean_inc(v_cache_1773_);
lean_inc(v_traceState_1768_);
lean_inc(v_auxDeclNGen_1772_);
lean_inc(v_ngen_1771_);
lean_inc(v_nextMacroScope_1770_);
lean_inc(v_env_1769_);
lean_dec(v___x_1767_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1807_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
uint64_t v_tid_1781_; lean_object* v_traces_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1806_; 
v_tid_1781_ = lean_ctor_get_uint64(v_traceState_1768_, sizeof(void*)*1);
v_traces_1782_ = lean_ctor_get(v_traceState_1768_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_traceState_1768_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1784_ = v_traceState_1768_;
v_isShared_1785_ = v_isSharedCheck_1806_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_traces_1782_);
lean_dec(v_traceState_1768_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1806_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1786_; double v___x_1787_; uint8_t v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1796_; 
v___x_1786_ = lean_box(0);
v___x_1787_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0);
v___x_1788_ = 0;
v___x_1789_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1));
v___x_1790_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1790_, 0, v_cls_1754_);
lean_ctor_set(v___x_1790_, 1, v___x_1786_);
lean_ctor_set(v___x_1790_, 2, v___x_1789_);
lean_ctor_set_float(v___x_1790_, sizeof(void*)*3, v___x_1787_);
lean_ctor_set_float(v___x_1790_, sizeof(void*)*3 + 8, v___x_1787_);
lean_ctor_set_uint8(v___x_1790_, sizeof(void*)*3 + 16, v___x_1788_);
v___x_1791_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__2));
v___x_1792_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1790_);
lean_ctor_set(v___x_1792_, 1, v_a_1763_);
lean_ctor_set(v___x_1792_, 2, v___x_1791_);
lean_inc(v_ref_1761_);
v___x_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1793_, 0, v_ref_1761_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
v___x_1794_ = l_Lean_PersistentArray_push___redArg(v_traces_1782_, v___x_1793_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 0, v___x_1794_);
v___x_1796_ = v___x_1784_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1794_);
lean_ctor_set_uint64(v_reuseFailAlloc_1805_, sizeof(void*)*1, v_tid_1781_);
v___x_1796_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
lean_object* v___x_1798_; 
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 4, v___x_1796_);
v___x_1798_ = v___x_1779_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_env_1769_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v_nextMacroScope_1770_);
lean_ctor_set(v_reuseFailAlloc_1804_, 2, v_ngen_1771_);
lean_ctor_set(v_reuseFailAlloc_1804_, 3, v_auxDeclNGen_1772_);
lean_ctor_set(v_reuseFailAlloc_1804_, 4, v___x_1796_);
lean_ctor_set(v_reuseFailAlloc_1804_, 5, v_cache_1773_);
lean_ctor_set(v_reuseFailAlloc_1804_, 6, v_messages_1774_);
lean_ctor_set(v_reuseFailAlloc_1804_, 7, v_infoState_1775_);
lean_ctor_set(v_reuseFailAlloc_1804_, 8, v_snapshotTasks_1776_);
lean_ctor_set(v_reuseFailAlloc_1804_, 9, v_newDecls_1777_);
v___x_1798_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1802_; 
v___x_1799_ = lean_st_ref_set(v___y_1759_, v___x_1798_);
v___x_1800_ = lean_box(0);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1800_);
v___x_1802_ = v___x_1765_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1800_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___boxed(lean_object* v_cls_1809_, lean_object* v_msg_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v_cls_1809_, v_msg_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(lean_object* v_as_1817_, size_t v_i_1818_, size_t v_stop_1819_, lean_object* v_b_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v_a_1827_; uint8_t v___x_1831_; 
v___x_1831_ = lean_usize_dec_eq(v_i_1818_, v_stop_1819_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; lean_object* v___x_1835_; 
v___x_1832_ = lean_array_uget_borrowed(v_as_1817_, v_i_1818_);
v___x_1835_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v___x_1832_, v___y_1822_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; uint8_t v___x_1837_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
lean_dec_ref(v___x_1835_);
v___x_1837_ = lean_unbox(v_a_1836_);
lean_dec(v_a_1836_);
if (v___x_1837_ == 0)
{
goto v___jp_1833_;
}
else
{
v_a_1827_ = v_b_1820_;
goto v___jp_1826_;
}
}
else
{
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1838_; uint8_t v___x_1839_; 
v_a_1838_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1838_);
lean_dec_ref(v___x_1835_);
v___x_1839_ = lean_unbox(v_a_1838_);
lean_dec(v_a_1838_);
if (v___x_1839_ == 0)
{
v_a_1827_ = v_b_1820_;
goto v___jp_1826_;
}
else
{
goto v___jp_1833_;
}
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
lean_dec_ref(v_b_1820_);
v_a_1840_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1835_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1835_);
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
v___jp_1833_:
{
lean_object* v___x_1834_; 
lean_inc(v___x_1832_);
v___x_1834_ = lean_array_push(v_b_1820_, v___x_1832_);
v_a_1827_ = v___x_1834_;
goto v___jp_1826_;
}
}
else
{
lean_object* v___x_1848_; 
v___x_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1848_, 0, v_b_1820_);
return v___x_1848_;
}
v___jp_1826_:
{
size_t v___x_1828_; size_t v___x_1829_; 
v___x_1828_ = ((size_t)1ULL);
v___x_1829_ = lean_usize_add(v_i_1818_, v___x_1828_);
v_i_1818_ = v___x_1829_;
v_b_1820_ = v_a_1827_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8___boxed(lean_object* v_as_1849_, lean_object* v_i_1850_, lean_object* v_stop_1851_, lean_object* v_b_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
size_t v_i_boxed_1858_; size_t v_stop_boxed_1859_; lean_object* v_res_1860_; 
v_i_boxed_1858_ = lean_unbox_usize(v_i_1850_);
lean_dec(v_i_1850_);
v_stop_boxed_1859_ = lean_unbox_usize(v_stop_1851_);
lean_dec(v_stop_1851_);
v_res_1860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v_as_1849_, v_i_boxed_1858_, v_stop_boxed_1859_, v_b_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec_ref(v_as_1849_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14_spec__16(size_t v_sz_1861_, size_t v_i_1862_, lean_object* v_bs_1863_){
_start:
{
uint8_t v___x_1864_; 
v___x_1864_ = lean_usize_dec_lt(v_i_1862_, v_sz_1861_);
if (v___x_1864_ == 0)
{
return v_bs_1863_;
}
else
{
lean_object* v_v_1865_; lean_object* v_msg_1866_; lean_object* v___x_1867_; lean_object* v_bs_x27_1868_; size_t v___x_1869_; size_t v___x_1870_; lean_object* v___x_1871_; 
v_v_1865_ = lean_array_uget_borrowed(v_bs_1863_, v_i_1862_);
v_msg_1866_ = lean_ctor_get(v_v_1865_, 1);
lean_inc_ref(v_msg_1866_);
v___x_1867_ = lean_unsigned_to_nat(0u);
v_bs_x27_1868_ = lean_array_uset(v_bs_1863_, v_i_1862_, v___x_1867_);
v___x_1869_ = ((size_t)1ULL);
v___x_1870_ = lean_usize_add(v_i_1862_, v___x_1869_);
v___x_1871_ = lean_array_uset(v_bs_x27_1868_, v_i_1862_, v_msg_1866_);
v_i_1862_ = v___x_1870_;
v_bs_1863_ = v___x_1871_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14_spec__16___boxed(lean_object* v_sz_1873_, lean_object* v_i_1874_, lean_object* v_bs_1875_){
_start:
{
size_t v_sz_boxed_1876_; size_t v_i_boxed_1877_; lean_object* v_res_1878_; 
v_sz_boxed_1876_ = lean_unbox_usize(v_sz_1873_);
lean_dec(v_sz_1873_);
v_i_boxed_1877_ = lean_unbox_usize(v_i_1874_);
lean_dec(v_i_1874_);
v_res_1878_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14_spec__16(v_sz_boxed_1876_, v_i_boxed_1877_, v_bs_1875_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14(lean_object* v_oldTraces_1879_, lean_object* v_data_1880_, lean_object* v_ref_1881_, lean_object* v_msg_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v_fileName_1888_; lean_object* v_fileMap_1889_; lean_object* v_options_1890_; lean_object* v_currRecDepth_1891_; lean_object* v_maxRecDepth_1892_; lean_object* v_ref_1893_; lean_object* v_currNamespace_1894_; lean_object* v_openDecls_1895_; lean_object* v_initHeartbeats_1896_; lean_object* v_maxHeartbeats_1897_; lean_object* v_quotContext_1898_; lean_object* v_currMacroScope_1899_; uint8_t v_diag_1900_; lean_object* v_cancelTk_x3f_1901_; uint8_t v_suppressElabErrors_1902_; lean_object* v_inheritedTraceOptions_1903_; lean_object* v___x_1904_; lean_object* v_traceState_1905_; lean_object* v_traces_1906_; lean_object* v_ref_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; size_t v_sz_1910_; size_t v___x_1911_; lean_object* v___x_1912_; lean_object* v_msg_1913_; lean_object* v___x_1914_; lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1953_; 
v_fileName_1888_ = lean_ctor_get(v___y_1885_, 0);
v_fileMap_1889_ = lean_ctor_get(v___y_1885_, 1);
v_options_1890_ = lean_ctor_get(v___y_1885_, 2);
v_currRecDepth_1891_ = lean_ctor_get(v___y_1885_, 3);
v_maxRecDepth_1892_ = lean_ctor_get(v___y_1885_, 4);
v_ref_1893_ = lean_ctor_get(v___y_1885_, 5);
v_currNamespace_1894_ = lean_ctor_get(v___y_1885_, 6);
v_openDecls_1895_ = lean_ctor_get(v___y_1885_, 7);
v_initHeartbeats_1896_ = lean_ctor_get(v___y_1885_, 8);
v_maxHeartbeats_1897_ = lean_ctor_get(v___y_1885_, 9);
v_quotContext_1898_ = lean_ctor_get(v___y_1885_, 10);
v_currMacroScope_1899_ = lean_ctor_get(v___y_1885_, 11);
v_diag_1900_ = lean_ctor_get_uint8(v___y_1885_, sizeof(void*)*14);
v_cancelTk_x3f_1901_ = lean_ctor_get(v___y_1885_, 12);
v_suppressElabErrors_1902_ = lean_ctor_get_uint8(v___y_1885_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1903_ = lean_ctor_get(v___y_1885_, 13);
v___x_1904_ = lean_st_ref_get(v___y_1886_);
v_traceState_1905_ = lean_ctor_get(v___x_1904_, 4);
lean_inc_ref(v_traceState_1905_);
lean_dec(v___x_1904_);
v_traces_1906_ = lean_ctor_get(v_traceState_1905_, 0);
lean_inc_ref(v_traces_1906_);
lean_dec_ref(v_traceState_1905_);
v_ref_1907_ = l_Lean_replaceRef(v_ref_1881_, v_ref_1893_);
lean_inc_ref(v_inheritedTraceOptions_1903_);
lean_inc(v_cancelTk_x3f_1901_);
lean_inc(v_currMacroScope_1899_);
lean_inc(v_quotContext_1898_);
lean_inc(v_maxHeartbeats_1897_);
lean_inc(v_initHeartbeats_1896_);
lean_inc(v_openDecls_1895_);
lean_inc(v_currNamespace_1894_);
lean_inc(v_maxRecDepth_1892_);
lean_inc(v_currRecDepth_1891_);
lean_inc_ref(v_options_1890_);
lean_inc_ref(v_fileMap_1889_);
lean_inc_ref(v_fileName_1888_);
v___x_1908_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1908_, 0, v_fileName_1888_);
lean_ctor_set(v___x_1908_, 1, v_fileMap_1889_);
lean_ctor_set(v___x_1908_, 2, v_options_1890_);
lean_ctor_set(v___x_1908_, 3, v_currRecDepth_1891_);
lean_ctor_set(v___x_1908_, 4, v_maxRecDepth_1892_);
lean_ctor_set(v___x_1908_, 5, v_ref_1907_);
lean_ctor_set(v___x_1908_, 6, v_currNamespace_1894_);
lean_ctor_set(v___x_1908_, 7, v_openDecls_1895_);
lean_ctor_set(v___x_1908_, 8, v_initHeartbeats_1896_);
lean_ctor_set(v___x_1908_, 9, v_maxHeartbeats_1897_);
lean_ctor_set(v___x_1908_, 10, v_quotContext_1898_);
lean_ctor_set(v___x_1908_, 11, v_currMacroScope_1899_);
lean_ctor_set(v___x_1908_, 12, v_cancelTk_x3f_1901_);
lean_ctor_set(v___x_1908_, 13, v_inheritedTraceOptions_1903_);
lean_ctor_set_uint8(v___x_1908_, sizeof(void*)*14, v_diag_1900_);
lean_ctor_set_uint8(v___x_1908_, sizeof(void*)*14 + 1, v_suppressElabErrors_1902_);
v___x_1909_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1906_);
lean_dec_ref(v_traces_1906_);
v_sz_1910_ = lean_array_size(v___x_1909_);
v___x_1911_ = ((size_t)0ULL);
v___x_1912_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14_spec__16(v_sz_1910_, v___x_1911_, v___x_1909_);
v_msg_1913_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1913_, 0, v_data_1880_);
lean_ctor_set(v_msg_1913_, 1, v_msg_1882_);
lean_ctor_set(v_msg_1913_, 2, v___x_1912_);
v___x_1914_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_1913_, v___y_1883_, v___y_1884_, v___x_1908_, v___y_1886_);
lean_dec_ref(v___x_1908_);
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1917_ = v___x_1914_;
v_isShared_1918_ = v_isSharedCheck_1953_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1914_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1953_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1919_; lean_object* v_traceState_1920_; lean_object* v_env_1921_; lean_object* v_nextMacroScope_1922_; lean_object* v_ngen_1923_; lean_object* v_auxDeclNGen_1924_; lean_object* v_cache_1925_; lean_object* v_messages_1926_; lean_object* v_infoState_1927_; lean_object* v_snapshotTasks_1928_; lean_object* v_newDecls_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1952_; 
v___x_1919_ = lean_st_ref_take(v___y_1886_);
v_traceState_1920_ = lean_ctor_get(v___x_1919_, 4);
v_env_1921_ = lean_ctor_get(v___x_1919_, 0);
v_nextMacroScope_1922_ = lean_ctor_get(v___x_1919_, 1);
v_ngen_1923_ = lean_ctor_get(v___x_1919_, 2);
v_auxDeclNGen_1924_ = lean_ctor_get(v___x_1919_, 3);
v_cache_1925_ = lean_ctor_get(v___x_1919_, 5);
v_messages_1926_ = lean_ctor_get(v___x_1919_, 6);
v_infoState_1927_ = lean_ctor_get(v___x_1919_, 7);
v_snapshotTasks_1928_ = lean_ctor_get(v___x_1919_, 8);
v_newDecls_1929_ = lean_ctor_get(v___x_1919_, 9);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1931_ = v___x_1919_;
v_isShared_1932_ = v_isSharedCheck_1952_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_newDecls_1929_);
lean_inc(v_snapshotTasks_1928_);
lean_inc(v_infoState_1927_);
lean_inc(v_messages_1926_);
lean_inc(v_cache_1925_);
lean_inc(v_traceState_1920_);
lean_inc(v_auxDeclNGen_1924_);
lean_inc(v_ngen_1923_);
lean_inc(v_nextMacroScope_1922_);
lean_inc(v_env_1921_);
lean_dec(v___x_1919_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1952_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
uint64_t v_tid_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1950_; 
v_tid_1933_ = lean_ctor_get_uint64(v_traceState_1920_, sizeof(void*)*1);
v_isSharedCheck_1950_ = !lean_is_exclusive(v_traceState_1920_);
if (v_isSharedCheck_1950_ == 0)
{
lean_object* v_unused_1951_; 
v_unused_1951_ = lean_ctor_get(v_traceState_1920_, 0);
lean_dec(v_unused_1951_);
v___x_1935_ = v_traceState_1920_;
v_isShared_1936_ = v_isSharedCheck_1950_;
goto v_resetjp_1934_;
}
else
{
lean_dec(v_traceState_1920_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1950_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1940_; 
v___x_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1937_, 0, v_ref_1881_);
lean_ctor_set(v___x_1937_, 1, v_a_1915_);
v___x_1938_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1879_, v___x_1937_);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 0, v___x_1938_);
v___x_1940_ = v___x_1935_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1938_);
lean_ctor_set_uint64(v_reuseFailAlloc_1949_, sizeof(void*)*1, v_tid_1933_);
v___x_1940_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
lean_object* v___x_1942_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 4, v___x_1940_);
v___x_1942_ = v___x_1931_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_env_1921_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_nextMacroScope_1922_);
lean_ctor_set(v_reuseFailAlloc_1948_, 2, v_ngen_1923_);
lean_ctor_set(v_reuseFailAlloc_1948_, 3, v_auxDeclNGen_1924_);
lean_ctor_set(v_reuseFailAlloc_1948_, 4, v___x_1940_);
lean_ctor_set(v_reuseFailAlloc_1948_, 5, v_cache_1925_);
lean_ctor_set(v_reuseFailAlloc_1948_, 6, v_messages_1926_);
lean_ctor_set(v_reuseFailAlloc_1948_, 7, v_infoState_1927_);
lean_ctor_set(v_reuseFailAlloc_1948_, 8, v_snapshotTasks_1928_);
lean_ctor_set(v_reuseFailAlloc_1948_, 9, v_newDecls_1929_);
v___x_1942_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1946_; 
v___x_1943_ = lean_st_ref_set(v___y_1886_, v___x_1942_);
v___x_1944_ = lean_box(0);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 0, v___x_1944_);
v___x_1946_ = v___x_1917_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___boxed(lean_object* v_oldTraces_1954_, lean_object* v_data_1955_, lean_object* v_ref_1956_, lean_object* v_msg_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14(v_oldTraces_1954_, v_data_1955_, v_ref_1956_, v_msg_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(lean_object* v_opts_1964_, lean_object* v_opt_1965_){
_start:
{
lean_object* v_name_1966_; lean_object* v_defValue_1967_; lean_object* v_map_1968_; lean_object* v___x_1969_; 
v_name_1966_ = lean_ctor_get(v_opt_1965_, 0);
v_defValue_1967_ = lean_ctor_get(v_opt_1965_, 1);
v_map_1968_ = lean_ctor_get(v_opts_1964_, 0);
v___x_1969_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1968_, v_name_1966_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_inc(v_defValue_1967_);
return v_defValue_1967_;
}
else
{
lean_object* v_val_1970_; 
v_val_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_val_1970_);
lean_dec_ref(v___x_1969_);
if (lean_obj_tag(v_val_1970_) == 3)
{
lean_object* v_v_1971_; 
v_v_1971_ = lean_ctor_get(v_val_1970_, 0);
lean_inc(v_v_1971_);
lean_dec_ref(v_val_1970_);
return v_v_1971_;
}
else
{
lean_dec(v_val_1970_);
lean_inc(v_defValue_1967_);
return v_defValue_1967_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16___boxed(lean_object* v_opts_1972_, lean_object* v_opt_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_1972_, v_opt_1973_);
lean_dec_ref(v_opt_1973_);
lean_dec_ref(v_opts_1972_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___redArg(lean_object* v_x_1975_){
_start:
{
if (lean_obj_tag(v_x_1975_) == 0)
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1984_; 
v_a_1977_ = lean_ctor_get(v_x_1975_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v_x_1975_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1979_ = v_x_1975_;
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v_x_1975_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
lean_ctor_set_tag(v___x_1979_, 1);
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_a_1977_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
v_a_1985_ = lean_ctor_get(v_x_1975_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v_x_1975_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v_x_1975_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v_x_1975_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
lean_ctor_set_tag(v___x_1987_, 0);
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___redArg___boxed(lean_object* v_x_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___redArg(v_x_1993_);
return v_res_1995_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(lean_object* v_e_1996_){
_start:
{
if (lean_obj_tag(v_e_1996_) == 0)
{
uint8_t v___x_1997_; 
v___x_1997_ = 2;
return v___x_1997_;
}
else
{
uint8_t v___x_1998_; 
v___x_1998_ = 0;
return v___x_1998_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13___boxed(lean_object* v_e_1999_){
_start:
{
uint8_t v_res_2000_; lean_object* v_r_2001_; 
v_res_2000_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(v_e_1999_);
lean_dec_ref(v_e_1999_);
v_r_2001_ = lean_box(v_res_2000_);
return v_r_2001_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1(void){
_start:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__0));
v___x_2004_ = l_Lean_stringToMessageData(v___x_2003_);
return v___x_2004_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2(void){
_start:
{
lean_object* v___x_2005_; double v___x_2006_; 
v___x_2005_ = lean_unsigned_to_nat(1000u);
v___x_2006_ = lean_float_of_nat(v___x_2005_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(lean_object* v_cls_2007_, uint8_t v_collapsed_2008_, lean_object* v_tag_2009_, lean_object* v_opts_2010_, uint8_t v_clsEnabled_2011_, lean_object* v_oldTraces_2012_, lean_object* v_msg_2013_, lean_object* v_resStartStop_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v_fst_2020_; lean_object* v_snd_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2120_; 
v_fst_2020_ = lean_ctor_get(v_resStartStop_2014_, 0);
v_snd_2021_ = lean_ctor_get(v_resStartStop_2014_, 1);
v_isSharedCheck_2120_ = !lean_is_exclusive(v_resStartStop_2014_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2023_ = v_resStartStop_2014_;
v_isShared_2024_ = v_isSharedCheck_2120_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_snd_2021_);
lean_inc(v_fst_2020_);
lean_dec(v_resStartStop_2014_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2120_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v_data_2028_; lean_object* v_fst_2039_; lean_object* v_snd_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2119_; 
v_fst_2039_ = lean_ctor_get(v_snd_2021_, 0);
v_snd_2040_ = lean_ctor_get(v_snd_2021_, 1);
v_isSharedCheck_2119_ = !lean_is_exclusive(v_snd_2021_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2042_ = v_snd_2021_;
v_isShared_2043_ = v_isSharedCheck_2119_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_snd_2040_);
lean_inc(v_fst_2039_);
lean_dec(v_snd_2021_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2119_;
goto v_resetjp_2041_;
}
v___jp_2025_:
{
lean_object* v___x_2029_; 
lean_inc(v___y_2026_);
v___x_2029_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14(v_oldTraces_2012_, v_data_2028_, v___y_2026_, v___y_2027_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v___x_2030_; 
lean_dec_ref(v___x_2029_);
v___x_2030_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___redArg(v_fst_2020_);
return v___x_2030_;
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec(v_fst_2020_);
v_a_2031_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_2029_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2029_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; uint8_t v___x_2045_; lean_object* v___y_2047_; lean_object* v_a_2048_; uint8_t v___y_2072_; double v___y_2104_; 
v___x_2044_ = l_Lean_trace_profiler;
v___x_2045_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_opts_2010_, v___x_2044_);
if (v___x_2045_ == 0)
{
v___y_2072_ = v___x_2045_;
goto v___jp_2071_;
}
else
{
lean_object* v___x_2109_; uint8_t v___x_2110_; 
v___x_2109_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2110_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_opts_2010_, v___x_2109_);
if (v___x_2110_ == 0)
{
lean_object* v___x_2111_; lean_object* v___x_2112_; double v___x_2113_; double v___x_2114_; double v___x_2115_; 
v___x_2111_ = l_Lean_trace_profiler_threshold;
v___x_2112_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_2010_, v___x_2111_);
v___x_2113_ = lean_float_of_nat(v___x_2112_);
v___x_2114_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2);
v___x_2115_ = lean_float_div(v___x_2113_, v___x_2114_);
v___y_2104_ = v___x_2115_;
goto v___jp_2103_;
}
else
{
lean_object* v___x_2116_; lean_object* v___x_2117_; double v___x_2118_; 
v___x_2116_ = l_Lean_trace_profiler_threshold;
v___x_2117_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_2010_, v___x_2116_);
v___x_2118_ = lean_float_of_nat(v___x_2117_);
v___y_2104_ = v___x_2118_;
goto v___jp_2103_;
}
}
v___jp_2046_:
{
uint8_t v_result_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2054_; 
v_result_2049_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(v_fst_2020_);
v___x_2050_ = l_Lean_TraceResult_toEmoji(v_result_2049_);
v___x_2051_ = l_Lean_stringToMessageData(v___x_2050_);
v___x_2052_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
if (v_isShared_2043_ == 0)
{
lean_ctor_set_tag(v___x_2042_, 7);
lean_ctor_set(v___x_2042_, 1, v___x_2052_);
lean_ctor_set(v___x_2042_, 0, v___x_2051_);
v___x_2054_ = v___x_2042_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2051_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
lean_object* v_m_2056_; 
if (v_isShared_2024_ == 0)
{
lean_ctor_set_tag(v___x_2023_, 7);
lean_ctor_set(v___x_2023_, 1, v_a_2048_);
lean_ctor_set(v___x_2023_, 0, v___x_2054_);
v_m_2056_ = v___x_2023_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2054_);
lean_ctor_set(v_reuseFailAlloc_2064_, 1, v_a_2048_);
v_m_2056_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; double v___x_2059_; lean_object* v_data_2060_; 
v___x_2057_ = lean_box(v_result_2049_);
v___x_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
v___x_2059_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0);
lean_inc_ref(v_tag_2009_);
lean_inc_ref(v___x_2058_);
lean_inc(v_cls_2007_);
v_data_2060_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2060_, 0, v_cls_2007_);
lean_ctor_set(v_data_2060_, 1, v___x_2058_);
lean_ctor_set(v_data_2060_, 2, v_tag_2009_);
lean_ctor_set_float(v_data_2060_, sizeof(void*)*3, v___x_2059_);
lean_ctor_set_float(v_data_2060_, sizeof(void*)*3 + 8, v___x_2059_);
lean_ctor_set_uint8(v_data_2060_, sizeof(void*)*3 + 16, v_collapsed_2008_);
if (v___x_2045_ == 0)
{
lean_dec_ref(v___x_2058_);
lean_dec(v_snd_2040_);
lean_dec(v_fst_2039_);
lean_dec_ref(v_tag_2009_);
lean_dec(v_cls_2007_);
v___y_2026_ = v___y_2047_;
v___y_2027_ = v_m_2056_;
v_data_2028_ = v_data_2060_;
goto v___jp_2025_;
}
else
{
lean_object* v_data_2061_; double v___x_2062_; double v___x_2063_; 
lean_dec_ref(v_data_2060_);
v_data_2061_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2061_, 0, v_cls_2007_);
lean_ctor_set(v_data_2061_, 1, v___x_2058_);
lean_ctor_set(v_data_2061_, 2, v_tag_2009_);
v___x_2062_ = lean_unbox_float(v_fst_2039_);
lean_dec(v_fst_2039_);
lean_ctor_set_float(v_data_2061_, sizeof(void*)*3, v___x_2062_);
v___x_2063_ = lean_unbox_float(v_snd_2040_);
lean_dec(v_snd_2040_);
lean_ctor_set_float(v_data_2061_, sizeof(void*)*3 + 8, v___x_2063_);
lean_ctor_set_uint8(v_data_2061_, sizeof(void*)*3 + 16, v_collapsed_2008_);
v___y_2026_ = v___y_2047_;
v___y_2027_ = v_m_2056_;
v_data_2028_ = v_data_2061_;
goto v___jp_2025_;
}
}
}
}
v___jp_2066_:
{
lean_object* v_ref_2067_; lean_object* v___x_2068_; 
v_ref_2067_ = lean_ctor_get(v___y_2017_, 5);
lean_inc(v___y_2018_);
lean_inc_ref(v___y_2017_);
lean_inc(v___y_2016_);
lean_inc_ref(v___y_2015_);
lean_inc(v_fst_2020_);
v___x_2068_ = lean_apply_6(v_msg_2013_, v_fst_2020_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, lean_box(0));
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_a_2069_);
lean_dec_ref(v___x_2068_);
v___y_2047_ = v_ref_2067_;
v_a_2048_ = v_a_2069_;
goto v___jp_2046_;
}
else
{
lean_object* v___x_2070_; 
lean_dec_ref(v___x_2068_);
v___x_2070_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1);
v___y_2047_ = v_ref_2067_;
v_a_2048_ = v___x_2070_;
goto v___jp_2046_;
}
}
v___jp_2071_:
{
if (v_clsEnabled_2011_ == 0)
{
if (v___y_2072_ == 0)
{
lean_object* v___x_2073_; lean_object* v_traceState_2074_; lean_object* v_env_2075_; lean_object* v_nextMacroScope_2076_; lean_object* v_ngen_2077_; lean_object* v_auxDeclNGen_2078_; lean_object* v_cache_2079_; lean_object* v_messages_2080_; lean_object* v_infoState_2081_; lean_object* v_snapshotTasks_2082_; lean_object* v_newDecls_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2102_; 
lean_del_object(v___x_2042_);
lean_dec(v_snd_2040_);
lean_dec(v_fst_2039_);
lean_del_object(v___x_2023_);
lean_dec_ref(v_msg_2013_);
lean_dec_ref(v_tag_2009_);
lean_dec(v_cls_2007_);
v___x_2073_ = lean_st_ref_take(v___y_2018_);
v_traceState_2074_ = lean_ctor_get(v___x_2073_, 4);
v_env_2075_ = lean_ctor_get(v___x_2073_, 0);
v_nextMacroScope_2076_ = lean_ctor_get(v___x_2073_, 1);
v_ngen_2077_ = lean_ctor_get(v___x_2073_, 2);
v_auxDeclNGen_2078_ = lean_ctor_get(v___x_2073_, 3);
v_cache_2079_ = lean_ctor_get(v___x_2073_, 5);
v_messages_2080_ = lean_ctor_get(v___x_2073_, 6);
v_infoState_2081_ = lean_ctor_get(v___x_2073_, 7);
v_snapshotTasks_2082_ = lean_ctor_get(v___x_2073_, 8);
v_newDecls_2083_ = lean_ctor_get(v___x_2073_, 9);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2085_ = v___x_2073_;
v_isShared_2086_ = v_isSharedCheck_2102_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_newDecls_2083_);
lean_inc(v_snapshotTasks_2082_);
lean_inc(v_infoState_2081_);
lean_inc(v_messages_2080_);
lean_inc(v_cache_2079_);
lean_inc(v_traceState_2074_);
lean_inc(v_auxDeclNGen_2078_);
lean_inc(v_ngen_2077_);
lean_inc(v_nextMacroScope_2076_);
lean_inc(v_env_2075_);
lean_dec(v___x_2073_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2102_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
uint64_t v_tid_2087_; lean_object* v_traces_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2101_; 
v_tid_2087_ = lean_ctor_get_uint64(v_traceState_2074_, sizeof(void*)*1);
v_traces_2088_ = lean_ctor_get(v_traceState_2074_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v_traceState_2074_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2090_ = v_traceState_2074_;
v_isShared_2091_ = v_isSharedCheck_2101_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_traces_2088_);
lean_dec(v_traceState_2074_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2101_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2092_; lean_object* v___x_2094_; 
v___x_2092_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2012_, v_traces_2088_);
lean_dec_ref(v_traces_2088_);
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 0, v___x_2092_);
v___x_2094_ = v___x_2090_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2092_);
lean_ctor_set_uint64(v_reuseFailAlloc_2100_, sizeof(void*)*1, v_tid_2087_);
v___x_2094_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
lean_object* v___x_2096_; 
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 4, v___x_2094_);
v___x_2096_ = v___x_2085_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_env_2075_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v_nextMacroScope_2076_);
lean_ctor_set(v_reuseFailAlloc_2099_, 2, v_ngen_2077_);
lean_ctor_set(v_reuseFailAlloc_2099_, 3, v_auxDeclNGen_2078_);
lean_ctor_set(v_reuseFailAlloc_2099_, 4, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2099_, 5, v_cache_2079_);
lean_ctor_set(v_reuseFailAlloc_2099_, 6, v_messages_2080_);
lean_ctor_set(v_reuseFailAlloc_2099_, 7, v_infoState_2081_);
lean_ctor_set(v_reuseFailAlloc_2099_, 8, v_snapshotTasks_2082_);
lean_ctor_set(v_reuseFailAlloc_2099_, 9, v_newDecls_2083_);
v___x_2096_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = lean_st_ref_set(v___y_2018_, v___x_2096_);
v___x_2098_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___redArg(v_fst_2020_);
return v___x_2098_;
}
}
}
}
}
else
{
goto v___jp_2066_;
}
}
else
{
goto v___jp_2066_;
}
}
v___jp_2103_:
{
double v___x_2105_; double v___x_2106_; double v___x_2107_; uint8_t v___x_2108_; 
v___x_2105_ = lean_unbox_float(v_snd_2040_);
v___x_2106_ = lean_unbox_float(v_fst_2039_);
v___x_2107_ = lean_float_sub(v___x_2105_, v___x_2106_);
v___x_2108_ = lean_float_decLt(v___y_2104_, v___x_2107_);
v___y_2072_ = v___x_2108_;
goto v___jp_2071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___boxed(lean_object* v_cls_2121_, lean_object* v_collapsed_2122_, lean_object* v_tag_2123_, lean_object* v_opts_2124_, lean_object* v_clsEnabled_2125_, lean_object* v_oldTraces_2126_, lean_object* v_msg_2127_, lean_object* v_resStartStop_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
uint8_t v_collapsed_boxed_2134_; uint8_t v_clsEnabled_boxed_2135_; lean_object* v_res_2136_; 
v_collapsed_boxed_2134_ = lean_unbox(v_collapsed_2122_);
v_clsEnabled_boxed_2135_ = lean_unbox(v_clsEnabled_2125_);
v_res_2136_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v_cls_2121_, v_collapsed_boxed_2134_, v_tag_2123_, v_opts_2124_, v_clsEnabled_boxed_2135_, v_oldTraces_2126_, v_msg_2127_, v_resStartStop_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec_ref(v_opts_2124_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_rwMatcher_spec__14___redArg(lean_object* v_a_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Lean_Meta_reduceRecMatcher_x3f(v_a_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2157_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2146_ = v___x_2143_;
v_isShared_2147_ = v_isSharedCheck_2157_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2143_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2157_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
if (lean_obj_tag(v_a_2144_) == 1)
{
lean_object* v_val_2148_; lean_object* v___x_2149_; 
lean_del_object(v___x_2146_);
lean_dec_ref(v_a_2137_);
v_val_2148_ = lean_ctor_get(v_a_2144_, 0);
lean_inc(v_val_2148_);
lean_dec_ref(v_a_2144_);
v___x_2149_ = l_Lean_Expr_headBeta(v_val_2148_);
v_a_2137_ = v___x_2149_;
goto _start;
}
else
{
lean_object* v___x_2151_; uint8_t v___x_2152_; 
lean_dec(v_a_2144_);
lean_inc_ref(v_a_2137_);
v___x_2151_ = l_Lean_Expr_headBeta(v_a_2137_);
v___x_2152_ = lean_expr_eqv(v_a_2137_, v___x_2151_);
if (v___x_2152_ == 0)
{
lean_del_object(v___x_2146_);
lean_dec_ref(v_a_2137_);
v_a_2137_ = v___x_2151_;
goto _start;
}
else
{
lean_object* v___x_2155_; 
lean_dec_ref(v___x_2151_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v_a_2137_);
v___x_2155_ = v___x_2146_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2137_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
}
else
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
lean_dec_ref(v_a_2137_);
v_a_2158_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2143_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2143_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2158_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_rwMatcher_spec__14___redArg___boxed(lean_object* v_a_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_rwMatcher_spec__14___redArg(v_a_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
return v_res_2172_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__3(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2177_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__2));
v___x_2178_ = l_Lean_stringToMessageData(v___x_2177_);
return v___x_2178_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__5(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__4));
v___x_2181_ = l_Lean_stringToMessageData(v___x_2180_);
return v___x_2181_;
}
}
static double _init_l_Lean_Meta_rwMatcher___closed__6(void){
_start:
{
lean_object* v___x_2182_; double v___x_2183_; 
v___x_2182_ = lean_unsigned_to_nat(1000000000u);
v___x_2183_ = lean_float_of_nat(v___x_2182_);
return v___x_2183_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__8(void){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__7));
v___x_2186_ = l_Lean_stringToMessageData(v___x_2185_);
return v___x_2186_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__13(void){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2194_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2195_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
v___x_2196_ = l_Lean_Name_append(v___x_2195_, v___x_2194_);
return v___x_2196_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__15(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2198_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__14));
v___x_2199_ = l_Lean_stringToMessageData(v___x_2198_);
return v___x_2199_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__17(void){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__16));
v___x_2202_ = l_Lean_stringToMessageData(v___x_2201_);
return v___x_2202_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__19(void){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2204_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__18));
v___x_2205_ = l_Lean_stringToMessageData(v___x_2204_);
return v___x_2205_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__21(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__20));
v___x_2208_ = l_Lean_stringToMessageData(v___x_2207_);
return v___x_2208_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__22(void){
_start:
{
lean_object* v___x_2209_; lean_object* v_dummy_2210_; 
v___x_2209_ = lean_box(0);
v_dummy_2210_ = l_Lean_Expr_sort___override(v___x_2209_);
return v_dummy_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher(lean_object* v_altIdx_2220_, lean_object* v_e_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_){
_start:
{
lean_object* v___y_2228_; uint8_t v___y_2247_; uint8_t v___y_2252_; lean_object* v___y_2257_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; uint8_t v___y_2265_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v_a_2296_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2303_; uint8_t v___y_2306_; lean_object* v___y_2307_; lean_object* v_proof_2308_; uint8_t v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; uint8_t v___y_2329_; lean_object* v___y_2330_; lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2333_; uint8_t v___y_2334_; uint8_t v___y_2347_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; uint8_t v___y_2351_; lean_object* v___y_2352_; lean_object* v___y_2353_; lean_object* v___y_2354_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; uint8_t v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; uint8_t v___y_2376_; lean_object* v___y_2377_; uint8_t v___y_2378_; lean_object* v___y_2379_; lean_object* v_a_2380_; lean_object* v___y_2397_; uint8_t v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; uint8_t v___y_2404_; lean_object* v___y_2405_; uint8_t v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2413_; uint8_t v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; size_t v___y_2417_; lean_object* v___y_2418_; uint8_t v___y_2419_; uint8_t v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2441_; uint8_t v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; size_t v___y_2445_; uint8_t v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; uint8_t v_fst_2449_; lean_object* v_fst_2450_; lean_object* v_snd_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; uint8_t v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; uint8_t v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v_a_2486_; uint8_t v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; uint8_t v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v_a_2506_; uint8_t v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; uint8_t v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; uint8_t v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; uint8_t v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v_a_2540_; uint8_t v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; uint8_t v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v_a_2563_; uint8_t v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; uint8_t v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; uint8_t v___y_2587_; lean_object* v___y_2588_; uint8_t v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; uint8_t v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; uint8_t v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; uint8_t v___y_2666_; lean_object* v___x_2857_; uint8_t v___x_2858_; 
v___x_2857_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__25));
v___x_2858_ = l_Lean_Expr_isAppOf(v_e_2221_, v___x_2857_);
if (v___x_2858_ == 0)
{
lean_object* v___x_2859_; uint8_t v___x_2860_; 
v___x_2859_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__27));
v___x_2860_ = l_Lean_Expr_isAppOf(v_e_2221_, v___x_2859_);
v___y_2666_ = v___x_2860_;
goto v___jp_2665_;
}
else
{
v___y_2666_ = v___x_2858_;
goto v___jp_2665_;
}
v___jp_2227_:
{
if (lean_obj_tag(v___y_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2237_; 
v_a_2229_ = lean_ctor_get(v___y_2228_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___y_2228_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2231_ = v___y_2228_;
v_isShared_2232_ = v_isSharedCheck_2237_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___y_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2237_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v_a_2233_; lean_object* v___x_2235_; 
v_a_2233_ = lean_ctor_get(v_a_2229_, 0);
lean_inc(v_a_2233_);
lean_dec(v_a_2229_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 0, v_a_2233_);
v___x_2235_ = v___x_2231_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2233_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
v_a_2238_ = lean_ctor_get(v___y_2228_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___y_2228_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___y_2228_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___y_2228_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
v___jp_2246_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2248_ = lean_box(0);
v___x_2249_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2249_, 0, v_e_2221_);
lean_ctor_set(v___x_2249_, 1, v___x_2248_);
lean_ctor_set_uint8(v___x_2249_, sizeof(void*)*2, v___y_2247_);
v___x_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
return v___x_2250_;
}
v___jp_2251_:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2253_ = lean_box(0);
v___x_2254_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2254_, 0, v_e_2221_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
lean_ctor_set_uint8(v___x_2254_, sizeof(void*)*2, v___y_2252_);
v___x_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
return v___x_2255_;
}
v___jp_2256_:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = lean_box(0);
lean_inc(v_a_2225_);
lean_inc_ref(v_a_2224_);
lean_inc(v_a_2223_);
lean_inc_ref(v_a_2222_);
v___x_2259_ = lean_apply_6(v___y_2257_, v___x_2258_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, lean_box(0));
v___y_2228_ = v___x_2259_;
goto v___jp_2227_;
}
v___jp_2260_:
{
if (v___y_2265_ == 0)
{
lean_object* v_options_2266_; uint8_t v_hasTrace_2267_; 
v_options_2266_ = lean_ctor_get(v_a_2224_, 2);
v_hasTrace_2267_ = lean_ctor_get_uint8(v_options_2266_, sizeof(void*)*1);
if (v_hasTrace_2267_ == 0)
{
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec(v___y_2261_);
v___y_2257_ = v___y_2264_;
goto v___jp_2256_;
}
else
{
lean_object* v_inheritedTraceOptions_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; uint8_t v___x_2271_; 
v_inheritedTraceOptions_2268_ = lean_ctor_get(v_a_2224_, 13);
v___x_2269_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2262_);
v___x_2270_ = l_Lean_Name_append(v___x_2269_, v___y_2262_);
v___x_2271_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2268_, v_options_2266_, v___x_2270_);
lean_dec(v___x_2270_);
if (v___x_2271_ == 0)
{
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec(v___y_2261_);
v___y_2257_ = v___y_2264_;
goto v___jp_2256_;
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2272_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__3, &l_Lean_Meta_rwMatcher___closed__3_once, _init_l_Lean_Meta_rwMatcher___closed__3);
v___x_2273_ = l_Lean_MessageData_ofConstName(v___y_2261_, v___y_2265_);
v___x_2274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2272_);
lean_ctor_set(v___x_2274_, 1, v___x_2273_);
v___x_2275_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__5, &l_Lean_Meta_rwMatcher___closed__5_once, _init_l_Lean_Meta_rwMatcher___closed__5);
v___x_2276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2274_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
v___x_2277_ = l_Lean_Exception_toMessageData(v___y_2263_);
v___x_2278_ = l_Lean_indentD(v___x_2277_);
v___x_2279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2276_);
lean_ctor_set(v___x_2279_, 1, v___x_2278_);
v___x_2280_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2262_, v___x_2279_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; lean_object* v___x_2282_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_a_2281_);
lean_dec_ref(v___x_2280_);
lean_inc(v_a_2225_);
lean_inc_ref(v_a_2224_);
lean_inc(v_a_2223_);
lean_inc_ref(v_a_2222_);
v___x_2282_ = lean_apply_6(v___y_2264_, v_a_2281_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, lean_box(0));
v___y_2228_ = v___x_2282_;
goto v___jp_2227_;
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec_ref(v___y_2264_);
v_a_2283_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2280_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2280_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
}
}
else
{
lean_object* v___x_2291_; 
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2262_);
lean_dec(v___y_2261_);
v___x_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2291_, 0, v___y_2263_);
return v___x_2291_;
}
}
v___jp_2292_:
{
uint8_t v___x_2297_; 
v___x_2297_ = l_Lean_Exception_isInterrupt(v_a_2296_);
if (v___x_2297_ == 0)
{
uint8_t v___x_2298_; 
lean_inc_ref(v_a_2296_);
v___x_2298_ = l_Lean_Exception_isRuntime(v_a_2296_);
v___y_2261_ = v___y_2293_;
v___y_2262_ = v___y_2294_;
v___y_2263_ = v_a_2296_;
v___y_2264_ = v___y_2295_;
v___y_2265_ = v___x_2298_;
goto v___jp_2260_;
}
else
{
v___y_2261_ = v___y_2293_;
v___y_2262_ = v___y_2294_;
v___y_2263_ = v_a_2296_;
v___y_2264_ = v___y_2295_;
v___y_2265_ = v___x_2297_;
goto v___jp_2260_;
}
}
v___jp_2299_:
{
if (lean_obj_tag(v___y_2303_) == 0)
{
lean_dec_ref(v___y_2302_);
lean_dec(v___y_2301_);
lean_dec(v___y_2300_);
return v___y_2303_;
}
else
{
lean_object* v_a_2304_; 
v_a_2304_ = lean_ctor_get(v___y_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref(v___y_2303_);
v___y_2293_ = v___y_2300_;
v___y_2294_ = v___y_2301_;
v___y_2295_ = v___y_2302_;
v_a_2296_ = v_a_2304_;
goto v___jp_2292_;
}
}
v___jp_2305_:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2309_, 0, v_proof_2308_);
v___x_2310_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2310_, 0, v___y_2307_);
lean_ctor_set(v___x_2310_, 1, v___x_2309_);
lean_ctor_set_uint8(v___x_2310_, sizeof(void*)*2, v___y_2306_);
v___x_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
return v___x_2311_;
}
v___jp_2312_:
{
if (lean_obj_tag(v___y_2318_) == 0)
{
lean_object* v_a_2319_; 
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec(v___y_2314_);
v_a_2319_ = lean_ctor_get(v___y_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref(v___y_2318_);
v___y_2306_ = v___y_2313_;
v___y_2307_ = v___y_2315_;
v_proof_2308_ = v_a_2319_;
goto v___jp_2305_;
}
else
{
lean_object* v_a_2320_; 
lean_dec_ref(v___y_2315_);
v_a_2320_ = lean_ctor_get(v___y_2318_, 0);
lean_inc(v_a_2320_);
lean_dec_ref(v___y_2318_);
v___y_2293_ = v___y_2314_;
v___y_2294_ = v___y_2316_;
v___y_2295_ = v___y_2317_;
v_a_2296_ = v_a_2320_;
goto v___jp_2292_;
}
}
v___jp_2321_:
{
if (v___y_2334_ == 0)
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
lean_dec_ref(v___y_2326_);
v___x_2335_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_2336_ = l_Lean_MessageData_ofExpr(v___y_2327_);
v___x_2337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2335_);
lean_ctor_set(v___x_2337_, 1, v___x_2336_);
v___x_2338_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_2339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2337_);
lean_ctor_set(v___x_2339_, 1, v___x_2338_);
v___x_2340_ = l_Lean_Exception_toMessageData(v___y_2331_);
v___x_2341_ = l_Lean_indentD(v___x_2340_);
v___x_2342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2339_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
v___x_2343_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_2344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2342_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
v___x_2345_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2344_, v___y_2333_, v___y_2322_, v___y_2332_, v___y_2330_);
v___y_2313_ = v___y_2329_;
v___y_2314_ = v___y_2323_;
v___y_2315_ = v___y_2324_;
v___y_2316_ = v___y_2325_;
v___y_2317_ = v___y_2328_;
v___y_2318_ = v___x_2345_;
goto v___jp_2312_;
}
else
{
lean_dec_ref(v___y_2331_);
lean_dec_ref(v___y_2327_);
v___y_2313_ = v___y_2329_;
v___y_2314_ = v___y_2323_;
v___y_2315_ = v___y_2324_;
v___y_2316_ = v___y_2325_;
v___y_2317_ = v___y_2328_;
v___y_2318_ = v___y_2326_;
goto v___jp_2312_;
}
}
v___jp_2346_:
{
lean_object* v___x_2358_; lean_object* v_a_2359_; lean_object* v___x_2360_; 
v___x_2358_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_2350_, v___y_2355_);
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2359_);
lean_dec_ref(v___x_2358_);
v___x_2360_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_2352_, v___y_2355_);
if (v___y_2351_ == 0)
{
lean_object* v_a_2361_; 
lean_dec_ref(v___y_2353_);
lean_dec(v___y_2349_);
lean_dec(v___y_2348_);
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2361_);
lean_dec_ref(v___x_2360_);
v___y_2306_ = v___y_2347_;
v___y_2307_ = v_a_2359_;
v_proof_2308_ = v_a_2361_;
goto v___jp_2305_;
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2363_; 
v_a_2362_ = lean_ctor_get(v___x_2360_, 0);
lean_inc_n(v_a_2362_, 2);
lean_dec_ref(v___x_2360_);
v___x_2363_ = l_Lean_Meta_mkEqOfHEq(v_a_2362_, v___y_2347_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_dec(v_a_2362_);
v___y_2313_ = v___y_2347_;
v___y_2314_ = v___y_2348_;
v___y_2315_ = v_a_2359_;
v___y_2316_ = v___y_2349_;
v___y_2317_ = v___y_2353_;
v___y_2318_ = v___x_2363_;
goto v___jp_2312_;
}
else
{
lean_object* v_a_2364_; uint8_t v___x_2365_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2364_);
v___x_2365_ = l_Lean_Exception_isInterrupt(v_a_2364_);
if (v___x_2365_ == 0)
{
uint8_t v___x_2366_; 
lean_inc(v_a_2364_);
v___x_2366_ = l_Lean_Exception_isRuntime(v_a_2364_);
v___y_2322_ = v___y_2355_;
v___y_2323_ = v___y_2348_;
v___y_2324_ = v_a_2359_;
v___y_2325_ = v___y_2349_;
v___y_2326_ = v___x_2363_;
v___y_2327_ = v_a_2362_;
v___y_2328_ = v___y_2353_;
v___y_2329_ = v___y_2347_;
v___y_2330_ = v___y_2357_;
v___y_2331_ = v_a_2364_;
v___y_2332_ = v___y_2356_;
v___y_2333_ = v___y_2354_;
v___y_2334_ = v___x_2366_;
goto v___jp_2321_;
}
else
{
v___y_2322_ = v___y_2355_;
v___y_2323_ = v___y_2348_;
v___y_2324_ = v_a_2359_;
v___y_2325_ = v___y_2349_;
v___y_2326_ = v___x_2363_;
v___y_2327_ = v_a_2362_;
v___y_2328_ = v___y_2353_;
v___y_2329_ = v___y_2347_;
v___y_2330_ = v___y_2357_;
v___y_2331_ = v_a_2364_;
v___y_2332_ = v___y_2356_;
v___y_2333_ = v___y_2354_;
v___y_2334_ = v___x_2365_;
goto v___jp_2321_;
}
}
}
}
v___jp_2367_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; uint8_t v___x_2383_; 
v___x_2381_ = lean_array_get_size(v_a_2380_);
v___x_2382_ = lean_unsigned_to_nat(0u);
v___x_2383_ = lean_nat_dec_eq(v___x_2381_, v___x_2382_);
if (v___x_2383_ == 0)
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v_a_2395_; 
lean_dec_ref(v___y_2375_);
lean_dec_ref(v___y_2373_);
v___x_2384_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
lean_inc(v___y_2370_);
v___x_2385_ = l_Lean_MessageData_ofConstName(v___y_2370_, v___y_2378_);
v___x_2386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2384_);
lean_ctor_set(v___x_2386_, 1, v___x_2385_);
v___x_2387_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_2388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2386_);
lean_ctor_set(v___x_2388_, 1, v___x_2387_);
v___x_2389_ = lean_array_to_list(v_a_2380_);
v___x_2390_ = lean_box(0);
v___x_2391_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_2389_, v___x_2390_);
v___x_2392_ = l_Lean_MessageData_ofList(v___x_2391_);
v___x_2393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2388_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
v___x_2394_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2393_, v___y_2377_, v___y_2374_, v___y_2372_, v___y_2369_);
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2395_);
lean_dec_ref(v___x_2394_);
v___y_2293_ = v___y_2370_;
v___y_2294_ = v___y_2371_;
v___y_2295_ = v___y_2379_;
v_a_2296_ = v_a_2395_;
goto v___jp_2292_;
}
else
{
lean_dec_ref(v_a_2380_);
v___y_2347_ = v___y_2368_;
v___y_2348_ = v___y_2370_;
v___y_2349_ = v___y_2371_;
v___y_2350_ = v___y_2373_;
v___y_2351_ = v___y_2376_;
v___y_2352_ = v___y_2375_;
v___y_2353_ = v___y_2379_;
v___y_2354_ = v___y_2377_;
v___y_2355_ = v___y_2374_;
v___y_2356_ = v___y_2372_;
v___y_2357_ = v___y_2369_;
goto v___jp_2346_;
}
}
v___jp_2396_:
{
if (lean_obj_tag(v___y_2409_) == 0)
{
lean_object* v_a_2410_; 
v_a_2410_ = lean_ctor_get(v___y_2409_, 0);
lean_inc(v_a_2410_);
lean_dec_ref(v___y_2409_);
v___y_2368_ = v___y_2398_;
v___y_2369_ = v___y_2397_;
v___y_2370_ = v___y_2399_;
v___y_2371_ = v___y_2401_;
v___y_2372_ = v___y_2400_;
v___y_2373_ = v___y_2402_;
v___y_2374_ = v___y_2403_;
v___y_2375_ = v___y_2407_;
v___y_2376_ = v___y_2406_;
v___y_2377_ = v___y_2405_;
v___y_2378_ = v___y_2404_;
v___y_2379_ = v___y_2408_;
v_a_2380_ = v_a_2410_;
goto v___jp_2367_;
}
else
{
lean_object* v_a_2411_; 
lean_dec_ref(v___y_2407_);
lean_dec_ref(v___y_2402_);
v_a_2411_ = lean_ctor_get(v___y_2409_, 0);
lean_inc(v_a_2411_);
lean_dec_ref(v___y_2409_);
v___y_2293_ = v___y_2399_;
v___y_2294_ = v___y_2401_;
v___y_2295_ = v___y_2408_;
v_a_2296_ = v_a_2411_;
goto v___jp_2292_;
}
}
v___jp_2412_:
{
lean_object* v___x_2427_; size_t v_sz_2428_; lean_object* v___x_2429_; 
v___x_2427_ = lean_box(0);
v_sz_2428_ = lean_array_size(v___y_2413_);
v___x_2429_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___y_2413_, v_sz_2428_, v___y_2417_, v___x_2427_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; uint8_t v___x_2433_; 
lean_dec_ref(v___x_2429_);
v___x_2430_ = lean_unsigned_to_nat(0u);
v___x_2431_ = lean_array_get_size(v___y_2413_);
v___x_2432_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_2433_ = lean_nat_dec_lt(v___x_2430_, v___x_2431_);
if (v___x_2433_ == 0)
{
lean_dec_ref(v___y_2413_);
v___y_2368_ = v___y_2414_;
v___y_2369_ = v___y_2426_;
v___y_2370_ = v___y_2415_;
v___y_2371_ = v___y_2416_;
v___y_2372_ = v___y_2425_;
v___y_2373_ = v___y_2418_;
v___y_2374_ = v___y_2424_;
v___y_2375_ = v___y_2421_;
v___y_2376_ = v___y_2420_;
v___y_2377_ = v___y_2423_;
v___y_2378_ = v___y_2419_;
v___y_2379_ = v___y_2422_;
v_a_2380_ = v___x_2432_;
goto v___jp_2367_;
}
else
{
uint8_t v___x_2434_; 
v___x_2434_ = lean_nat_dec_le(v___x_2431_, v___x_2431_);
if (v___x_2434_ == 0)
{
if (v___x_2433_ == 0)
{
lean_dec_ref(v___y_2413_);
v___y_2368_ = v___y_2414_;
v___y_2369_ = v___y_2426_;
v___y_2370_ = v___y_2415_;
v___y_2371_ = v___y_2416_;
v___y_2372_ = v___y_2425_;
v___y_2373_ = v___y_2418_;
v___y_2374_ = v___y_2424_;
v___y_2375_ = v___y_2421_;
v___y_2376_ = v___y_2420_;
v___y_2377_ = v___y_2423_;
v___y_2378_ = v___y_2419_;
v___y_2379_ = v___y_2422_;
v_a_2380_ = v___x_2432_;
goto v___jp_2367_;
}
else
{
size_t v___x_2435_; lean_object* v___x_2436_; 
v___x_2435_ = lean_usize_of_nat(v___x_2431_);
v___x_2436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___y_2413_, v___y_2417_, v___x_2435_, v___x_2432_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec_ref(v___y_2413_);
v___y_2397_ = v___y_2426_;
v___y_2398_ = v___y_2414_;
v___y_2399_ = v___y_2415_;
v___y_2400_ = v___y_2425_;
v___y_2401_ = v___y_2416_;
v___y_2402_ = v___y_2418_;
v___y_2403_ = v___y_2424_;
v___y_2404_ = v___y_2419_;
v___y_2405_ = v___y_2423_;
v___y_2406_ = v___y_2420_;
v___y_2407_ = v___y_2421_;
v___y_2408_ = v___y_2422_;
v___y_2409_ = v___x_2436_;
goto v___jp_2396_;
}
}
else
{
size_t v___x_2437_; lean_object* v___x_2438_; 
v___x_2437_ = lean_usize_of_nat(v___x_2431_);
v___x_2438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___y_2413_, v___y_2417_, v___x_2437_, v___x_2432_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec_ref(v___y_2413_);
v___y_2397_ = v___y_2426_;
v___y_2398_ = v___y_2414_;
v___y_2399_ = v___y_2415_;
v___y_2400_ = v___y_2425_;
v___y_2401_ = v___y_2416_;
v___y_2402_ = v___y_2418_;
v___y_2403_ = v___y_2424_;
v___y_2404_ = v___y_2419_;
v___y_2405_ = v___y_2423_;
v___y_2406_ = v___y_2420_;
v___y_2407_ = v___y_2421_;
v___y_2408_ = v___y_2422_;
v___y_2409_ = v___x_2438_;
goto v___jp_2396_;
}
}
}
else
{
lean_object* v_a_2439_; 
lean_dec_ref(v___y_2421_);
lean_dec_ref(v___y_2418_);
lean_dec_ref(v___y_2413_);
v_a_2439_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_a_2439_);
lean_dec_ref(v___x_2429_);
v___y_2293_ = v___y_2415_;
v___y_2294_ = v___y_2416_;
v___y_2295_ = v___y_2422_;
v_a_2296_ = v_a_2439_;
goto v___jp_2292_;
}
}
v___jp_2440_:
{
lean_object* v___x_2456_; 
lean_inc_ref(v_fst_2450_);
lean_inc_ref(v_e_2221_);
v___x_2456_ = l_Lean_Meta_isExprDefEq(v_e_2221_, v_fst_2450_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; uint8_t v___x_2458_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_a_2457_);
lean_dec_ref(v___x_2456_);
v___x_2458_ = lean_unbox(v_a_2457_);
lean_dec(v_a_2457_);
if (v___x_2458_ == 0)
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v_a_2473_; 
lean_dec_ref(v_snd_2451_);
lean_dec_ref(v___y_2447_);
lean_dec_ref(v___y_2441_);
v___x_2459_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_2460_ = l_Lean_MessageData_ofExpr(v_fst_2450_);
v___x_2461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2459_);
lean_ctor_set(v___x_2461_, 1, v___x_2460_);
v___x_2462_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_2463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2461_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
lean_inc(v___y_2443_);
v___x_2464_ = l_Lean_MessageData_ofConstName(v___y_2443_, v___y_2446_);
v___x_2465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2463_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
v___x_2466_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_2467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2465_);
lean_ctor_set(v___x_2467_, 1, v___x_2466_);
v___x_2468_ = l_Lean_MessageData_ofExpr(v_e_2221_);
v___x_2469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2467_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
v___x_2470_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_2471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2469_);
lean_ctor_set(v___x_2471_, 1, v___x_2470_);
v___x_2472_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2471_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_a_2473_);
lean_dec_ref(v___x_2472_);
v___y_2293_ = v___y_2443_;
v___y_2294_ = v___y_2444_;
v___y_2295_ = v___y_2448_;
v_a_2296_ = v_a_2473_;
goto v___jp_2292_;
}
else
{
lean_dec_ref(v_fst_2450_);
lean_dec_ref(v_e_2221_);
v___y_2413_ = v___y_2441_;
v___y_2414_ = v___y_2442_;
v___y_2415_ = v___y_2443_;
v___y_2416_ = v___y_2444_;
v___y_2417_ = v___y_2445_;
v___y_2418_ = v_snd_2451_;
v___y_2419_ = v___y_2446_;
v___y_2420_ = v_fst_2449_;
v___y_2421_ = v___y_2447_;
v___y_2422_ = v___y_2448_;
v___y_2423_ = v___y_2452_;
v___y_2424_ = v___y_2453_;
v___y_2425_ = v___y_2454_;
v___y_2426_ = v___y_2455_;
goto v___jp_2412_;
}
}
else
{
lean_object* v_a_2474_; 
lean_dec_ref(v_snd_2451_);
lean_dec_ref(v_fst_2450_);
lean_dec_ref(v___y_2447_);
lean_dec_ref(v___y_2441_);
lean_dec_ref(v_e_2221_);
v_a_2474_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_a_2474_);
lean_dec_ref(v___x_2456_);
v___y_2293_ = v___y_2443_;
v___y_2294_ = v___y_2444_;
v___y_2295_ = v___y_2448_;
v_a_2296_ = v_a_2474_;
goto v___jp_2292_;
}
}
v___jp_2475_:
{
lean_object* v___x_2487_; double v___x_2488_; double v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2487_ = lean_io_get_num_heartbeats();
v___x_2488_ = lean_float_of_nat(v___y_2478_);
v___x_2489_ = lean_float_of_nat(v___x_2487_);
v___x_2490_ = lean_box_float(v___x_2488_);
v___x_2491_ = lean_box_float(v___x_2489_);
v___x_2492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2490_);
lean_ctor_set(v___x_2492_, 1, v___x_2491_);
v___x_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2493_, 0, v_a_2486_);
lean_ctor_set(v___x_2493_, 1, v___x_2492_);
lean_inc_ref(v___y_2483_);
lean_inc(v___y_2479_);
v___x_2494_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v___y_2479_, v___y_2476_, v___y_2483_, v___y_2485_, v___y_2482_, v___y_2480_, v___y_2481_, v___x_2493_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
v___y_2300_ = v___y_2477_;
v___y_2301_ = v___y_2479_;
v___y_2302_ = v___y_2484_;
v___y_2303_ = v___x_2494_;
goto v___jp_2299_;
}
v___jp_2495_:
{
lean_object* v___x_2507_; 
v___x_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2507_, 0, v_a_2506_);
v___y_2476_ = v___y_2496_;
v___y_2477_ = v___y_2497_;
v___y_2478_ = v___y_2498_;
v___y_2479_ = v___y_2499_;
v___y_2480_ = v___y_2500_;
v___y_2481_ = v___y_2501_;
v___y_2482_ = v___y_2503_;
v___y_2483_ = v___y_2502_;
v___y_2484_ = v___y_2504_;
v___y_2485_ = v___y_2505_;
v_a_2486_ = v___x_2507_;
goto v___jp_2475_;
}
v___jp_2508_:
{
if (lean_obj_tag(v___y_2519_) == 0)
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
v_a_2520_ = lean_ctor_get(v___y_2519_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___y_2519_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___y_2519_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___y_2519_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
lean_ctor_set_tag(v___x_2522_, 1);
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
v___y_2476_ = v___y_2509_;
v___y_2477_ = v___y_2510_;
v___y_2478_ = v___y_2511_;
v___y_2479_ = v___y_2512_;
v___y_2480_ = v___y_2513_;
v___y_2481_ = v___y_2514_;
v___y_2482_ = v___y_2516_;
v___y_2483_ = v___y_2515_;
v___y_2484_ = v___y_2517_;
v___y_2485_ = v___y_2518_;
v_a_2486_ = v___x_2525_;
goto v___jp_2475_;
}
}
}
else
{
lean_object* v_a_2528_; 
v_a_2528_ = lean_ctor_get(v___y_2519_, 0);
lean_inc(v_a_2528_);
lean_dec_ref(v___y_2519_);
v___y_2496_ = v___y_2509_;
v___y_2497_ = v___y_2510_;
v___y_2498_ = v___y_2511_;
v___y_2499_ = v___y_2512_;
v___y_2500_ = v___y_2513_;
v___y_2501_ = v___y_2514_;
v___y_2502_ = v___y_2515_;
v___y_2503_ = v___y_2516_;
v___y_2504_ = v___y_2517_;
v___y_2505_ = v___y_2518_;
v_a_2506_ = v_a_2528_;
goto v___jp_2495_;
}
}
v___jp_2529_:
{
lean_object* v___x_2541_; double v___x_2542_; double v___x_2543_; double v___x_2544_; double v___x_2545_; double v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2541_ = lean_io_mono_nanos_now();
v___x_2542_ = lean_float_of_nat(v___y_2539_);
v___x_2543_ = lean_float_once(&l_Lean_Meta_rwMatcher___closed__6, &l_Lean_Meta_rwMatcher___closed__6_once, _init_l_Lean_Meta_rwMatcher___closed__6);
v___x_2544_ = lean_float_div(v___x_2542_, v___x_2543_);
v___x_2545_ = lean_float_of_nat(v___x_2541_);
v___x_2546_ = lean_float_div(v___x_2545_, v___x_2543_);
v___x_2547_ = lean_box_float(v___x_2544_);
v___x_2548_ = lean_box_float(v___x_2546_);
v___x_2549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2547_);
lean_ctor_set(v___x_2549_, 1, v___x_2548_);
v___x_2550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2550_, 0, v_a_2540_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
lean_inc_ref(v___y_2536_);
lean_inc(v___y_2532_);
v___x_2551_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v___y_2532_, v___y_2530_, v___y_2536_, v___y_2538_, v___y_2535_, v___y_2533_, v___y_2534_, v___x_2550_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
v___y_2300_ = v___y_2531_;
v___y_2301_ = v___y_2532_;
v___y_2302_ = v___y_2537_;
v___y_2303_ = v___x_2551_;
goto v___jp_2299_;
}
v___jp_2552_:
{
lean_object* v___x_2564_; 
v___x_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2564_, 0, v_a_2563_);
v___y_2530_ = v___y_2553_;
v___y_2531_ = v___y_2554_;
v___y_2532_ = v___y_2555_;
v___y_2533_ = v___y_2556_;
v___y_2534_ = v___y_2557_;
v___y_2535_ = v___y_2559_;
v___y_2536_ = v___y_2558_;
v___y_2537_ = v___y_2560_;
v___y_2538_ = v___y_2562_;
v___y_2539_ = v___y_2561_;
v_a_2540_ = v___x_2564_;
goto v___jp_2529_;
}
v___jp_2565_:
{
if (lean_obj_tag(v___y_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
v_a_2577_ = lean_ctor_get(v___y_2576_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___y_2576_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___y_2576_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___y_2576_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
lean_ctor_set_tag(v___x_2579_, 1);
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
v___y_2530_ = v___y_2566_;
v___y_2531_ = v___y_2567_;
v___y_2532_ = v___y_2568_;
v___y_2533_ = v___y_2569_;
v___y_2534_ = v___y_2570_;
v___y_2535_ = v___y_2572_;
v___y_2536_ = v___y_2571_;
v___y_2537_ = v___y_2573_;
v___y_2538_ = v___y_2575_;
v___y_2539_ = v___y_2574_;
v_a_2540_ = v___x_2582_;
goto v___jp_2529_;
}
}
}
else
{
lean_object* v_a_2585_; 
v_a_2585_ = lean_ctor_get(v___y_2576_, 0);
lean_inc(v_a_2585_);
lean_dec_ref(v___y_2576_);
v___y_2553_ = v___y_2566_;
v___y_2554_ = v___y_2567_;
v___y_2555_ = v___y_2568_;
v___y_2556_ = v___y_2569_;
v___y_2557_ = v___y_2570_;
v___y_2558_ = v___y_2571_;
v___y_2559_ = v___y_2572_;
v___y_2560_ = v___y_2573_;
v___y_2561_ = v___y_2574_;
v___y_2562_ = v___y_2575_;
v_a_2563_ = v_a_2585_;
goto v___jp_2552_;
}
}
v___jp_2586_:
{
lean_object* v___x_2601_; lean_object* v_a_2602_; lean_object* v___x_2603_; uint8_t v___x_2604_; 
v___x_2601_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg(v_a_2225_);
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_a_2602_);
lean_dec_ref(v___x_2601_);
v___x_2603_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2604_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v___y_2600_, v___x_2603_);
if (v___x_2604_ == 0)
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2605_ = lean_io_mono_nanos_now();
lean_inc(v_a_2225_);
lean_inc_ref(v_a_2224_);
lean_inc(v_a_2223_);
lean_inc_ref(v_a_2222_);
v___x_2606_ = lean_infer_type(v___y_2599_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; uint8_t v___x_2608_; lean_object* v___x_2609_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2607_);
lean_dec_ref(v___x_2606_);
v___x_2608_ = 0;
v___x_2609_ = l_Lean_Meta_forallMetaTelescope(v_a_2607_, v___x_2608_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; lean_object* v_snd_2611_; lean_object* v_fst_2612_; lean_object* v_snd_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2631_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_a_2610_);
lean_dec_ref(v___x_2609_);
v_snd_2611_ = lean_ctor_get(v_a_2610_, 1);
lean_inc(v_snd_2611_);
v_fst_2612_ = lean_ctor_get(v_a_2610_, 0);
lean_inc(v_fst_2612_);
lean_dec(v_a_2610_);
v_snd_2613_ = lean_ctor_get(v_snd_2611_, 1);
v_isSharedCheck_2631_ = !lean_is_exclusive(v_snd_2611_);
if (v_isSharedCheck_2631_ == 0)
{
lean_object* v_unused_2632_; 
v_unused_2632_ = lean_ctor_get(v_snd_2611_, 0);
lean_dec(v_unused_2632_);
v___x_2615_ = v_snd_2611_;
v_isShared_2616_ = v_isSharedCheck_2631_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_snd_2613_);
lean_dec(v_snd_2611_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2631_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; uint8_t v___x_2619_; 
v___x_2617_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2594_);
v___x_2618_ = l_Lean_Name_append(v___x_2617_, v___y_2594_);
v___x_2619_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2595_, v___y_2600_, v___x_2618_);
lean_dec(v___x_2618_);
if (v___x_2619_ == 0)
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
lean_del_object(v___x_2615_);
v___x_2620_ = lean_box(0);
v___x_2621_ = l_Lean_Meta_rwMatcher___lam__2(v___y_2587_, v___y_2591_, v_fst_2612_, v___y_2588_, v___x_2604_, v_e_2221_, v_snd_2613_, v___x_2620_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
lean_dec(v_snd_2613_);
v___y_2566_ = v___y_2592_;
v___y_2567_ = v___y_2593_;
v___y_2568_ = v___y_2594_;
v___y_2569_ = v_a_2602_;
v___y_2570_ = v___y_2590_;
v___y_2571_ = v___y_2596_;
v___y_2572_ = v___y_2597_;
v___y_2573_ = v___y_2598_;
v___y_2574_ = v___x_2605_;
v___y_2575_ = v___y_2600_;
v___y_2576_ = v___x_2621_;
goto v___jp_2565_;
}
else
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2625_; 
v___x_2622_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2613_);
v___x_2623_ = l_Lean_indentExpr(v_snd_2613_);
if (v_isShared_2616_ == 0)
{
lean_ctor_set_tag(v___x_2615_, 7);
lean_ctor_set(v___x_2615_, 1, v___x_2623_);
lean_ctor_set(v___x_2615_, 0, v___x_2622_);
v___x_2625_ = v___x_2615_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2622_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v___x_2623_);
v___x_2625_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
lean_object* v___x_2626_; 
lean_inc(v___y_2594_);
v___x_2626_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2594_, v___x_2625_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; lean_object* v___x_2628_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2627_);
lean_dec_ref(v___x_2626_);
v___x_2628_ = l_Lean_Meta_rwMatcher___lam__2(v___y_2587_, v___y_2591_, v_fst_2612_, v___y_2588_, v___x_2604_, v_e_2221_, v_snd_2613_, v_a_2627_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
lean_dec(v_snd_2613_);
v___y_2566_ = v___y_2592_;
v___y_2567_ = v___y_2593_;
v___y_2568_ = v___y_2594_;
v___y_2569_ = v_a_2602_;
v___y_2570_ = v___y_2590_;
v___y_2571_ = v___y_2596_;
v___y_2572_ = v___y_2597_;
v___y_2573_ = v___y_2598_;
v___y_2574_ = v___x_2605_;
v___y_2575_ = v___y_2600_;
v___y_2576_ = v___x_2628_;
goto v___jp_2565_;
}
else
{
lean_object* v_a_2629_; 
lean_dec(v_snd_2613_);
lean_dec(v_fst_2612_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2588_);
lean_dec_ref(v_e_2221_);
v_a_2629_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2629_);
lean_dec_ref(v___x_2626_);
v___y_2553_ = v___y_2592_;
v___y_2554_ = v___y_2593_;
v___y_2555_ = v___y_2594_;
v___y_2556_ = v_a_2602_;
v___y_2557_ = v___y_2590_;
v___y_2558_ = v___y_2596_;
v___y_2559_ = v___y_2597_;
v___y_2560_ = v___y_2598_;
v___y_2561_ = v___x_2605_;
v___y_2562_ = v___y_2600_;
v_a_2563_ = v_a_2629_;
goto v___jp_2552_;
}
}
}
}
}
else
{
lean_object* v_a_2633_; 
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2588_);
lean_dec_ref(v_e_2221_);
v_a_2633_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_a_2633_);
lean_dec_ref(v___x_2609_);
v___y_2553_ = v___y_2592_;
v___y_2554_ = v___y_2593_;
v___y_2555_ = v___y_2594_;
v___y_2556_ = v_a_2602_;
v___y_2557_ = v___y_2590_;
v___y_2558_ = v___y_2596_;
v___y_2559_ = v___y_2597_;
v___y_2560_ = v___y_2598_;
v___y_2561_ = v___x_2605_;
v___y_2562_ = v___y_2600_;
v_a_2563_ = v_a_2633_;
goto v___jp_2552_;
}
}
else
{
lean_object* v_a_2634_; 
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2588_);
lean_dec_ref(v_e_2221_);
v_a_2634_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2634_);
lean_dec_ref(v___x_2606_);
v___y_2553_ = v___y_2592_;
v___y_2554_ = v___y_2593_;
v___y_2555_ = v___y_2594_;
v___y_2556_ = v_a_2602_;
v___y_2557_ = v___y_2590_;
v___y_2558_ = v___y_2596_;
v___y_2559_ = v___y_2597_;
v___y_2560_ = v___y_2598_;
v___y_2561_ = v___x_2605_;
v___y_2562_ = v___y_2600_;
v_a_2563_ = v_a_2634_;
goto v___jp_2552_;
}
}
else
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2635_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2225_);
lean_inc_ref(v_a_2224_);
lean_inc(v_a_2223_);
lean_inc_ref(v_a_2222_);
v___x_2636_ = lean_infer_type(v___y_2599_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; uint8_t v___x_2638_; lean_object* v___x_2639_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_a_2637_);
lean_dec_ref(v___x_2636_);
v___x_2638_ = 0;
v___x_2639_ = l_Lean_Meta_forallMetaTelescope(v_a_2637_, v___x_2638_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; lean_object* v_snd_2641_; lean_object* v_fst_2642_; lean_object* v_snd_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2661_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
lean_inc(v_a_2640_);
lean_dec_ref(v___x_2639_);
v_snd_2641_ = lean_ctor_get(v_a_2640_, 1);
lean_inc(v_snd_2641_);
v_fst_2642_ = lean_ctor_get(v_a_2640_, 0);
lean_inc(v_fst_2642_);
lean_dec(v_a_2640_);
v_snd_2643_ = lean_ctor_get(v_snd_2641_, 1);
v_isSharedCheck_2661_ = !lean_is_exclusive(v_snd_2641_);
if (v_isSharedCheck_2661_ == 0)
{
lean_object* v_unused_2662_; 
v_unused_2662_ = lean_ctor_get(v_snd_2641_, 0);
lean_dec(v_unused_2662_);
v___x_2645_ = v_snd_2641_;
v_isShared_2646_ = v_isSharedCheck_2661_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_snd_2643_);
lean_dec(v_snd_2641_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2661_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; uint8_t v___x_2649_; 
v___x_2647_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2594_);
v___x_2648_ = l_Lean_Name_append(v___x_2647_, v___y_2594_);
v___x_2649_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2595_, v___y_2600_, v___x_2648_);
lean_dec(v___x_2648_);
if (v___x_2649_ == 0)
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
lean_del_object(v___x_2645_);
v___x_2650_ = lean_box(0);
v___x_2651_ = l_Lean_Meta_rwMatcher___lam__3(v___y_2587_, v___y_2591_, v_fst_2642_, v___y_2588_, v___x_2604_, v_e_2221_, v___y_2589_, v_snd_2643_, v___x_2650_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
lean_dec(v_snd_2643_);
v___y_2509_ = v___y_2592_;
v___y_2510_ = v___y_2593_;
v___y_2511_ = v___x_2635_;
v___y_2512_ = v___y_2594_;
v___y_2513_ = v_a_2602_;
v___y_2514_ = v___y_2590_;
v___y_2515_ = v___y_2596_;
v___y_2516_ = v___y_2597_;
v___y_2517_ = v___y_2598_;
v___y_2518_ = v___y_2600_;
v___y_2519_ = v___x_2651_;
goto v___jp_2508_;
}
else
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2655_; 
v___x_2652_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2643_);
v___x_2653_ = l_Lean_indentExpr(v_snd_2643_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set_tag(v___x_2645_, 7);
lean_ctor_set(v___x_2645_, 1, v___x_2653_);
lean_ctor_set(v___x_2645_, 0, v___x_2652_);
v___x_2655_ = v___x_2645_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2652_);
lean_ctor_set(v_reuseFailAlloc_2660_, 1, v___x_2653_);
v___x_2655_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
lean_object* v___x_2656_; 
lean_inc(v___y_2594_);
v___x_2656_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2594_, v___x_2655_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2658_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref(v___x_2656_);
v___x_2658_ = l_Lean_Meta_rwMatcher___lam__3(v___y_2587_, v___y_2591_, v_fst_2642_, v___y_2588_, v___x_2604_, v_e_2221_, v___y_2589_, v_snd_2643_, v_a_2657_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
lean_dec(v_snd_2643_);
v___y_2509_ = v___y_2592_;
v___y_2510_ = v___y_2593_;
v___y_2511_ = v___x_2635_;
v___y_2512_ = v___y_2594_;
v___y_2513_ = v_a_2602_;
v___y_2514_ = v___y_2590_;
v___y_2515_ = v___y_2596_;
v___y_2516_ = v___y_2597_;
v___y_2517_ = v___y_2598_;
v___y_2518_ = v___y_2600_;
v___y_2519_ = v___x_2658_;
goto v___jp_2508_;
}
else
{
lean_object* v_a_2659_; 
lean_dec(v_snd_2643_);
lean_dec(v_fst_2642_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2588_);
lean_dec_ref(v_e_2221_);
v_a_2659_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2659_);
lean_dec_ref(v___x_2656_);
v___y_2496_ = v___y_2592_;
v___y_2497_ = v___y_2593_;
v___y_2498_ = v___x_2635_;
v___y_2499_ = v___y_2594_;
v___y_2500_ = v_a_2602_;
v___y_2501_ = v___y_2590_;
v___y_2502_ = v___y_2596_;
v___y_2503_ = v___y_2597_;
v___y_2504_ = v___y_2598_;
v___y_2505_ = v___y_2600_;
v_a_2506_ = v_a_2659_;
goto v___jp_2495_;
}
}
}
}
}
else
{
lean_object* v_a_2663_; 
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2588_);
lean_dec_ref(v_e_2221_);
v_a_2663_ = lean_ctor_get(v___x_2639_, 0);
lean_inc(v_a_2663_);
lean_dec_ref(v___x_2639_);
v___y_2496_ = v___y_2592_;
v___y_2497_ = v___y_2593_;
v___y_2498_ = v___x_2635_;
v___y_2499_ = v___y_2594_;
v___y_2500_ = v_a_2602_;
v___y_2501_ = v___y_2590_;
v___y_2502_ = v___y_2596_;
v___y_2503_ = v___y_2597_;
v___y_2504_ = v___y_2598_;
v___y_2505_ = v___y_2600_;
v_a_2506_ = v_a_2663_;
goto v___jp_2495_;
}
}
else
{
lean_object* v_a_2664_; 
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2588_);
lean_dec_ref(v_e_2221_);
v_a_2664_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_a_2664_);
lean_dec_ref(v___x_2636_);
v___y_2496_ = v___y_2592_;
v___y_2497_ = v___y_2593_;
v___y_2498_ = v___x_2635_;
v___y_2499_ = v___y_2594_;
v___y_2500_ = v_a_2602_;
v___y_2501_ = v___y_2590_;
v___y_2502_ = v___y_2596_;
v___y_2503_ = v___y_2597_;
v___y_2504_ = v___y_2598_;
v___y_2505_ = v___y_2600_;
v_a_2506_ = v_a_2664_;
goto v___jp_2495_;
}
}
}
v___jp_2665_:
{
uint8_t v___x_2667_; 
v___x_2667_ = 1;
if (v___y_2666_ == 0)
{
lean_object* v___x_2668_; lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2837_; 
v___x_2668_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(v_e_2221_, v_a_2225_);
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2671_ = v___x_2668_;
v_isShared_2672_ = v_isSharedCheck_2837_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2668_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2837_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
uint8_t v___x_2673_; 
v___x_2673_ = lean_unbox(v_a_2669_);
lean_dec(v_a_2669_);
if (v___x_2673_ == 0)
{
lean_object* v_options_2674_; uint8_t v_hasTrace_2675_; 
lean_del_object(v___x_2671_);
lean_dec(v_altIdx_2220_);
v_options_2674_ = lean_ctor_get(v_a_2224_, 2);
v_hasTrace_2675_ = lean_ctor_get_uint8(v_options_2674_, sizeof(void*)*1);
if (v_hasTrace_2675_ == 0)
{
v___y_2247_ = v___x_2667_;
goto v___jp_2246_;
}
else
{
lean_object* v_inheritedTraceOptions_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; uint8_t v___x_2679_; 
v_inheritedTraceOptions_2676_ = lean_ctor_get(v_a_2224_, 13);
v___x_2677_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2678_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2679_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2676_, v_options_2674_, v___x_2678_);
if (v___x_2679_ == 0)
{
v___y_2247_ = v___x_2667_;
goto v___jp_2246_;
}
else
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2680_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__15, &l_Lean_Meta_rwMatcher___closed__15_once, _init_l_Lean_Meta_rwMatcher___closed__15);
lean_inc_ref(v_e_2221_);
v___x_2681_ = l_Lean_indentExpr(v_e_2221_);
v___x_2682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2680_);
lean_ctor_set(v___x_2682_, 1, v___x_2681_);
v___x_2683_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2677_, v___x_2682_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_dec_ref(v___x_2683_);
v___y_2247_ = v___x_2667_;
goto v___jp_2246_;
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_dec_ref(v_e_2221_);
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2683_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2683_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
}
}
else
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2692_ = l_Lean_Expr_getAppFn(v_e_2221_);
v___x_2693_ = l_Lean_Expr_constName_x21(v___x_2692_);
lean_inc(v_a_2225_);
lean_inc_ref(v_a_2224_);
lean_inc(v_a_2223_);
lean_inc_ref(v_a_2222_);
lean_inc(v___x_2693_);
v___x_2694_ = lean_get_congr_match_equations_for(v___x_2693_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; lean_object* v___x_2696_; uint8_t v___x_2697_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_a_2695_);
lean_dec_ref(v___x_2694_);
v___x_2696_ = lean_array_get_size(v_a_2695_);
v___x_2697_ = lean_nat_dec_lt(v_altIdx_2220_, v___x_2696_);
if (v___x_2697_ == 0)
{
lean_object* v_options_2698_; uint8_t v_hasTrace_2699_; 
lean_dec(v_a_2695_);
lean_dec_ref(v___x_2692_);
v_options_2698_ = lean_ctor_get(v_a_2224_, 2);
v_hasTrace_2699_ = lean_ctor_get_uint8(v_options_2698_, sizeof(void*)*1);
if (v_hasTrace_2699_ == 0)
{
lean_dec(v___x_2693_);
lean_del_object(v___x_2671_);
lean_dec(v_altIdx_2220_);
v___y_2252_ = v___x_2667_;
goto v___jp_2251_;
}
else
{
lean_object* v_inheritedTraceOptions_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; uint8_t v___x_2703_; 
v_inheritedTraceOptions_2700_ = lean_ctor_get(v_a_2224_, 13);
v___x_2701_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2702_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2703_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2700_, v_options_2698_, v___x_2702_);
if (v___x_2703_ == 0)
{
lean_dec(v___x_2693_);
lean_del_object(v___x_2671_);
lean_dec(v_altIdx_2220_);
v___y_2252_ = v___x_2667_;
goto v___jp_2251_;
}
else
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2707_; 
v___x_2704_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__17, &l_Lean_Meta_rwMatcher___closed__17_once, _init_l_Lean_Meta_rwMatcher___closed__17);
v___x_2705_ = l_Nat_reprFast(v_altIdx_2220_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set_tag(v___x_2671_, 3);
lean_ctor_set(v___x_2671_, 0, v___x_2705_);
v___x_2707_ = v___x_2671_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2705_);
v___x_2707_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2708_ = l_Lean_MessageData_ofFormat(v___x_2707_);
v___x_2709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2704_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___x_2710_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__19, &l_Lean_Meta_rwMatcher___closed__19_once, _init_l_Lean_Meta_rwMatcher___closed__19);
v___x_2711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2709_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
v___x_2712_ = l_Nat_reprFast(v___x_2696_);
v___x_2713_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2712_);
v___x_2714_ = l_Lean_MessageData_ofFormat(v___x_2713_);
v___x_2715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2711_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v___x_2716_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__21, &l_Lean_Meta_rwMatcher___closed__21_once, _init_l_Lean_Meta_rwMatcher___closed__21);
v___x_2717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2715_);
lean_ctor_set(v___x_2717_, 1, v___x_2716_);
v___x_2718_ = l_Lean_MessageData_ofConstName(v___x_2693_, v___y_2666_);
v___x_2719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2717_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
v___x_2720_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2701_, v___x_2719_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_dec_ref(v___x_2720_);
v___y_2252_ = v___x_2667_;
goto v___jp_2251_;
}
else
{
lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2728_; 
lean_dec_ref(v_e_2221_);
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2723_ = v___x_2720_;
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___x_2720_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2726_; 
if (v_isShared_2724_ == 0)
{
v___x_2726_ = v___x_2723_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2721_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
}
}
}
else
{
lean_object* v_options_2730_; lean_object* v_inheritedTraceOptions_2731_; uint8_t v_hasTrace_2732_; lean_object* v_nargs_2733_; lean_object* v___x_2734_; lean_object* v___f_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v_dummy_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
lean_dec(v___x_2693_);
lean_del_object(v___x_2671_);
v_options_2730_ = lean_ctor_get(v_a_2224_, 2);
v_inheritedTraceOptions_2731_ = lean_ctor_get(v_a_2224_, 13);
v_hasTrace_2732_ = lean_ctor_get_uint8(v_options_2730_, sizeof(void*)*1);
v_nargs_2733_ = l_Lean_Expr_getAppNumArgs(v_e_2221_);
v___x_2734_ = lean_box(v___x_2667_);
lean_inc_ref_n(v_e_2221_, 2);
v___f_2735_ = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2735_, 0, v_e_2221_);
lean_closure_set(v___f_2735_, 1, v___x_2734_);
v___x_2736_ = lean_box(0);
v___x_2737_ = lean_array_get(v___x_2736_, v_a_2695_, v_altIdx_2220_);
lean_dec(v_altIdx_2220_);
lean_dec(v_a_2695_);
v___x_2738_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2739_ = l_Lean_Expr_constLevels_x21(v___x_2692_);
lean_dec_ref(v___x_2692_);
lean_inc(v___x_2737_);
v___x_2740_ = l_Lean_mkConst(v___x_2737_, v___x_2739_);
v_dummy_2741_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__22, &l_Lean_Meta_rwMatcher___closed__22_once, _init_l_Lean_Meta_rwMatcher___closed__22);
lean_inc(v_nargs_2733_);
v___x_2742_ = lean_mk_array(v_nargs_2733_, v_dummy_2741_);
v___x_2743_ = lean_unsigned_to_nat(1u);
v___x_2744_ = lean_nat_sub(v_nargs_2733_, v___x_2743_);
lean_dec(v_nargs_2733_);
v___x_2745_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2221_, v___x_2742_, v___x_2744_);
v___x_2746_ = l_Lean_mkAppN(v___x_2740_, v___x_2745_);
lean_dec_ref(v___x_2745_);
if (v_hasTrace_2732_ == 0)
{
lean_object* v___x_2747_; 
lean_inc(v_a_2225_);
lean_inc_ref(v_a_2224_);
lean_inc(v_a_2223_);
lean_inc_ref(v_a_2222_);
lean_inc_ref(v___x_2746_);
v___x_2747_ = lean_infer_type(v___x_2746_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2748_; uint8_t v___x_2749_; lean_object* v___x_2750_; 
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
lean_inc(v_a_2748_);
lean_dec_ref(v___x_2747_);
v___x_2749_ = 0;
v___x_2750_ = l_Lean_Meta_forallMetaTelescope(v_a_2748_, v___x_2749_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v_snd_2752_; lean_object* v_fst_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2791_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_a_2751_);
lean_dec_ref(v___x_2750_);
v_snd_2752_ = lean_ctor_get(v_a_2751_, 1);
v_fst_2753_ = lean_ctor_get(v_a_2751_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v_a_2751_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2755_ = v_a_2751_;
v_isShared_2756_ = v_isSharedCheck_2791_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_snd_2752_);
lean_inc(v_fst_2753_);
lean_dec(v_a_2751_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2791_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v_snd_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2789_; 
v_snd_2757_ = lean_ctor_get(v_snd_2752_, 1);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_snd_2752_);
if (v_isSharedCheck_2789_ == 0)
{
lean_object* v_unused_2790_; 
v_unused_2790_ = lean_ctor_get(v_snd_2752_, 0);
lean_dec(v_unused_2790_);
v___x_2759_ = v_snd_2752_;
v_isShared_2760_ = v_isSharedCheck_2789_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_snd_2757_);
lean_dec(v_snd_2752_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2789_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2761_; size_t v_sz_2762_; size_t v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; uint8_t v___x_2767_; 
v___x_2761_ = l_Lean_mkAppN(v___x_2746_, v_fst_2753_);
v_sz_2762_ = lean_array_size(v_fst_2753_);
v___x_2763_ = ((size_t)0ULL);
v___x_2764_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_2762_, v___x_2763_, v_fst_2753_);
v___x_2765_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_2766_ = lean_unsigned_to_nat(4u);
v___x_2767_ = l_Lean_Expr_isAppOfArity(v_snd_2757_, v___x_2765_, v___x_2766_);
if (v___x_2767_ == 0)
{
lean_object* v___x_2768_; lean_object* v___x_2769_; uint8_t v___x_2770_; 
v___x_2768_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_2769_ = lean_unsigned_to_nat(3u);
v___x_2770_ = l_Lean_Expr_isAppOfArity(v_snd_2757_, v___x_2768_, v___x_2769_);
if (v___x_2770_ == 0)
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
lean_dec_ref(v___x_2764_);
lean_dec_ref(v___x_2761_);
lean_dec(v_snd_2757_);
lean_dec_ref(v_e_2221_);
v___x_2771_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
lean_inc(v___x_2737_);
v___x_2772_ = l_Lean_MessageData_ofConstName(v___x_2737_, v_hasTrace_2732_);
if (v_isShared_2760_ == 0)
{
lean_ctor_set_tag(v___x_2759_, 7);
lean_ctor_set(v___x_2759_, 1, v___x_2772_);
lean_ctor_set(v___x_2759_, 0, v___x_2771_);
v___x_2774_ = v___x_2759_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v___x_2771_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
lean_object* v___x_2775_; lean_object* v___x_2777_; 
v___x_2775_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
if (v_isShared_2756_ == 0)
{
lean_ctor_set_tag(v___x_2755_, 7);
lean_ctor_set(v___x_2755_, 1, v___x_2775_);
lean_ctor_set(v___x_2755_, 0, v___x_2774_);
v___x_2777_ = v___x_2755_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2774_);
lean_ctor_set(v_reuseFailAlloc_2780_, 1, v___x_2775_);
v___x_2777_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
lean_object* v___x_2778_; lean_object* v_a_2779_; 
v___x_2778_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2777_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2779_);
lean_dec_ref(v___x_2778_);
v___y_2293_ = v___x_2737_;
v___y_2294_ = v___x_2738_;
v___y_2295_ = v___f_2735_;
v_a_2296_ = v_a_2779_;
goto v___jp_2292_;
}
}
}
else
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
lean_del_object(v___x_2759_);
lean_del_object(v___x_2755_);
v___x_2782_ = l_Lean_Expr_appFn_x21(v_snd_2757_);
v___x_2783_ = l_Lean_Expr_appArg_x21(v___x_2782_);
lean_dec_ref(v___x_2782_);
v___x_2784_ = l_Lean_Expr_appArg_x21(v_snd_2757_);
lean_dec(v_snd_2757_);
v___y_2441_ = v___x_2764_;
v___y_2442_ = v___x_2667_;
v___y_2443_ = v___x_2737_;
v___y_2444_ = v___x_2738_;
v___y_2445_ = v___x_2763_;
v___y_2446_ = v_hasTrace_2732_;
v___y_2447_ = v___x_2761_;
v___y_2448_ = v___f_2735_;
v_fst_2449_ = v_hasTrace_2732_;
v_fst_2450_ = v___x_2783_;
v_snd_2451_ = v___x_2784_;
v___y_2452_ = v_a_2222_;
v___y_2453_ = v_a_2223_;
v___y_2454_ = v_a_2224_;
v___y_2455_ = v_a_2225_;
goto v___jp_2440_;
}
}
else
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
lean_del_object(v___x_2759_);
lean_del_object(v___x_2755_);
v___x_2785_ = l_Lean_Expr_appFn_x21(v_snd_2757_);
v___x_2786_ = l_Lean_Expr_appFn_x21(v___x_2785_);
lean_dec_ref(v___x_2785_);
v___x_2787_ = l_Lean_Expr_appArg_x21(v___x_2786_);
lean_dec_ref(v___x_2786_);
v___x_2788_ = l_Lean_Expr_appArg_x21(v_snd_2757_);
lean_dec(v_snd_2757_);
v___y_2441_ = v___x_2764_;
v___y_2442_ = v___x_2667_;
v___y_2443_ = v___x_2737_;
v___y_2444_ = v___x_2738_;
v___y_2445_ = v___x_2763_;
v___y_2446_ = v_hasTrace_2732_;
v___y_2447_ = v___x_2761_;
v___y_2448_ = v___f_2735_;
v_fst_2449_ = v___x_2667_;
v_fst_2450_ = v___x_2787_;
v_snd_2451_ = v___x_2788_;
v___y_2452_ = v_a_2222_;
v___y_2453_ = v_a_2223_;
v___y_2454_ = v_a_2224_;
v___y_2455_ = v_a_2225_;
goto v___jp_2440_;
}
}
}
}
else
{
lean_object* v_a_2792_; 
lean_dec_ref(v___x_2746_);
lean_dec_ref(v_e_2221_);
v_a_2792_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_a_2792_);
lean_dec_ref(v___x_2750_);
v___y_2293_ = v___x_2737_;
v___y_2294_ = v___x_2738_;
v___y_2295_ = v___f_2735_;
v_a_2296_ = v_a_2792_;
goto v___jp_2292_;
}
}
else
{
lean_object* v_a_2793_; 
lean_dec_ref(v___x_2746_);
lean_dec_ref(v_e_2221_);
v_a_2793_ = lean_ctor_get(v___x_2747_, 0);
lean_inc(v_a_2793_);
lean_dec_ref(v___x_2747_);
v___y_2293_ = v___x_2737_;
v___y_2294_ = v___x_2738_;
v___y_2295_ = v___f_2735_;
v_a_2296_ = v_a_2793_;
goto v___jp_2292_;
}
}
else
{
lean_object* v___x_2794_; lean_object* v___f_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; uint8_t v___x_2798_; 
v___x_2794_ = lean_box(v___y_2666_);
lean_inc_ref(v_e_2221_);
lean_inc(v___x_2737_);
v___f_2795_ = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__1___boxed), 9, 3);
lean_closure_set(v___f_2795_, 0, v___x_2737_);
lean_closure_set(v___f_2795_, 1, v___x_2794_);
lean_closure_set(v___f_2795_, 2, v_e_2221_);
v___x_2796_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1));
v___x_2797_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2798_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2731_, v_options_2730_, v___x_2797_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2799_; uint8_t v___x_2800_; 
v___x_2799_ = l_Lean_trace_profiler;
v___x_2800_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_options_2730_, v___x_2799_);
if (v___x_2800_ == 0)
{
lean_object* v___x_2801_; 
lean_dec_ref(v___f_2795_);
lean_inc(v_a_2225_);
lean_inc_ref(v_a_2224_);
lean_inc(v_a_2223_);
lean_inc_ref(v_a_2222_);
lean_inc_ref(v___x_2746_);
v___x_2801_ = lean_infer_type(v___x_2746_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; uint8_t v___x_2803_; lean_object* v___x_2804_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2802_);
lean_dec_ref(v___x_2801_);
v___x_2803_ = 0;
v___x_2804_ = l_Lean_Meta_forallMetaTelescope(v_a_2802_, v___x_2803_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v_a_2805_; lean_object* v_snd_2806_; 
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_a_2805_);
lean_dec_ref(v___x_2804_);
v_snd_2806_ = lean_ctor_get(v_a_2805_, 1);
lean_inc(v_snd_2806_);
if (v___x_2798_ == 0)
{
lean_object* v_fst_2807_; lean_object* v_snd_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v_fst_2807_ = lean_ctor_get(v_a_2805_, 0);
lean_inc(v_fst_2807_);
lean_dec(v_a_2805_);
v_snd_2808_ = lean_ctor_get(v_snd_2806_, 1);
lean_inc(v_snd_2808_);
lean_dec(v_snd_2806_);
v___x_2809_ = lean_box(0);
lean_inc(v___x_2737_);
v___x_2810_ = l_Lean_Meta_rwMatcher___lam__4(v___x_2667_, v___x_2746_, v_fst_2807_, v___x_2737_, v___x_2800_, v_e_2221_, v_snd_2808_, v___x_2809_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
lean_dec(v_snd_2808_);
v___y_2300_ = v___x_2737_;
v___y_2301_ = v___x_2738_;
v___y_2302_ = v___f_2735_;
v___y_2303_ = v___x_2810_;
goto v___jp_2299_;
}
else
{
lean_object* v_fst_2811_; lean_object* v_snd_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2825_; 
v_fst_2811_ = lean_ctor_get(v_a_2805_, 0);
lean_inc(v_fst_2811_);
lean_dec(v_a_2805_);
v_snd_2812_ = lean_ctor_get(v_snd_2806_, 1);
v_isSharedCheck_2825_ = !lean_is_exclusive(v_snd_2806_);
if (v_isSharedCheck_2825_ == 0)
{
lean_object* v_unused_2826_; 
v_unused_2826_ = lean_ctor_get(v_snd_2806_, 0);
lean_dec(v_unused_2826_);
v___x_2814_ = v_snd_2806_;
v_isShared_2815_ = v_isSharedCheck_2825_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_snd_2812_);
lean_dec(v_snd_2806_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2825_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2819_; 
v___x_2816_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2812_);
v___x_2817_ = l_Lean_indentExpr(v_snd_2812_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set_tag(v___x_2814_, 7);
lean_ctor_set(v___x_2814_, 1, v___x_2817_);
lean_ctor_set(v___x_2814_, 0, v___x_2816_);
v___x_2819_ = v___x_2814_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v___x_2816_);
lean_ctor_set(v_reuseFailAlloc_2824_, 1, v___x_2817_);
v___x_2819_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2738_, v___x_2819_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2822_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref(v___x_2820_);
lean_inc(v___x_2737_);
v___x_2822_ = l_Lean_Meta_rwMatcher___lam__4(v___x_2667_, v___x_2746_, v_fst_2811_, v___x_2737_, v___x_2800_, v_e_2221_, v_snd_2812_, v_a_2821_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
lean_dec(v_snd_2812_);
v___y_2300_ = v___x_2737_;
v___y_2301_ = v___x_2738_;
v___y_2302_ = v___f_2735_;
v___y_2303_ = v___x_2822_;
goto v___jp_2299_;
}
else
{
lean_object* v_a_2823_; 
lean_dec(v_snd_2812_);
lean_dec(v_fst_2811_);
lean_dec_ref(v___x_2746_);
lean_dec_ref(v_e_2221_);
v_a_2823_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2823_);
lean_dec_ref(v___x_2820_);
v___y_2293_ = v___x_2737_;
v___y_2294_ = v___x_2738_;
v___y_2295_ = v___f_2735_;
v_a_2296_ = v_a_2823_;
goto v___jp_2292_;
}
}
}
}
}
else
{
lean_object* v_a_2827_; 
lean_dec_ref(v___x_2746_);
lean_dec_ref(v_e_2221_);
v_a_2827_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_a_2827_);
lean_dec_ref(v___x_2804_);
v___y_2293_ = v___x_2737_;
v___y_2294_ = v___x_2738_;
v___y_2295_ = v___f_2735_;
v_a_2296_ = v_a_2827_;
goto v___jp_2292_;
}
}
else
{
lean_object* v_a_2828_; 
lean_dec_ref(v___x_2746_);
lean_dec_ref(v_e_2221_);
v_a_2828_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2828_);
lean_dec_ref(v___x_2801_);
v___y_2293_ = v___x_2737_;
v___y_2294_ = v___x_2738_;
v___y_2295_ = v___f_2735_;
v_a_2296_ = v_a_2828_;
goto v___jp_2292_;
}
}
else
{
lean_inc_ref(v___x_2746_);
lean_inc(v___x_2737_);
v___y_2587_ = v___x_2667_;
v___y_2588_ = v___x_2737_;
v___y_2589_ = v___y_2666_;
v___y_2590_ = v___f_2795_;
v___y_2591_ = v___x_2746_;
v___y_2592_ = v___x_2667_;
v___y_2593_ = v___x_2737_;
v___y_2594_ = v___x_2738_;
v___y_2595_ = v_inheritedTraceOptions_2731_;
v___y_2596_ = v___x_2796_;
v___y_2597_ = v___x_2798_;
v___y_2598_ = v___f_2735_;
v___y_2599_ = v___x_2746_;
v___y_2600_ = v_options_2730_;
goto v___jp_2586_;
}
}
else
{
lean_inc_ref(v___x_2746_);
lean_inc(v___x_2737_);
v___y_2587_ = v___x_2667_;
v___y_2588_ = v___x_2737_;
v___y_2589_ = v___y_2666_;
v___y_2590_ = v___f_2795_;
v___y_2591_ = v___x_2746_;
v___y_2592_ = v___x_2667_;
v___y_2593_ = v___x_2737_;
v___y_2594_ = v___x_2738_;
v___y_2595_ = v_inheritedTraceOptions_2731_;
v___y_2596_ = v___x_2796_;
v___y_2597_ = v___x_2798_;
v___y_2598_ = v___f_2735_;
v___y_2599_ = v___x_2746_;
v___y_2600_ = v_options_2730_;
goto v___jp_2586_;
}
}
}
}
else
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2836_; 
lean_dec(v___x_2693_);
lean_dec_ref(v___x_2692_);
lean_del_object(v___x_2671_);
lean_dec_ref(v_e_2221_);
lean_dec(v_altIdx_2220_);
v_a_2829_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2831_ = v___x_2694_;
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2694_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2834_; 
if (v_isShared_2832_ == 0)
{
v___x_2834_ = v___x_2831_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
}
}
else
{
lean_object* v___x_2838_; 
lean_dec(v_altIdx_2220_);
v___x_2838_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_rwMatcher_spec__14___redArg(v_e_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2848_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2841_ = v___x_2838_;
v_isShared_2842_ = v_isSharedCheck_2848_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2838_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2848_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2846_; 
v___x_2843_ = lean_box(0);
v___x_2844_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2844_, 0, v_a_2839_);
lean_ctor_set(v___x_2844_, 1, v___x_2843_);
lean_ctor_set_uint8(v___x_2844_, sizeof(void*)*2, v___x_2667_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v___x_2844_);
v___x_2846_ = v___x_2841_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2844_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
v_a_2849_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2838_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2838_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___boxed(lean_object* v_altIdx_2861_, lean_object* v_e_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = l_Lean_Meta_rwMatcher(v_altIdx_2861_, v_e_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_);
lean_dec(v_a_2866_);
lean_dec_ref(v_a_2865_);
lean_dec(v_a_2864_);
lean_dec_ref(v_a_2863_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(lean_object* v_mvarId_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_mvarId_2869_, v___y_2871_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___boxed(lean_object* v_mvarId_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(v_mvarId_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v_mvarId_2876_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5(lean_object* v_00_u03b1_2883_, lean_object* v_msg_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v___x_2890_; 
v___x_2890_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v_msg_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___boxed(lean_object* v_00_u03b1_2891_, lean_object* v_msg_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
lean_object* v_res_2898_; 
v_res_2898_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5(v_00_u03b1_2891_, v_msg_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
lean_dec(v___y_2896_);
lean_dec_ref(v___y_2895_);
lean_dec(v___y_2894_);
lean_dec_ref(v___y_2893_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(lean_object* v_00_u03b1_2899_, lean_object* v_x_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_){
_start:
{
lean_object* v___x_2906_; 
v___x_2906_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___redArg(v_x_2900_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___boxed(lean_object* v_00_u03b1_2907_, lean_object* v_x_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(v_00_u03b1_2907_, v_x_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_rwMatcher_spec__14(lean_object* v_inst_2915_, lean_object* v_a_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v___x_2922_; 
v___x_2922_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_rwMatcher_spec__14___redArg(v_a_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00Lean_Meta_rwMatcher_spec__14___boxed(lean_object* v_inst_2923_, lean_object* v_a_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_rwMatcher_spec__14(v_inst_2923_, v_a_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
return v_res_2930_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(lean_object* v_00_u03b2_2931_, lean_object* v_x_2932_, lean_object* v_x_2933_){
_start:
{
uint8_t v___x_2934_; 
v___x_2934_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_x_2932_, v_x_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2935_, lean_object* v_x_2936_, lean_object* v_x_2937_){
_start:
{
uint8_t v_res_2938_; lean_object* v_r_2939_; 
v_res_2938_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(v_00_u03b2_2935_, v_x_2936_, v_x_2937_);
lean_dec(v_x_2937_);
lean_dec_ref(v_x_2936_);
v_r_2939_ = lean_box(v_res_2938_);
return v_r_2939_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5(lean_object* v_00_u03b2_2940_, lean_object* v_x_2941_, size_t v_x_2942_, lean_object* v_x_2943_){
_start:
{
uint8_t v___x_2944_; 
v___x_2944_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_2941_, v_x_2942_, v_x_2943_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b2_2945_, lean_object* v_x_2946_, lean_object* v_x_2947_, lean_object* v_x_2948_){
_start:
{
size_t v_x_112424__boxed_2949_; uint8_t v_res_2950_; lean_object* v_r_2951_; 
v_x_112424__boxed_2949_ = lean_unbox_usize(v_x_2947_);
lean_dec(v_x_2947_);
v_res_2950_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5(v_00_u03b2_2945_, v_x_2946_, v_x_112424__boxed_2949_, v_x_2948_);
lean_dec(v_x_2948_);
lean_dec_ref(v_x_2946_);
v_r_2951_ = lean_box(v_res_2950_);
return v_r_2951_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20(lean_object* v_00_u03b2_2952_, lean_object* v_keys_2953_, lean_object* v_vals_2954_, lean_object* v_heq_2955_, lean_object* v_i_2956_, lean_object* v_k_2957_){
_start:
{
uint8_t v___x_2958_; 
v___x_2958_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20___redArg(v_keys_2953_, v_i_2956_, v_k_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20___boxed(lean_object* v_00_u03b2_2959_, lean_object* v_keys_2960_, lean_object* v_vals_2961_, lean_object* v_heq_2962_, lean_object* v_i_2963_, lean_object* v_k_2964_){
_start:
{
uint8_t v_res_2965_; lean_object* v_r_2966_; 
v_res_2965_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20(v_00_u03b2_2959_, v_keys_2960_, v_vals_2961_, v_heq_2962_, v_i_2963_, v_k_2964_);
lean_dec(v_k_2964_);
lean_dec_ref(v_vals_2961_);
lean_dec_ref(v_keys_2960_);
v_r_2966_ = lean_box(v_res_2965_);
return v_r_2966_;
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
