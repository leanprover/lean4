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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
uint8_t l_Lean_Meta_isMatcherAppCore(lean_object*, lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* lean_get_congr_match_equations_for(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis(lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_hrefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_heqOfEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_io_mono_nanos_now();
lean_object* lean_io_get_num_heartbeats();
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
static const lean_string_object l_Lean_Meta_rwIfWith___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ite_eq_right"};
static const lean_object* l_Lean_Meta_rwIfWith___closed__6 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__6_value;
static const lean_ctor_object l_Lean_Meta_rwIfWith___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwIfWith___closed__6_value),LEAN_SCALAR_PTR_LITERAL(61, 39, 8, 237, 213, 91, 107, 69)}};
static const lean_object* l_Lean_Meta_rwIfWith___closed__7 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__7_value;
static const lean_string_object l_Lean_Meta_rwIfWith___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ite_eq_left"};
static const lean_object* l_Lean_Meta_rwIfWith___closed__8 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__8_value;
static const lean_ctor_object l_Lean_Meta_rwIfWith___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwIfWith___closed__8_value),LEAN_SCALAR_PTR_LITERAL(224, 237, 116, 5, 155, 59, 56, 160)}};
static const lean_object* l_Lean_Meta_rwIfWith___closed__9 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__9_value;
static const lean_string_object l_Lean_Meta_rwIfWith___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "dite_eq_right"};
static const lean_object* l_Lean_Meta_rwIfWith___closed__10 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__10_value;
static const lean_ctor_object l_Lean_Meta_rwIfWith___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwIfWith___closed__10_value),LEAN_SCALAR_PTR_LITERAL(138, 158, 15, 234, 166, 144, 231, 97)}};
static const lean_object* l_Lean_Meta_rwIfWith___closed__11 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__11_value;
static const lean_string_object l_Lean_Meta_rwIfWith___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "dite_eq_left"};
static const lean_object* l_Lean_Meta_rwIfWith___closed__12 = (const lean_object*)&l_Lean_Meta_rwIfWith___closed__12_value;
static const lean_ctor_object l_Lean_Meta_rwIfWith___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwIfWith___closed__12_value),LEAN_SCALAR_PTR_LITERAL(239, 169, 41, 13, 119, 67, 249, 86)}};
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
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__17___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14_spec__16(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_rwMatcher___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "PSum"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__0 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__0_value;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "casesOn"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__1 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__1_value;
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwMatcher___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 224, 206, 173, 168, 27, 198, 53)}};
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_rwMatcher___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_rwMatcher___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 115, 173, 38, 27, 113, 160, 8)}};
static const lean_object* l_Lean_Meta_rwMatcher___closed__2 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__2_value;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "PSigma"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__3 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__3_value;
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwMatcher___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 171, 149, 177, 120, 131, 37, 223)}};
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_rwMatcher___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_rwMatcher___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 129, 3, 119, 45, 252, 168, 83)}};
static const lean_object* l_Lean_Meta_rwMatcher___closed__4 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__4_value;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__5 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__5_value;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Match"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__6 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__6_value;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__7 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__7_value;
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwMatcher___closed__5_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_rwMatcher___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_rwMatcher___closed__6_value),LEAN_SCALAR_PTR_LITERAL(250, 1, 225, 180, 135, 246, 184, 244)}};
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_rwMatcher___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_rwMatcher___closed__7_value),LEAN_SCALAR_PTR_LITERAL(253, 56, 25, 25, 156, 146, 62, 130)}};
static const lean_object* l_Lean_Meta_rwMatcher___closed__8 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__8_value;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__9 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__9_value;
static const lean_ctor_object l_Lean_Meta_rwMatcher___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_rwMatcher___closed__9_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_rwMatcher___closed__10 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__10_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__11;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Not a matcher application:"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__12 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__12_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__13;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "When trying to reduce arm "};
static const lean_object* l_Lean_Meta_rwMatcher___closed__14 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__14_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__15;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ", only "};
static const lean_object* l_Lean_Meta_rwMatcher___closed__16 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__16_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__17;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " equations for "};
static const lean_object* l_Lean_Meta_rwMatcher___closed__18 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__18_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__19;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Failed to apply "};
static const lean_object* l_Lean_Meta_rwMatcher___closed__20 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__20_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__21;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__22 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__22_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__23;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__24;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_rwMatcher___closed__25;
static const lean_string_object l_Lean_Meta_rwMatcher___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "eqProof has type"};
static const lean_object* l_Lean_Meta_rwMatcher___closed__26 = (const lean_object*)&l_Lean_Meta_rwMatcher___closed__26_value;
static lean_once_cell_t l_Lean_Meta_rwMatcher___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_rwMatcher___closed__27;
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec(v_a_58_);
v___x_60_ = l_Lean_Expr_isApp(v___x_59_);
if (v___x_60_ == 0)
{
lean_dec_ref(v___x_59_);
lean_dec_ref(v_hc_45_);
goto v___jp_52_;
}
else
{
lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_61_ = l_Lean_Expr_appFnCleanup___redArg(v___x_59_);
v___x_62_ = l_Lean_Expr_isApp(v___x_61_);
if (v___x_62_ == 0)
{
lean_dec_ref(v___x_61_);
lean_dec_ref(v___x_59_);
lean_dec_ref(v_hc_45_);
goto v___jp_52_;
}
else
{
lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_63_ = l_Lean_Expr_appFnCleanup___redArg(v___x_61_);
v___x_64_ = l_Lean_Expr_isApp(v___x_63_);
if (v___x_64_ == 0)
{
lean_dec_ref(v___x_63_);
lean_dec_ref(v___x_61_);
lean_dec_ref(v___x_59_);
lean_dec_ref(v_hc_45_);
goto v___jp_52_;
}
else
{
lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_65_ = l_Lean_Expr_appFnCleanup___redArg(v___x_63_);
v___x_66_ = l_Lean_Expr_isApp(v___x_65_);
if (v___x_66_ == 0)
{
lean_dec_ref(v___x_65_);
lean_dec_ref(v___x_63_);
lean_dec_ref(v___x_61_);
lean_dec_ref(v___x_59_);
lean_dec_ref(v_hc_45_);
goto v___jp_52_;
}
else
{
lean_object* v_arg_67_; lean_object* v_arg_68_; lean_object* v_arg_69_; lean_object* v_arg_70_; lean_object* v___x_71_; lean_object* v___x_72_; uint8_t v___x_73_; 
v_arg_67_ = lean_ctor_get(v___x_59_, 1);
lean_inc_ref(v_arg_67_);
lean_dec_ref(v___x_59_);
v_arg_68_ = lean_ctor_get(v___x_61_, 1);
lean_inc_ref(v_arg_68_);
lean_dec_ref(v___x_61_);
v_arg_69_ = lean_ctor_get(v___x_63_, 1);
lean_inc_ref(v_arg_69_);
lean_dec_ref(v___x_63_);
v_arg_70_ = lean_ctor_get(v___x_65_, 1);
lean_inc_ref(v_arg_70_);
v___x_71_ = l_Lean_Expr_appFnCleanup___redArg(v___x_65_);
lean_dec_ref(v___x_65_);
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
lean_dec_ref(v_arg_69_);
lean_dec_ref(v_arg_68_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_hc_45_);
goto v___jp_52_;
}
else
{
lean_object* v_arg_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
v_arg_75_ = lean_ctor_get(v___x_71_, 1);
lean_inc_ref(v_arg_75_);
v___x_76_ = l_Lean_Expr_appFnCleanup___redArg(v___x_71_);
lean_dec_ref(v___x_71_);
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
lean_dec_ref(v_arg_69_);
lean_dec_ref(v_arg_68_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_hc_45_);
goto v___jp_52_;
}
else
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = l_Lean_Expr_constLevels_x21(v___x_76_);
lean_dec_ref(v___x_76_);
lean_inc(v_a_50_);
lean_inc_ref(v_a_49_);
lean_inc(v_a_48_);
lean_inc_ref(v_a_47_);
lean_inc_ref(v_hc_45_);
v___x_82_ = lean_infer_type(v_hc_45_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v_a_83_; lean_object* v___x_84_; 
v_a_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc(v_a_83_);
lean_dec_ref_known(v___x_82_, 1);
lean_inc_ref(v_arg_70_);
v___x_84_ = l_Lean_Meta_isExprDefEq(v_arg_70_, v_a_83_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_84_) == 0)
{
lean_object* v_a_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_148_; 
v_a_85_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_148_ == 0)
{
v___x_87_ = v___x_84_;
v_isShared_88_ = v_isSharedCheck_148_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_a_85_);
lean_dec(v___x_84_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_148_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
uint8_t v___x_89_; 
v___x_89_ = lean_unbox(v_a_85_);
lean_dec(v_a_85_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; 
lean_del_object(v___x_87_);
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
lean_dec(v___x_81_);
lean_dec_ref(v_arg_75_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_69_);
lean_dec_ref(v_arg_68_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_hc_45_);
goto v___jp_52_;
}
else
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_113_; 
lean_dec_ref(v_e_46_);
v___x_99_ = ((lean_object*)(l_Lean_Meta_rwIfWith___closed__7));
v___x_100_ = l_Lean_mkConst(v___x_99_, v___x_81_);
v___x_101_ = lean_unsigned_to_nat(6u);
v___x_102_ = lean_mk_empty_array_with_capacity(v___x_101_);
v___x_103_ = lean_array_push(v___x_102_, v_arg_70_);
v___x_104_ = lean_array_push(v___x_103_, v_arg_69_);
v___x_105_ = lean_array_push(v___x_104_, v_hc_45_);
v___x_106_ = lean_array_push(v___x_105_, v_arg_75_);
v___x_107_ = lean_array_push(v___x_106_, v_arg_68_);
lean_inc_ref(v_arg_67_);
v___x_108_ = lean_array_push(v___x_107_, v_arg_67_);
v___x_109_ = l_Lean_mkAppN(v___x_100_, v___x_108_);
lean_dec_ref(v___x_108_);
v___x_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
v___x_111_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_111_, 0, v_arg_67_);
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
lean_dec(v___x_81_);
lean_dec_ref(v_arg_75_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_69_);
lean_dec_ref(v_arg_68_);
lean_dec_ref(v_arg_67_);
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
lean_dec(v___x_81_);
lean_dec_ref(v_arg_75_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_69_);
lean_dec_ref(v_arg_68_);
lean_dec_ref(v_arg_67_);
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
v___x_133_ = l_Lean_mkConst(v___x_132_, v___x_81_);
v___x_134_ = lean_unsigned_to_nat(6u);
v___x_135_ = lean_mk_empty_array_with_capacity(v___x_134_);
v___x_136_ = lean_array_push(v___x_135_, v_arg_70_);
v___x_137_ = lean_array_push(v___x_136_, v_arg_69_);
v___x_138_ = lean_array_push(v___x_137_, v_hc_45_);
v___x_139_ = lean_array_push(v___x_138_, v_arg_75_);
lean_inc_ref(v_arg_68_);
v___x_140_ = lean_array_push(v___x_139_, v_arg_68_);
v___x_141_ = lean_array_push(v___x_140_, v_arg_67_);
v___x_142_ = l_Lean_mkAppN(v___x_133_, v___x_141_);
lean_dec_ref(v___x_141_);
v___x_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
v___x_144_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_144_, 0, v_arg_68_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
lean_ctor_set_uint8(v___x_144_, sizeof(void*)*2, v___x_80_);
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 0, v___x_144_);
v___x_146_ = v___x_87_;
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
lean_dec(v___x_81_);
lean_dec_ref(v_arg_75_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_69_);
lean_dec_ref(v_arg_68_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_hc_45_);
v_a_149_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_84_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_84_);
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
lean_dec(v___x_81_);
lean_dec_ref(v_arg_75_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_69_);
lean_dec_ref(v_arg_68_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_hc_45_);
v_a_157_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_164_ == 0)
{
v___x_159_ = v___x_82_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_82_);
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
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = l_Lean_Expr_constLevels_x21(v___x_76_);
lean_dec_ref(v___x_76_);
lean_inc(v_a_50_);
lean_inc_ref(v_a_49_);
lean_inc(v_a_48_);
lean_inc_ref(v_a_47_);
lean_inc_ref(v_hc_45_);
v___x_166_ = lean_infer_type(v_hc_45_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v_a_167_; lean_object* v___x_168_; 
v_a_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc(v_a_167_);
lean_dec_ref_known(v___x_166_, 1);
lean_inc_ref(v_arg_70_);
v___x_168_ = l_Lean_Meta_isExprDefEq(v_arg_70_, v_a_167_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_240_; 
v_a_169_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_240_ == 0)
{
v___x_171_ = v___x_168_;
v_isShared_172_ = v_isSharedCheck_240_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_168_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_240_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
uint8_t v___x_173_; 
v___x_173_ = lean_unbox(v_a_169_);
lean_dec(v_a_169_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; 
lean_del_object(v___x_171_);
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
lean_dec(v___x_165_);
lean_dec_ref(v_arg_75_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_69_);
lean_dec_ref(v_arg_68_);
lean_dec_ref(v_arg_67_);
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
lean_inc_ref(v_arg_67_);
v___x_186_ = l_Lean_Expr_beta(v_arg_67_, v___x_185_);
v___x_187_ = ((lean_object*)(l_Lean_Meta_rwIfWith___closed__11));
v___x_188_ = l_Lean_mkConst(v___x_187_, v___x_165_);
v___x_189_ = lean_unsigned_to_nat(6u);
v___x_190_ = lean_mk_empty_array_with_capacity(v___x_189_);
v___x_191_ = lean_array_push(v___x_190_, v_arg_70_);
v___x_192_ = lean_array_push(v___x_191_, v_arg_69_);
v___x_193_ = lean_array_push(v___x_192_, v_hc_45_);
v___x_194_ = lean_array_push(v___x_193_, v_arg_75_);
v___x_195_ = lean_array_push(v___x_194_, v_arg_68_);
v___x_196_ = lean_array_push(v___x_195_, v_arg_67_);
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
lean_dec(v___x_165_);
lean_dec_ref(v_arg_75_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_69_);
lean_dec_ref(v_arg_68_);
lean_dec_ref(v_arg_67_);
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
lean_dec(v___x_165_);
lean_dec_ref(v_arg_75_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_69_);
lean_dec_ref(v_arg_68_);
lean_dec_ref(v_arg_67_);
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
lean_inc_ref(v_arg_68_);
v___x_223_ = l_Lean_Expr_beta(v_arg_68_, v___x_222_);
v___x_224_ = ((lean_object*)(l_Lean_Meta_rwIfWith___closed__13));
v___x_225_ = l_Lean_mkConst(v___x_224_, v___x_165_);
v___x_226_ = lean_unsigned_to_nat(6u);
v___x_227_ = lean_mk_empty_array_with_capacity(v___x_226_);
v___x_228_ = lean_array_push(v___x_227_, v_arg_70_);
v___x_229_ = lean_array_push(v___x_228_, v_arg_69_);
v___x_230_ = lean_array_push(v___x_229_, v_hc_45_);
v___x_231_ = lean_array_push(v___x_230_, v_arg_75_);
v___x_232_ = lean_array_push(v___x_231_, v_arg_68_);
v___x_233_ = lean_array_push(v___x_232_, v_arg_67_);
v___x_234_ = l_Lean_mkAppN(v___x_225_, v___x_233_);
lean_dec_ref(v___x_233_);
v___x_235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
v___x_236_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_236_, 0, v___x_223_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*2, v___x_78_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 0, v___x_236_);
v___x_238_ = v___x_171_;
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
lean_dec(v___x_165_);
lean_dec_ref(v_arg_75_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_69_);
lean_dec_ref(v_arg_68_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_hc_45_);
v_a_241_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_248_ == 0)
{
v___x_243_ = v___x_168_;
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_168_);
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
lean_dec(v___x_165_);
lean_dec_ref(v_arg_75_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_69_);
lean_dec_ref(v_arg_68_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_hc_45_);
v_a_249_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_256_ == 0)
{
v___x_251_ = v___x_166_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_166_);
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
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = l_Lean_Expr_constLevels_x21(v___x_71_);
lean_dec_ref(v___x_71_);
lean_inc(v_a_50_);
lean_inc_ref(v_a_49_);
lean_inc(v_a_48_);
lean_inc_ref(v_a_47_);
lean_inc_ref(v_hc_45_);
v___x_258_ = lean_infer_type(v_hc_45_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_object* v_a_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v_a_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_a_259_);
lean_dec_ref_known(v___x_258_, 1);
v___x_260_ = lean_obj_once(&l_Lean_Meta_rwIfWith___closed__17, &l_Lean_Meta_rwIfWith___closed__17_once, _init_l_Lean_Meta_rwIfWith___closed__17);
lean_inc_ref(v_arg_69_);
v___x_261_ = l_Lean_Meta_mkEq(v_arg_69_, v___x_260_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_263_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_a_262_);
lean_dec_ref_known(v___x_261_, 1);
v___x_263_ = l_Lean_Meta_isExprDefEq(v_a_259_, v_a_262_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_335_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_335_ == 0)
{
v___x_266_ = v___x_263_;
v_isShared_267_ = v_isSharedCheck_335_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_263_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_335_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
uint8_t v___x_268_; 
v___x_268_ = lean_unbox(v_a_264_);
lean_dec(v_a_264_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
lean_del_object(v___x_266_);
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
lean_inc_ref(v_arg_69_);
v___x_272_ = l_Lean_Meta_mkEq(v_arg_69_, v___x_271_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
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
lean_dec(v___x_257_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_69_);
lean_dec_ref(v_arg_68_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_hc_45_);
goto v___jp_52_;
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_293_; 
lean_dec_ref(v_e_46_);
v___x_280_ = ((lean_object*)(l_Lean_Meta_rwIfWith___closed__22));
v___x_281_ = l_Lean_mkConst(v___x_280_, v___x_257_);
v___x_282_ = lean_unsigned_to_nat(5u);
v___x_283_ = lean_mk_empty_array_with_capacity(v___x_282_);
v___x_284_ = lean_array_push(v___x_283_, v_arg_70_);
v___x_285_ = lean_array_push(v___x_284_, v_arg_69_);
v___x_286_ = lean_array_push(v___x_285_, v_arg_68_);
lean_inc_ref(v_arg_67_);
v___x_287_ = lean_array_push(v___x_286_, v_arg_67_);
v___x_288_ = lean_array_push(v___x_287_, v_hc_45_);
v___x_289_ = l_Lean_mkAppN(v___x_281_, v___x_288_);
lean_dec_ref(v___x_288_);
v___x_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
v___x_291_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_291_, 0, v_arg_67_);
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
lean_dec(v___x_257_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_69_);
lean_dec_ref(v_arg_68_);
lean_dec_ref(v_arg_67_);
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
lean_dec(v___x_257_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_69_);
lean_dec_ref(v_arg_68_);
lean_dec_ref(v_arg_67_);
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
lean_dec(v___x_257_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_69_);
lean_dec_ref(v_arg_68_);
lean_dec_ref(v_arg_67_);
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
v___x_321_ = l_Lean_mkConst(v___x_320_, v___x_257_);
v___x_322_ = lean_unsigned_to_nat(5u);
v___x_323_ = lean_mk_empty_array_with_capacity(v___x_322_);
v___x_324_ = lean_array_push(v___x_323_, v_arg_70_);
v___x_325_ = lean_array_push(v___x_324_, v_arg_69_);
lean_inc_ref(v_arg_68_);
v___x_326_ = lean_array_push(v___x_325_, v_arg_68_);
v___x_327_ = lean_array_push(v___x_326_, v_arg_67_);
v___x_328_ = lean_array_push(v___x_327_, v_hc_45_);
v___x_329_ = l_Lean_mkAppN(v___x_321_, v___x_328_);
lean_dec_ref(v___x_328_);
v___x_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
v___x_331_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_331_, 0, v_arg_68_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*2, v___x_73_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 0, v___x_331_);
v___x_333_ = v___x_266_;
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
lean_dec(v___x_257_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_69_);
lean_dec_ref(v_arg_68_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_hc_45_);
v_a_336_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_263_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_263_);
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
lean_dec(v_a_259_);
lean_dec(v___x_257_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_69_);
lean_dec_ref(v_arg_68_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_hc_45_);
v_a_344_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_261_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_261_);
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
lean_dec(v___x_257_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_69_);
lean_dec_ref(v_arg_68_);
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_e_46_);
lean_dec_ref(v_hc_45_);
v_a_352_ = lean_ctor_get(v___x_258_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_258_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_258_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__2___redArg(lean_object* v_e_376_, lean_object* v___y_377_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__2___redArg___boxed(lean_object* v_e_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__2___redArg(v_e_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v_e_384_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__2(lean_object* v_e_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__2___redArg(v_e_388_, v___y_392_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__2___boxed(lean_object* v_e_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__2(v_e_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec_ref(v_e_395_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(lean_object* v_e_402_, lean_object* v___y_403_){
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
v___x_422_ = lean_st_ref_put(v___y_403_, v___x_421_);
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v_fst_410_);
return v___x_423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg___boxed(lean_object* v_e_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v_e_427_, v___y_428_);
lean_dec(v___y_428_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5(lean_object* v_e_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v_e_431_, v___y_433_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___boxed(lean_object* v_e_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5(v_e_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
return v_res_444_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__0(void){
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__1(void){
_start:
{
size_t v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_448_ = ((size_t)5ULL);
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = lean_unsigned_to_nat(32u);
v___x_451_ = lean_mk_empty_array_with_capacity(v___x_450_);
v___x_452_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__0);
v___x_453_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v___x_451_);
lean_ctor_set(v___x_453_, 2, v___x_449_);
lean_ctor_set(v___x_453_, 3, v___x_449_);
lean_ctor_set_usize(v___x_453_, 4, v___x_448_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg(lean_object* v___y_454_){
_start:
{
lean_object* v___x_456_; lean_object* v_traceState_457_; lean_object* v_traces_458_; lean_object* v___x_459_; lean_object* v_traceState_460_; lean_object* v_env_461_; lean_object* v_nextMacroScope_462_; lean_object* v_ngen_463_; lean_object* v_auxDeclNGen_464_; lean_object* v_cache_465_; lean_object* v_recordedDeps_466_; lean_object* v_messages_467_; lean_object* v_infoState_468_; lean_object* v_snapshotTasks_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_488_; 
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
v_recordedDeps_466_ = lean_ctor_get(v___x_459_, 6);
v_messages_467_ = lean_ctor_get(v___x_459_, 7);
v_infoState_468_ = lean_ctor_get(v___x_459_, 8);
v_snapshotTasks_469_ = lean_ctor_get(v___x_459_, 9);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_488_ == 0)
{
v___x_471_ = v___x_459_;
v_isShared_472_ = v_isSharedCheck_488_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_snapshotTasks_469_);
lean_inc(v_infoState_468_);
lean_inc(v_messages_467_);
lean_inc(v_recordedDeps_466_);
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
v___x_477_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___closed__1);
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
lean_ctor_set(v_reuseFailAlloc_484_, 6, v_recordedDeps_466_);
lean_ctor_set(v_reuseFailAlloc_484_, 7, v_messages_467_);
lean_ctor_set(v_reuseFailAlloc_484_, 8, v_infoState_468_);
lean_ctor_set(v_reuseFailAlloc_484_, 9, v_snapshotTasks_469_);
v___x_481_ = v_reuseFailAlloc_484_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_st_ref_put(v___y_454_, v___x_481_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v_traces_458_);
return v___x_483_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg___boxed(lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg(v___y_489_);
lean_dec(v___y_489_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10(lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg(v___y_495_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___boxed(lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10(v___y_498_, v___y_499_, v___y_500_, v___y_501_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
return v_res_503_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11(lean_object* v_opts_504_, lean_object* v_opt_505_){
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
lean_dec_ref_known(v___x_509_, 1);
if (lean_obj_tag(v_val_511_) == 1)
{
uint8_t v_v_512_; 
v_v_512_ = lean_ctor_get_uint8(v_val_511_, 0);
lean_dec_ref_known(v_val_511_, 0);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11___boxed(lean_object* v_opts_514_, lean_object* v_opt_515_){
_start:
{
uint8_t v_res_516_; lean_object* v_r_517_; 
v_res_516_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11(v_opts_514_, v_opt_515_);
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
uint8_t v___x_89049__boxed_538_; lean_object* v_res_539_; 
v___x_89049__boxed_538_ = lean_unbox(v___x_531_);
v_res_539_ = l_Lean_Meta_rwMatcher___lam__0(v_e_530_, v___x_89049__boxed_538_, v_____r_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__1(lean_object* v___x_546_, uint8_t v___x_547_, lean_object* v_e_548_, lean_object* v_x_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_555_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__1, &l_Lean_Meta_rwMatcher___lam__1___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__1);
v___x_556_ = l_Lean_MessageData_ofConstName(v___x_546_, v___x_547_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__1___boxed(lean_object* v___x_563_, lean_object* v___x_564_, lean_object* v_e_565_, lean_object* v_x_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
uint8_t v___x_89091__boxed_572_; lean_object* v_res_573_; 
v___x_89091__boxed_572_ = lean_unbox(v___x_564_);
v_res_573_ = l_Lean_Meta_rwMatcher___lam__1(v___x_563_, v___x_89091__boxed_572_, v_e_565_, v_x_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec_ref(v_x_566_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3_spec__4(lean_object* v_msgData_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v___x_580_; lean_object* v_env_581_; uint8_t v___x_582_; lean_object* v_env_583_; lean_object* v___x_584_; lean_object* v_toCold_585_; lean_object* v_mctx_586_; lean_object* v_lctx_587_; lean_object* v_options_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_580_ = lean_st_ref_get(v___y_578_);
v_env_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc_ref(v_env_581_);
lean_dec(v___x_580_);
v___x_582_ = 0;
v_env_583_ = l_Lean_Environment_setRecordingDeps(v_env_581_, v___x_582_);
v___x_584_ = lean_st_ref_get(v___y_576_);
v_toCold_585_ = lean_ctor_get(v___y_577_, 0);
v_mctx_586_ = lean_ctor_get(v___x_584_, 0);
lean_inc_ref(v_mctx_586_);
lean_dec(v___x_584_);
v_lctx_587_ = lean_ctor_get(v___y_575_, 2);
v_options_588_ = lean_ctor_get(v_toCold_585_, 2);
lean_inc_ref(v_options_588_);
lean_inc_ref(v_lctx_587_);
v___x_589_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_589_, 0, v_env_583_);
lean_ctor_set(v___x_589_, 1, v_mctx_586_);
lean_ctor_set(v___x_589_, 2, v_lctx_587_);
lean_ctor_set(v___x_589_, 3, v_options_588_);
v___x_590_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
lean_ctor_set(v___x_590_, 1, v_msgData_574_);
v___x_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3_spec__4___boxed(lean_object* v_msgData_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3_spec__4(v_msgData_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(lean_object* v_msg_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v_ref_605_; lean_object* v___x_606_; lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_615_; 
v_ref_605_ = lean_ctor_get(v___y_602_, 2);
v___x_606_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3_spec__4(v_msg_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
v_a_607_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_615_ == 0)
{
v___x_609_ = v___x_606_;
v_isShared_610_ = v_isSharedCheck_615_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_606_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_615_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_613_; 
lean_inc(v_ref_605_);
v___x_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_611_, 0, v_ref_605_);
lean_ctor_set(v___x_611_, 1, v_a_607_);
if (v_isShared_610_ == 0)
{
lean_ctor_set_tag(v___x_609_, 1);
lean_ctor_set(v___x_609_, 0, v___x_611_);
v___x_613_ = v___x_609_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg___boxed(lean_object* v_msg_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v_msg_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
return v_res_622_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6_spec__18___redArg(lean_object* v_keys_623_, lean_object* v_i_624_, lean_object* v_k_625_){
_start:
{
lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_626_ = lean_array_get_size(v_keys_623_);
v___x_627_ = lean_nat_dec_lt(v_i_624_, v___x_626_);
if (v___x_627_ == 0)
{
lean_dec(v_i_624_);
return v___x_627_;
}
else
{
lean_object* v_k_x27_628_; uint8_t v___x_629_; 
v_k_x27_628_ = lean_array_fget_borrowed(v_keys_623_, v_i_624_);
v___x_629_ = l_Lean_instBEqMVarId_beq(v_k_625_, v_k_x27_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_unsigned_to_nat(1u);
v___x_631_ = lean_nat_add(v_i_624_, v___x_630_);
lean_dec(v_i_624_);
v_i_624_ = v___x_631_;
goto _start;
}
else
{
lean_dec(v_i_624_);
return v___x_627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6_spec__18___redArg___boxed(lean_object* v_keys_633_, lean_object* v_i_634_, lean_object* v_k_635_){
_start:
{
uint8_t v_res_636_; lean_object* v_r_637_; 
v_res_636_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6_spec__18___redArg(v_keys_633_, v_i_634_, v_k_635_);
lean_dec(v_k_635_);
lean_dec_ref(v_keys_633_);
v_r_637_ = lean_box(v_res_636_);
return v_r_637_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6___redArg(lean_object* v_x_638_, size_t v_x_639_, lean_object* v_x_640_){
_start:
{
if (lean_obj_tag(v_x_638_) == 0)
{
lean_object* v_es_641_; lean_object* v___x_642_; size_t v___x_643_; size_t v___x_644_; lean_object* v_j_645_; lean_object* v___x_646_; 
v_es_641_ = lean_ctor_get(v_x_638_, 0);
v___x_642_ = lean_box(2);
v___x_643_ = ((size_t)31ULL);
v___x_644_ = lean_usize_land(v_x_639_, v___x_643_);
v_j_645_ = lean_usize_to_nat(v___x_644_);
v___x_646_ = lean_array_get_borrowed(v___x_642_, v_es_641_, v_j_645_);
lean_dec(v_j_645_);
switch(lean_obj_tag(v___x_646_))
{
case 0:
{
lean_object* v_key_647_; uint8_t v___x_648_; 
v_key_647_ = lean_ctor_get(v___x_646_, 0);
v___x_648_ = l_Lean_instBEqMVarId_beq(v_x_640_, v_key_647_);
return v___x_648_;
}
case 1:
{
lean_object* v_node_649_; size_t v___x_650_; size_t v___x_651_; 
v_node_649_ = lean_ctor_get(v___x_646_, 0);
v___x_650_ = ((size_t)5ULL);
v___x_651_ = lean_usize_shift_right(v_x_639_, v___x_650_);
v_x_638_ = v_node_649_;
v_x_639_ = v___x_651_;
goto _start;
}
default: 
{
uint8_t v___x_653_; 
v___x_653_ = 0;
return v___x_653_;
}
}
}
else
{
lean_object* v_ks_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v_ks_654_ = lean_ctor_get(v_x_638_, 0);
v___x_655_ = lean_unsigned_to_nat(0u);
v___x_656_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6_spec__18___redArg(v_ks_654_, v___x_655_, v_x_640_);
return v___x_656_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6___redArg___boxed(lean_object* v_x_657_, lean_object* v_x_658_, lean_object* v_x_659_){
_start:
{
size_t v_x_89212__boxed_660_; uint8_t v_res_661_; lean_object* v_r_662_; 
v_x_89212__boxed_660_ = lean_unbox_usize(v_x_658_);
lean_dec(v_x_658_);
v_res_661_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6___redArg(v_x_657_, v_x_89212__boxed_660_, v_x_659_);
lean_dec(v_x_659_);
lean_dec_ref(v_x_657_);
v_r_662_ = lean_box(v_res_661_);
return v_r_662_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1___redArg(lean_object* v_x_663_, lean_object* v_x_664_){
_start:
{
uint64_t v___x_665_; size_t v___x_666_; uint8_t v___x_667_; 
v___x_665_ = l_Lean_instHashableMVarId_hash(v_x_664_);
v___x_666_ = lean_uint64_to_usize(v___x_665_);
v___x_667_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6___redArg(v_x_663_, v___x_666_, v_x_664_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1___redArg___boxed(lean_object* v_x_668_, lean_object* v_x_669_){
_start:
{
uint8_t v_res_670_; lean_object* v_r_671_; 
v_res_670_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1___redArg(v_x_668_, v_x_669_);
lean_dec(v_x_669_);
lean_dec_ref(v_x_668_);
v_r_671_ = lean_box(v_res_670_);
return v_r_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1___redArg(lean_object* v_mvarId_672_, lean_object* v___y_673_){
_start:
{
lean_object* v___x_675_; lean_object* v_mctx_676_; lean_object* v_eAssignment_677_; uint8_t v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_675_ = lean_st_ref_get(v___y_673_);
v_mctx_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc_ref(v_mctx_676_);
lean_dec(v___x_675_);
v_eAssignment_677_ = lean_ctor_get(v_mctx_676_, 8);
lean_inc_ref(v_eAssignment_677_);
lean_dec_ref(v_mctx_676_);
v___x_678_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1___redArg(v_eAssignment_677_, v_mvarId_672_);
lean_dec_ref(v_eAssignment_677_);
v___x_679_ = lean_box(v___x_678_);
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1___redArg___boxed(lean_object* v_mvarId_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1___redArg(v_mvarId_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec(v_mvarId_681_);
return v_res_684_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__0));
v___x_687_ = l_Lean_stringToMessageData(v___x_686_);
return v___x_687_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__2));
v___x_690_ = l_Lean_stringToMessageData(v___x_689_);
return v___x_690_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__5(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__4));
v___x_693_ = l_Lean_stringToMessageData(v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8(lean_object* v_as_694_, size_t v_sz_695_, size_t v_i_696_, lean_object* v_b_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_a_704_; uint8_t v___x_708_; 
v___x_708_ = lean_usize_dec_lt(v_i_696_, v_sz_695_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; 
v___x_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_709_, 0, v_b_697_);
return v___x_709_;
}
else
{
lean_object* v___x_710_; lean_object* v_a_711_; lean_object* v___x_712_; 
v___x_710_ = lean_box(0);
v_a_711_ = lean_array_uget_borrowed(v_as_694_, v_i_696_);
v___x_712_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1___redArg(v_a_711_, v___y_699_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; uint8_t v___x_714_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_a_713_);
lean_dec_ref_known(v___x_712_, 1);
v___x_714_ = lean_unbox(v_a_713_);
lean_dec(v_a_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; 
lean_inc(v_a_711_);
v___x_715_ = l_Lean_MVarId_getType(v_a_711_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; uint8_t v___x_717_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_a_716_);
lean_dec_ref_known(v___x_715_, 1);
v___x_717_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_a_716_);
if (v___x_717_ == 0)
{
uint8_t v___x_718_; 
v___x_718_ = l_Lean_Expr_isEq(v_a_716_);
if (v___x_718_ == 0)
{
uint8_t v___x_719_; 
v___x_719_ = l_Lean_Expr_isHEq(v_a_716_);
lean_dec(v_a_716_);
if (v___x_719_ == 0)
{
v_a_704_ = v___x_710_;
goto v___jp_703_;
}
else
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_Meta_saveState___redArg(v___y_699_, v___y_701_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_722_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_a_721_);
lean_dec_ref_known(v___x_720_, 1);
lean_inc(v_a_711_);
v___x_722_ = l_Lean_MVarId_assumption(v_a_711_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_dec_ref_known(v___x_722_, 1);
lean_dec(v_a_721_);
v_a_704_ = v___x_710_;
goto v___jp_703_;
}
else
{
lean_object* v_a_723_; uint8_t v___x_724_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
v___x_724_ = l_Lean_Exception_isInterrupt(v_a_723_);
if (v___x_724_ == 0)
{
uint8_t v___x_725_; 
lean_inc(v_a_723_);
v___x_725_ = l_Lean_Exception_isRuntime(v_a_723_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; 
lean_dec_ref_known(v___x_722_, 1);
v___x_726_ = l_Lean_Meta_SavedState_restore___redArg(v_a_721_, v___y_699_, v___y_701_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v___x_727_; 
lean_dec_ref_known(v___x_726_, 1);
v___x_727_ = l_Lean_Meta_saveState___redArg(v___y_699_, v___y_701_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_729_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_728_);
lean_dec_ref_known(v___x_727_, 1);
lean_inc(v_a_711_);
v___x_729_ = l_Lean_MVarId_hrefl(v_a_711_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_dec_ref_known(v___x_729_, 1);
lean_dec(v_a_728_);
v_a_704_ = v___x_710_;
goto v___jp_703_;
}
else
{
lean_object* v_a_730_; uint8_t v___x_731_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
v___x_731_ = l_Lean_Exception_isInterrupt(v_a_730_);
if (v___x_731_ == 0)
{
uint8_t v___x_732_; 
lean_inc(v_a_730_);
v___x_732_ = l_Lean_Exception_isRuntime(v_a_730_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; 
lean_dec_ref_known(v___x_729_, 1);
v___x_733_ = l_Lean_Meta_SavedState_restore___redArg(v_a_728_, v___y_699_, v___y_701_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v___x_734_; 
lean_dec_ref_known(v___x_733_, 1);
v___x_734_ = l_Lean_Meta_saveState___redArg(v___y_699_, v___y_701_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_768_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_768_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_768_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_768_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v_a_740_; lean_object* v___x_763_; 
lean_inc(v_a_711_);
v___x_763_ = l_Lean_MVarId_heqOfEq(v_a_711_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___x_765_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v___x_765_ = l_Lean_MVarId_assumption(v_a_764_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_dec_ref_known(v___x_765_, 1);
lean_del_object(v___x_737_);
lean_dec(v_a_735_);
v_a_704_ = v___x_710_;
goto v___jp_703_;
}
else
{
lean_object* v_a_766_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
v_a_740_ = v_a_766_;
goto v___jp_739_;
}
}
else
{
lean_object* v_a_767_; 
v_a_767_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_767_);
lean_dec_ref_known(v___x_763_, 1);
v_a_740_ = v_a_767_;
goto v___jp_739_;
}
v___jp_739_:
{
uint8_t v___x_741_; 
v___x_741_ = l_Lean_Exception_isInterrupt(v_a_740_);
if (v___x_741_ == 0)
{
uint8_t v___x_742_; 
lean_inc_ref(v_a_740_);
v___x_742_ = l_Lean_Exception_isRuntime(v_a_740_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; 
lean_dec_ref(v_a_740_);
lean_del_object(v___x_737_);
v___x_743_ = l_Lean_Meta_SavedState_restore___redArg(v_a_735_, v___y_699_, v___y_701_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_755_; 
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_755_ == 0)
{
lean_object* v_unused_756_; 
v_unused_756_ = lean_ctor_get(v___x_743_, 0);
lean_dec(v_unused_756_);
v___x_745_ = v___x_743_;
v_isShared_746_ = v_isSharedCheck_755_;
goto v_resetjp_744_;
}
else
{
lean_dec(v___x_743_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_755_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_747_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1);
lean_inc(v_a_711_);
if (v_isShared_746_ == 0)
{
lean_ctor_set_tag(v___x_745_, 1);
lean_ctor_set(v___x_745_, 0, v_a_711_);
v___x_749_ = v___x_745_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_711_);
v___x_749_ = v_reuseFailAlloc_754_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_747_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
v___x_752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_750_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_752_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_dec_ref_known(v___x_753_, 1);
v_a_704_ = v___x_710_;
goto v___jp_703_;
}
else
{
return v___x_753_;
}
}
}
}
else
{
return v___x_743_;
}
}
else
{
lean_object* v___x_758_; 
lean_dec(v_a_735_);
if (v_isShared_738_ == 0)
{
lean_ctor_set_tag(v___x_737_, 1);
lean_ctor_set(v___x_737_, 0, v_a_740_);
v___x_758_ = v___x_737_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_740_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
else
{
lean_object* v___x_761_; 
lean_dec(v_a_735_);
if (v_isShared_738_ == 0)
{
lean_ctor_set_tag(v___x_737_, 1);
lean_ctor_set(v___x_737_, 0, v_a_740_);
v___x_761_ = v___x_737_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_740_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
v_a_769_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_734_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_734_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
else
{
return v___x_733_;
}
}
else
{
lean_dec(v_a_728_);
return v___x_729_;
}
}
else
{
lean_dec(v_a_728_);
return v___x_729_;
}
}
}
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
v_a_777_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_784_ == 0)
{
v___x_779_ = v___x_727_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_727_);
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
return v___x_726_;
}
}
else
{
lean_dec(v_a_721_);
return v___x_722_;
}
}
else
{
lean_dec(v_a_721_);
return v___x_722_;
}
}
}
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
v_a_785_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_720_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_720_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
}
else
{
lean_object* v___x_793_; 
lean_dec(v_a_716_);
v___x_793_ = l_Lean_Meta_saveState___redArg(v___y_699_, v___y_701_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; lean_object* v___x_795_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_a_794_);
lean_dec_ref_known(v___x_793_, 1);
lean_inc(v_a_711_);
v___x_795_ = l_Lean_MVarId_assumption(v_a_711_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_dec_ref_known(v___x_795_, 1);
lean_dec(v_a_794_);
v_a_704_ = v___x_710_;
goto v___jp_703_;
}
else
{
lean_object* v_a_796_; uint8_t v___x_797_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
v___x_797_ = l_Lean_Exception_isInterrupt(v_a_796_);
if (v___x_797_ == 0)
{
uint8_t v___x_798_; 
lean_inc(v_a_796_);
v___x_798_ = l_Lean_Exception_isRuntime(v_a_796_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; 
lean_dec_ref_known(v___x_795_, 1);
v___x_799_ = l_Lean_Meta_SavedState_restore___redArg(v_a_794_, v___y_699_, v___y_701_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v___x_800_; 
lean_dec_ref_known(v___x_799_, 1);
v___x_800_ = l_Lean_Meta_saveState___redArg(v___y_699_, v___y_701_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v___x_802_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_801_);
lean_dec_ref_known(v___x_800_, 1);
lean_inc(v_a_711_);
v___x_802_ = l_Lean_MVarId_refl(v_a_711_, v___x_708_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_dec_ref_known(v___x_802_, 1);
lean_dec(v_a_801_);
v_a_704_ = v___x_710_;
goto v___jp_703_;
}
else
{
lean_object* v_a_803_; uint8_t v___x_804_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
v___x_804_ = l_Lean_Exception_isInterrupt(v_a_803_);
if (v___x_804_ == 0)
{
uint8_t v___x_805_; 
lean_inc(v_a_803_);
v___x_805_ = l_Lean_Exception_isRuntime(v_a_803_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; 
lean_dec_ref_known(v___x_802_, 1);
v___x_806_ = l_Lean_Meta_SavedState_restore___redArg(v_a_801_, v___y_699_, v___y_701_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_818_; 
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_818_ == 0)
{
lean_object* v_unused_819_; 
v_unused_819_ = lean_ctor_get(v___x_806_, 0);
lean_dec(v_unused_819_);
v___x_808_ = v___x_806_;
v_isShared_809_ = v_isSharedCheck_818_;
goto v_resetjp_807_;
}
else
{
lean_dec(v___x_806_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_818_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_810_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1);
lean_inc(v_a_711_);
if (v_isShared_809_ == 0)
{
lean_ctor_set_tag(v___x_808_, 1);
lean_ctor_set(v___x_808_, 0, v_a_711_);
v___x_812_ = v___x_808_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_711_);
v___x_812_ = v_reuseFailAlloc_817_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_810_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
v___x_815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_815_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_dec_ref_known(v___x_816_, 1);
v_a_704_ = v___x_710_;
goto v___jp_703_;
}
else
{
return v___x_816_;
}
}
}
}
else
{
return v___x_806_;
}
}
else
{
lean_dec(v_a_801_);
return v___x_802_;
}
}
else
{
lean_dec(v_a_801_);
return v___x_802_;
}
}
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
v_a_820_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_800_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_800_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
else
{
return v___x_799_;
}
}
else
{
lean_dec(v_a_794_);
return v___x_795_;
}
}
else
{
lean_dec(v_a_794_);
return v___x_795_;
}
}
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
v_a_828_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_793_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_793_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
}
else
{
lean_object* v___x_836_; 
lean_dec(v_a_716_);
v___x_836_ = l_Lean_Meta_saveState___redArg(v___y_699_, v___y_701_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_a_837_; lean_object* v___x_838_; 
v_a_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_a_837_);
lean_dec_ref_known(v___x_836_, 1);
lean_inc(v_a_711_);
v___x_838_ = l_Lean_MVarId_assumption(v_a_711_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_dec_ref_known(v___x_838_, 1);
lean_dec(v_a_837_);
v_a_704_ = v___x_710_;
goto v___jp_703_;
}
else
{
lean_object* v_a_839_; uint8_t v___x_840_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
v___x_840_ = l_Lean_Exception_isInterrupt(v_a_839_);
if (v___x_840_ == 0)
{
uint8_t v___x_841_; 
lean_inc(v_a_839_);
v___x_841_ = l_Lean_Exception_isRuntime(v_a_839_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; 
lean_dec_ref_known(v___x_838_, 1);
v___x_842_ = l_Lean_Meta_SavedState_restore___redArg(v_a_837_, v___y_699_, v___y_701_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_854_; 
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; 
v_unused_855_ = lean_ctor_get(v___x_842_, 0);
lean_dec(v_unused_855_);
v___x_844_ = v___x_842_;
v_isShared_845_ = v_isSharedCheck_854_;
goto v_resetjp_843_;
}
else
{
lean_dec(v___x_842_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_854_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_846_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__5);
lean_inc(v_a_711_);
if (v_isShared_845_ == 0)
{
lean_ctor_set_tag(v___x_844_, 1);
lean_ctor_set(v___x_844_, 0, v_a_711_);
v___x_848_ = v___x_844_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_711_);
v___x_848_ = v_reuseFailAlloc_853_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_846_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
v___x_850_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
v___x_851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_849_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_851_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_dec_ref_known(v___x_852_, 1);
v_a_704_ = v___x_710_;
goto v___jp_703_;
}
else
{
return v___x_852_;
}
}
}
}
else
{
return v___x_842_;
}
}
else
{
lean_dec(v_a_837_);
return v___x_838_;
}
}
else
{
lean_dec(v_a_837_);
return v___x_838_;
}
}
}
else
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
v_a_856_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_836_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_836_);
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
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
v_a_864_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_715_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_715_);
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
v_a_704_ = v___x_710_;
goto v___jp_703_;
}
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
v_a_872_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_712_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_712_);
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
v___jp_703_:
{
size_t v___x_705_; size_t v___x_706_; 
v___x_705_ = ((size_t)1ULL);
v___x_706_ = lean_usize_add(v_i_696_, v___x_705_);
v_i_696_ = v___x_706_;
v_b_697_ = v_a_704_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___boxed(lean_object* v_as_880_, lean_object* v_sz_881_, lean_object* v_i_882_, lean_object* v_b_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
size_t v_sz_boxed_889_; size_t v_i_boxed_890_; lean_object* v_res_891_; 
v_sz_boxed_889_ = lean_unbox_usize(v_sz_881_);
lean_dec(v_sz_881_);
v_i_boxed_890_ = lean_unbox_usize(v_i_882_);
lean_dec(v_i_882_);
v_res_891_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8(v_as_880_, v_sz_boxed_889_, v_i_boxed_890_, v_b_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec_ref(v_as_880_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9(lean_object* v_as_892_, size_t v_i_893_, size_t v_stop_894_, lean_object* v_b_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_a_902_; uint8_t v___x_906_; 
v___x_906_ = lean_usize_dec_eq(v_i_893_, v_stop_894_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = lean_array_uget_borrowed(v_as_892_, v_i_893_);
v___x_908_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1___redArg(v___x_907_, v___y_897_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; uint8_t v___x_910_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_a_909_);
lean_dec_ref_known(v___x_908_, 1);
v___x_910_ = lean_unbox(v_a_909_);
lean_dec(v_a_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; 
lean_inc(v___x_907_);
v___x_911_ = lean_array_push(v_b_895_, v___x_907_);
v_a_902_ = v___x_911_;
goto v___jp_901_;
}
else
{
v_a_902_ = v_b_895_;
goto v___jp_901_;
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec_ref(v_b_895_);
v_a_912_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_908_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_908_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
else
{
lean_object* v___x_920_; 
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v_b_895_);
return v___x_920_;
}
v___jp_901_:
{
size_t v___x_903_; size_t v___x_904_; 
v___x_903_ = ((size_t)1ULL);
v___x_904_ = lean_usize_add(v_i_893_, v___x_903_);
v_i_893_ = v___x_904_;
v_b_895_ = v_a_902_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9___boxed(lean_object* v_as_921_, lean_object* v_i_922_, lean_object* v_stop_923_, lean_object* v_b_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
size_t v_i_boxed_930_; size_t v_stop_boxed_931_; lean_object* v_res_932_; 
v_i_boxed_930_ = lean_unbox_usize(v_i_922_);
lean_dec(v_i_922_);
v_stop_boxed_931_ = lean_unbox_usize(v_stop_923_);
lean_dec(v_stop_923_);
v_res_932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9(v_as_921_, v_i_boxed_930_, v_stop_boxed_931_, v_b_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec_ref(v_as_921_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4(size_t v_sz_933_, size_t v_i_934_, lean_object* v_bs_935_){
_start:
{
uint8_t v___x_936_; 
v___x_936_ = lean_usize_dec_lt(v_i_934_, v_sz_933_);
if (v___x_936_ == 0)
{
return v_bs_935_;
}
else
{
lean_object* v_v_937_; lean_object* v___x_938_; lean_object* v_bs_x27_939_; lean_object* v___x_940_; size_t v___x_941_; size_t v___x_942_; lean_object* v___x_943_; 
v_v_937_ = lean_array_uget(v_bs_935_, v_i_934_);
v___x_938_ = lean_unsigned_to_nat(0u);
v_bs_x27_939_ = lean_array_uset(v_bs_935_, v_i_934_, v___x_938_);
v___x_940_ = l_Lean_Expr_mvarId_x21(v_v_937_);
lean_dec(v_v_937_);
v___x_941_ = ((size_t)1ULL);
v___x_942_ = lean_usize_add(v_i_934_, v___x_941_);
v___x_943_ = lean_array_uset(v_bs_x27_939_, v_i_934_, v___x_940_);
v_i_934_ = v___x_942_;
v_bs_935_ = v___x_943_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4___boxed(lean_object* v_sz_945_, lean_object* v_i_946_, lean_object* v_bs_947_){
_start:
{
size_t v_sz_boxed_948_; size_t v_i_boxed_949_; lean_object* v_res_950_; 
v_sz_boxed_948_ = lean_unbox_usize(v_sz_945_);
lean_dec(v_sz_945_);
v_i_boxed_949_ = lean_unbox_usize(v_i_946_);
lean_dec(v_i_946_);
v_res_950_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4(v_sz_boxed_948_, v_i_boxed_949_, v_bs_947_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__7(lean_object* v_a_951_, lean_object* v_a_952_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2(uint8_t v___x_1003_, lean_object* v___x_1004_, lean_object* v_fst_1005_, lean_object* v___x_1006_, lean_object* v_e_1007_, uint8_t v___x_1008_, lean_object* v_snd_1009_, lean_object* v_____r_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v___y_1017_; lean_object* v_proof_1018_; lean_object* v___x_1022_; uint8_t v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; uint8_t v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v_a_1076_; size_t v_sz_1099_; size_t v___x_1100_; lean_object* v___x_1101_; uint8_t v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; uint8_t v_fst_1136_; lean_object* v_fst_1137_; lean_object* v_snd_1138_; lean_object* v___x_1172_; lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1022_ = l_Lean_mkAppN(v___x_1004_, v_fst_1005_);
v_sz_1099_ = lean_array_size(v_fst_1005_);
v___x_1100_ = ((size_t)0ULL);
v___x_1101_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4(v_sz_1099_, v___x_1100_, v_fst_1005_);
v___x_1172_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1173_ = lean_unsigned_to_nat(4u);
v___x_1174_ = l_Lean_Expr_isAppOfArity(v_snd_1009_, v___x_1172_, v___x_1173_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1175_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1176_ = lean_unsigned_to_nat(3u);
v___x_1177_ = l_Lean_Expr_isAppOfArity(v_snd_1009_, v___x_1175_, v___x_1176_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec_ref(v___x_1101_);
lean_dec_ref(v___x_1022_);
lean_dec_ref(v_e_1007_);
v___x_1178_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1179_ = l_Lean_MessageData_ofConstName(v___x_1006_, v___x_1008_);
v___x_1180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1178_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1180_);
lean_ctor_set(v___x_1182_, 1, v___x_1181_);
v___x_1183_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1182_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1183_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1183_);
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
else
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1192_ = l_Lean_Expr_appFn_x21(v_snd_1009_);
v___x_1193_ = l_Lean_Expr_appArg_x21(v___x_1192_);
lean_dec_ref(v___x_1192_);
v___x_1194_ = l_Lean_Expr_appArg_x21(v_snd_1009_);
v_fst_1136_ = v___x_1008_;
v_fst_1137_ = v___x_1193_;
v_snd_1138_ = v___x_1194_;
goto v___jp_1135_;
}
}
else
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1195_ = l_Lean_Expr_appFn_x21(v_snd_1009_);
v___x_1196_ = l_Lean_Expr_appFn_x21(v___x_1195_);
lean_dec_ref(v___x_1195_);
v___x_1197_ = l_Lean_Expr_appArg_x21(v___x_1196_);
lean_dec_ref(v___x_1196_);
v___x_1198_ = l_Lean_Expr_appArg_x21(v_snd_1009_);
v_fst_1136_ = v___x_1003_;
v_fst_1137_ = v___x_1197_;
v_snd_1138_ = v___x_1198_;
goto v___jp_1135_;
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
v___jp_1023_:
{
lean_object* v___x_1030_; lean_object* v_a_1031_; lean_object* v___x_1032_; 
v___x_1030_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___y_1025_, v___y_1027_);
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_a_1031_);
lean_dec_ref(v___x_1030_);
v___x_1032_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1022_, v___y_1027_);
if (v___y_1024_ == 0)
{
lean_object* v_a_1033_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_a_1033_);
lean_dec_ref(v___x_1032_);
v___y_1017_ = v_a_1031_;
v_proof_1018_ = v_a_1033_;
goto v___jp_1016_;
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1035_; 
v_a_1034_ = lean_ctor_get(v___x_1032_, 0);
lean_inc_n(v_a_1034_, 2);
lean_dec_ref(v___x_1032_);
v___x_1035_ = l_Lean_Meta_mkEqOfHEq(v_a_1034_, v___x_1003_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; 
lean_dec(v_a_1034_);
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref_known(v___x_1035_, 1);
v___y_1017_ = v_a_1031_;
v_proof_1018_ = v_a_1036_;
goto v___jp_1016_;
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1068_; 
lean_dec(v_a_1031_);
v_a_1037_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1039_ = v___x_1035_;
v_isShared_1040_ = v_isSharedCheck_1068_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1035_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1068_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
uint8_t v___x_1041_; 
v___x_1041_ = l_Lean_Exception_isInterrupt(v_a_1037_);
if (v___x_1041_ == 0)
{
uint8_t v___x_1042_; 
lean_inc(v_a_1037_);
v___x_1042_ = l_Lean_Exception_isRuntime(v_a_1037_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
lean_del_object(v___x_1039_);
v___x_1043_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1044_ = l_Lean_MessageData_ofExpr(v_a_1034_);
v___x_1045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1043_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1045_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = l_Lean_Exception_toMessageData(v_a_1037_);
v___x_1049_ = l_Lean_indentD(v___x_1048_);
v___x_1050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1047_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1052_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_1053_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1053_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
else
{
lean_object* v___x_1063_; 
lean_dec(v_a_1034_);
if (v_isShared_1040_ == 0)
{
v___x_1063_ = v___x_1039_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1037_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
else
{
lean_object* v___x_1066_; 
lean_dec(v_a_1034_);
if (v_isShared_1040_ == 0)
{
v___x_1066_ = v___x_1039_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1037_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
}
}
v___jp_1069_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v___x_1077_ = lean_array_get_size(v_a_1076_);
v___x_1078_ = lean_unsigned_to_nat(0u);
v___x_1079_ = lean_nat_dec_eq(v___x_1077_, v___x_1078_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec_ref(v___y_1071_);
lean_dec_ref(v___x_1022_);
v___x_1080_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1081_ = l_Lean_MessageData_ofConstName(v___x_1006_, v___x_1079_);
v___x_1082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1080_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1082_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = lean_array_to_list(v_a_1076_);
v___x_1086_ = lean_box(0);
v___x_1087_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1085_, v___x_1086_);
v___x_1088_ = l_Lean_MessageData_ofList(v___x_1087_);
v___x_1089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1084_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1089_, v___y_1074_, v___y_1073_, v___y_1075_, v___y_1072_);
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1090_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1090_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
else
{
lean_dec_ref(v_a_1076_);
lean_dec(v___x_1006_);
v___y_1024_ = v___y_1070_;
v___y_1025_ = v___y_1071_;
v___y_1026_ = v___y_1074_;
v___y_1027_ = v___y_1073_;
v___y_1028_ = v___y_1075_;
v___y_1029_ = v___y_1072_;
goto v___jp_1023_;
}
}
v___jp_1102_:
{
lean_object* v___x_1109_; size_t v_sz_1110_; lean_object* v___x_1111_; 
v___x_1109_ = lean_box(0);
v_sz_1110_ = lean_array_size(v___x_1101_);
v___x_1111_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8(v___x_1101_, v_sz_1110_, v___x_1100_, v___x_1109_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
lean_dec_ref_known(v___x_1111_, 1);
v___x_1112_ = lean_unsigned_to_nat(0u);
v___x_1113_ = lean_array_get_size(v___x_1101_);
v___x_1114_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1115_ = lean_nat_dec_lt(v___x_1112_, v___x_1113_);
if (v___x_1115_ == 0)
{
lean_dec_ref(v___x_1101_);
v___y_1070_ = v___y_1103_;
v___y_1071_ = v___y_1104_;
v___y_1072_ = v___y_1108_;
v___y_1073_ = v___y_1106_;
v___y_1074_ = v___y_1105_;
v___y_1075_ = v___y_1107_;
v_a_1076_ = v___x_1114_;
goto v___jp_1069_;
}
else
{
size_t v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = lean_usize_of_nat(v___x_1113_);
v___x_1117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9(v___x_1101_, v___x_1100_, v___x_1116_, v___x_1114_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec_ref(v___x_1101_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
v___y_1070_ = v___y_1103_;
v___y_1071_ = v___y_1104_;
v___y_1072_ = v___y_1108_;
v___y_1073_ = v___y_1106_;
v___y_1074_ = v___y_1105_;
v___y_1075_ = v___y_1107_;
v_a_1076_ = v_a_1118_;
goto v___jp_1069_;
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec_ref(v___y_1104_);
lean_dec_ref(v___x_1022_);
lean_dec(v___x_1006_);
v_a_1119_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1117_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1117_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec_ref(v___y_1104_);
lean_dec_ref(v___x_1101_);
lean_dec_ref(v___x_1022_);
lean_dec(v___x_1006_);
v_a_1127_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1111_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1111_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
v___jp_1135_:
{
lean_object* v___x_1139_; 
lean_inc_ref(v_fst_1137_);
lean_inc_ref(v_e_1007_);
v___x_1139_ = l_Lean_Meta_isExprDefEq(v_e_1007_, v_fst_1137_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; uint8_t v___x_1141_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref_known(v___x_1139_, 1);
v___x_1141_ = lean_unbox(v_a_1140_);
lean_dec(v_a_1140_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_dec_ref(v_snd_1138_);
lean_dec_ref(v___x_1101_);
lean_dec_ref(v___x_1022_);
v___x_1142_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1143_ = l_Lean_MessageData_ofExpr(v_fst_1137_);
v___x_1144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1142_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1144_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___x_1147_ = l_Lean_MessageData_ofConstName(v___x_1006_, v___x_1008_);
v___x_1148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1146_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1148_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = l_Lean_MessageData_ofExpr(v_e_1007_);
v___x_1152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1150_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___x_1153_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
v___x_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1152_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1154_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1155_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1155_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
else
{
lean_dec_ref(v_fst_1137_);
lean_dec_ref(v_e_1007_);
v___y_1103_ = v_fst_1136_;
v___y_1104_ = v_snd_1138_;
v___y_1105_ = v___y_1011_;
v___y_1106_ = v___y_1012_;
v___y_1107_ = v___y_1013_;
v___y_1108_ = v___y_1014_;
goto v___jp_1102_;
}
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
lean_dec_ref(v_snd_1138_);
lean_dec_ref(v_fst_1137_);
lean_dec_ref(v___x_1101_);
lean_dec_ref(v___x_1022_);
lean_dec_ref(v_e_1007_);
lean_dec(v___x_1006_);
v_a_1164_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1139_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1139_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2___boxed(lean_object* v___x_1199_, lean_object* v___x_1200_, lean_object* v_fst_1201_, lean_object* v___x_1202_, lean_object* v_e_1203_, lean_object* v___x_1204_, lean_object* v_snd_1205_, lean_object* v_____r_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
uint8_t v___x_89881__boxed_1212_; uint8_t v___x_89885__boxed_1213_; lean_object* v_res_1214_; 
v___x_89881__boxed_1212_ = lean_unbox(v___x_1199_);
v___x_89885__boxed_1213_ = lean_unbox(v___x_1204_);
v_res_1214_ = l_Lean_Meta_rwMatcher___lam__2(v___x_89881__boxed_1212_, v___x_1200_, v_fst_1201_, v___x_1202_, v_e_1203_, v___x_89885__boxed_1213_, v_snd_1205_, v_____r_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec_ref(v_snd_1205_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3(uint8_t v___x_1215_, lean_object* v___x_1216_, lean_object* v_fst_1217_, lean_object* v___x_1218_, lean_object* v_e_1219_, uint8_t v___x_1220_, lean_object* v_snd_1221_, lean_object* v_____r_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v___y_1229_; lean_object* v_proof_1230_; lean_object* v___x_1234_; uint8_t v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; uint8_t v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v_a_1288_; size_t v_sz_1311_; size_t v___x_1312_; lean_object* v___x_1313_; uint8_t v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; uint8_t v_fst_1348_; lean_object* v_fst_1349_; lean_object* v_snd_1350_; lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1234_ = l_Lean_mkAppN(v___x_1216_, v_fst_1217_);
v_sz_1311_ = lean_array_size(v_fst_1217_);
v___x_1312_ = ((size_t)0ULL);
v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4(v_sz_1311_, v___x_1312_, v_fst_1217_);
v___x_1384_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1385_ = lean_unsigned_to_nat(4u);
v___x_1386_ = l_Lean_Expr_isAppOfArity(v_snd_1221_, v___x_1384_, v___x_1385_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; 
v___x_1387_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1388_ = lean_unsigned_to_nat(3u);
v___x_1389_ = l_Lean_Expr_isAppOfArity(v_snd_1221_, v___x_1387_, v___x_1388_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
lean_dec_ref(v___x_1313_);
lean_dec_ref(v___x_1234_);
lean_dec_ref(v_e_1219_);
v___x_1390_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1391_ = l_Lean_MessageData_ofConstName(v___x_1218_, v___x_1220_);
v___x_1392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1390_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
v___x_1393_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1392_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
v___x_1395_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1394_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1395_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1395_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
else
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1404_ = l_Lean_Expr_appFn_x21(v_snd_1221_);
v___x_1405_ = l_Lean_Expr_appArg_x21(v___x_1404_);
lean_dec_ref(v___x_1404_);
v___x_1406_ = l_Lean_Expr_appArg_x21(v_snd_1221_);
v_fst_1348_ = v___x_1220_;
v_fst_1349_ = v___x_1405_;
v_snd_1350_ = v___x_1406_;
goto v___jp_1347_;
}
}
else
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1407_ = l_Lean_Expr_appFn_x21(v_snd_1221_);
v___x_1408_ = l_Lean_Expr_appFn_x21(v___x_1407_);
lean_dec_ref(v___x_1407_);
v___x_1409_ = l_Lean_Expr_appArg_x21(v___x_1408_);
lean_dec_ref(v___x_1408_);
v___x_1410_ = l_Lean_Expr_appArg_x21(v_snd_1221_);
v_fst_1348_ = v___x_1215_;
v_fst_1349_ = v___x_1409_;
v_snd_1350_ = v___x_1410_;
goto v___jp_1347_;
}
v___jp_1228_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1231_, 0, v_proof_1230_);
v___x_1232_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1232_, 0, v___y_1229_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
lean_ctor_set_uint8(v___x_1232_, sizeof(void*)*2, v___x_1215_);
v___x_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
return v___x_1233_;
}
v___jp_1235_:
{
lean_object* v___x_1242_; lean_object* v_a_1243_; lean_object* v___x_1244_; 
v___x_1242_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___y_1237_, v___y_1239_);
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_a_1243_);
lean_dec_ref(v___x_1242_);
v___x_1244_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1234_, v___y_1239_);
if (v___y_1236_ == 0)
{
lean_object* v_a_1245_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref(v___x_1244_);
v___y_1229_ = v_a_1243_;
v_proof_1230_ = v_a_1245_;
goto v___jp_1228_;
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1247_; 
v_a_1246_ = lean_ctor_get(v___x_1244_, 0);
lean_inc_n(v_a_1246_, 2);
lean_dec_ref(v___x_1244_);
v___x_1247_ = l_Lean_Meta_mkEqOfHEq(v_a_1246_, v___x_1215_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; 
lean_dec(v_a_1246_);
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1248_);
lean_dec_ref_known(v___x_1247_, 1);
v___y_1229_ = v_a_1243_;
v_proof_1230_ = v_a_1248_;
goto v___jp_1228_;
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1280_; 
lean_dec(v_a_1243_);
v_a_1249_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1251_ = v___x_1247_;
v_isShared_1252_ = v_isSharedCheck_1280_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1247_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1280_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
uint8_t v___x_1253_; 
v___x_1253_ = l_Lean_Exception_isInterrupt(v_a_1249_);
if (v___x_1253_ == 0)
{
uint8_t v___x_1254_; 
lean_inc(v_a_1249_);
v___x_1254_ = l_Lean_Exception_isRuntime(v_a_1249_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_del_object(v___x_1251_);
v___x_1255_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1256_ = l_Lean_MessageData_ofExpr(v_a_1246_);
v___x_1257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1255_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v___x_1258_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1257_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
v___x_1260_ = l_Lean_Exception_toMessageData(v_a_1249_);
v___x_1261_ = l_Lean_indentD(v___x_1260_);
v___x_1262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1259_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1262_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
v___x_1265_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1264_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
else
{
lean_object* v___x_1275_; 
lean_dec(v_a_1246_);
if (v_isShared_1252_ == 0)
{
v___x_1275_ = v___x_1251_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1249_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
else
{
lean_object* v___x_1278_; 
lean_dec(v_a_1246_);
if (v_isShared_1252_ == 0)
{
v___x_1278_ = v___x_1251_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1249_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
}
}
v___jp_1281_:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v___x_1289_ = lean_array_get_size(v_a_1288_);
v___x_1290_ = lean_unsigned_to_nat(0u);
v___x_1291_ = lean_nat_dec_eq(v___x_1289_, v___x_1290_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_dec_ref(v___y_1287_);
lean_dec_ref(v___x_1234_);
v___x_1292_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1293_ = l_Lean_MessageData_ofConstName(v___x_1218_, v___x_1291_);
v___x_1294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1292_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
v___x_1295_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1294_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
v___x_1297_ = lean_array_to_list(v_a_1288_);
v___x_1298_ = lean_box(0);
v___x_1299_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1297_, v___x_1298_);
v___x_1300_ = l_Lean_MessageData_ofList(v___x_1299_);
v___x_1301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1296_);
lean_ctor_set(v___x_1301_, 1, v___x_1300_);
v___x_1302_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1301_, v___y_1285_, v___y_1283_, v___y_1284_, v___y_1286_);
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1302_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1302_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
else
{
lean_dec_ref(v_a_1288_);
lean_dec(v___x_1218_);
v___y_1236_ = v___y_1282_;
v___y_1237_ = v___y_1287_;
v___y_1238_ = v___y_1285_;
v___y_1239_ = v___y_1283_;
v___y_1240_ = v___y_1284_;
v___y_1241_ = v___y_1286_;
goto v___jp_1235_;
}
}
v___jp_1314_:
{
lean_object* v___x_1321_; size_t v_sz_1322_; lean_object* v___x_1323_; 
v___x_1321_ = lean_box(0);
v_sz_1322_ = lean_array_size(v___x_1313_);
v___x_1323_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8(v___x_1313_, v_sz_1322_, v___x_1312_, v___x_1321_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; 
lean_dec_ref_known(v___x_1323_, 1);
v___x_1324_ = lean_unsigned_to_nat(0u);
v___x_1325_ = lean_array_get_size(v___x_1313_);
v___x_1326_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1327_ = lean_nat_dec_lt(v___x_1324_, v___x_1325_);
if (v___x_1327_ == 0)
{
lean_dec_ref(v___x_1313_);
v___y_1282_ = v___y_1315_;
v___y_1283_ = v___y_1318_;
v___y_1284_ = v___y_1319_;
v___y_1285_ = v___y_1317_;
v___y_1286_ = v___y_1320_;
v___y_1287_ = v___y_1316_;
v_a_1288_ = v___x_1326_;
goto v___jp_1281_;
}
else
{
size_t v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = lean_usize_of_nat(v___x_1325_);
v___x_1329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9(v___x_1313_, v___x_1312_, v___x_1328_, v___x_1326_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
lean_dec_ref(v___x_1313_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_a_1330_);
lean_dec_ref_known(v___x_1329_, 1);
v___y_1282_ = v___y_1315_;
v___y_1283_ = v___y_1318_;
v___y_1284_ = v___y_1319_;
v___y_1285_ = v___y_1317_;
v___y_1286_ = v___y_1320_;
v___y_1287_ = v___y_1316_;
v_a_1288_ = v_a_1330_;
goto v___jp_1281_;
}
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
lean_dec_ref(v___y_1316_);
lean_dec_ref(v___x_1234_);
lean_dec(v___x_1218_);
v_a_1331_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1329_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1329_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
}
else
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
lean_dec_ref(v___y_1316_);
lean_dec_ref(v___x_1313_);
lean_dec_ref(v___x_1234_);
lean_dec(v___x_1218_);
v_a_1339_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1323_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1323_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
v___jp_1347_:
{
lean_object* v___x_1351_; 
lean_inc_ref(v_fst_1349_);
lean_inc_ref(v_e_1219_);
v___x_1351_ = l_Lean_Meta_isExprDefEq(v_e_1219_, v_fst_1349_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; uint8_t v___x_1353_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1352_);
lean_dec_ref_known(v___x_1351_, 1);
v___x_1353_ = lean_unbox(v_a_1352_);
lean_dec(v_a_1352_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec_ref(v_snd_1350_);
lean_dec_ref(v___x_1313_);
lean_dec_ref(v___x_1234_);
v___x_1354_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1355_ = l_Lean_MessageData_ofExpr(v_fst_1349_);
v___x_1356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1354_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___x_1357_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1356_);
lean_ctor_set(v___x_1358_, 1, v___x_1357_);
v___x_1359_ = l_Lean_MessageData_ofConstName(v___x_1218_, v___x_1220_);
v___x_1360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1358_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
v___x_1361_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1360_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
v___x_1363_ = l_Lean_MessageData_ofExpr(v_e_1219_);
v___x_1364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1362_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
v___x_1365_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
v___x_1366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1364_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
v___x_1367_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1366_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1367_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1367_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
else
{
lean_dec_ref(v_fst_1349_);
lean_dec_ref(v_e_1219_);
v___y_1315_ = v_fst_1348_;
v___y_1316_ = v_snd_1350_;
v___y_1317_ = v___y_1223_;
v___y_1318_ = v___y_1224_;
v___y_1319_ = v___y_1225_;
v___y_1320_ = v___y_1226_;
goto v___jp_1314_;
}
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_dec_ref(v_snd_1350_);
lean_dec_ref(v_fst_1349_);
lean_dec_ref(v___x_1313_);
lean_dec_ref(v___x_1234_);
lean_dec_ref(v_e_1219_);
lean_dec(v___x_1218_);
v_a_1376_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1351_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1351_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3___boxed(lean_object* v___x_1411_, lean_object* v___x_1412_, lean_object* v_fst_1413_, lean_object* v___x_1414_, lean_object* v_e_1415_, lean_object* v___x_1416_, lean_object* v_snd_1417_, lean_object* v_____r_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
uint8_t v___x_90363__boxed_1424_; uint8_t v___x_90367__boxed_1425_; lean_object* v_res_1426_; 
v___x_90363__boxed_1424_ = lean_unbox(v___x_1411_);
v___x_90367__boxed_1425_ = lean_unbox(v___x_1416_);
v_res_1426_ = l_Lean_Meta_rwMatcher___lam__3(v___x_90363__boxed_1424_, v___x_1412_, v_fst_1413_, v___x_1414_, v_e_1415_, v___x_90367__boxed_1425_, v_snd_1417_, v_____r_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec_ref(v_snd_1417_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4(uint8_t v___x_1427_, lean_object* v___x_1428_, lean_object* v_fst_1429_, lean_object* v___x_1430_, lean_object* v_e_1431_, uint8_t v___x_1432_, lean_object* v_snd_1433_, lean_object* v_____r_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v___y_1441_; lean_object* v_proof_1442_; lean_object* v___x_1446_; lean_object* v___y_1448_; uint8_t v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; uint8_t v___y_1499_; lean_object* v_a_1500_; size_t v_sz_1523_; size_t v___x_1524_; lean_object* v___x_1525_; lean_object* v___y_1527_; uint8_t v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; uint8_t v_fst_1560_; lean_object* v_fst_1561_; lean_object* v_snd_1562_; lean_object* v___x_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; 
v___x_1446_ = l_Lean_mkAppN(v___x_1428_, v_fst_1429_);
v_sz_1523_ = lean_array_size(v_fst_1429_);
v___x_1524_ = ((size_t)0ULL);
v___x_1525_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4(v_sz_1523_, v___x_1524_, v_fst_1429_);
v___x_1596_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1597_ = lean_unsigned_to_nat(4u);
v___x_1598_ = l_Lean_Expr_isAppOfArity(v_snd_1433_, v___x_1596_, v___x_1597_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; lean_object* v___x_1600_; uint8_t v___x_1601_; 
v___x_1599_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1600_ = lean_unsigned_to_nat(3u);
v___x_1601_ = l_Lean_Expr_isAppOfArity(v_snd_1433_, v___x_1599_, v___x_1600_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_dec_ref(v___x_1525_);
lean_dec_ref(v___x_1446_);
lean_dec_ref(v_e_1431_);
v___x_1602_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1603_ = l_Lean_MessageData_ofConstName(v___x_1430_, v___x_1432_);
v___x_1604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1602_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
v___x_1605_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1604_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v___x_1607_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1606_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1607_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1607_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
else
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1616_ = l_Lean_Expr_appFn_x21(v_snd_1433_);
v___x_1617_ = l_Lean_Expr_appArg_x21(v___x_1616_);
lean_dec_ref(v___x_1616_);
v___x_1618_ = l_Lean_Expr_appArg_x21(v_snd_1433_);
v_fst_1560_ = v___x_1432_;
v_fst_1561_ = v___x_1617_;
v_snd_1562_ = v___x_1618_;
goto v___jp_1559_;
}
}
else
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1619_ = l_Lean_Expr_appFn_x21(v_snd_1433_);
v___x_1620_ = l_Lean_Expr_appFn_x21(v___x_1619_);
lean_dec_ref(v___x_1619_);
v___x_1621_ = l_Lean_Expr_appArg_x21(v___x_1620_);
lean_dec_ref(v___x_1620_);
v___x_1622_ = l_Lean_Expr_appArg_x21(v_snd_1433_);
v_fst_1560_ = v___x_1427_;
v_fst_1561_ = v___x_1621_;
v_snd_1562_ = v___x_1622_;
goto v___jp_1559_;
}
v___jp_1440_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1443_, 0, v_proof_1442_);
v___x_1444_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1444_, 0, v___y_1441_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*2, v___x_1427_);
v___x_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
return v___x_1445_;
}
v___jp_1447_:
{
lean_object* v___x_1454_; lean_object* v_a_1455_; lean_object* v___x_1456_; 
v___x_1454_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___y_1448_, v___y_1451_);
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1455_);
lean_dec_ref(v___x_1454_);
v___x_1456_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1446_, v___y_1451_);
if (v___y_1449_ == 0)
{
lean_object* v_a_1457_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref(v___x_1456_);
v___y_1441_ = v_a_1455_;
v_proof_1442_ = v_a_1457_;
goto v___jp_1440_;
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1459_; 
v_a_1458_ = lean_ctor_get(v___x_1456_, 0);
lean_inc_n(v_a_1458_, 2);
lean_dec_ref(v___x_1456_);
v___x_1459_ = l_Lean_Meta_mkEqOfHEq(v_a_1458_, v___x_1427_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; 
lean_dec(v_a_1458_);
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1460_);
lean_dec_ref_known(v___x_1459_, 1);
v___y_1441_ = v_a_1455_;
v_proof_1442_ = v_a_1460_;
goto v___jp_1440_;
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1492_; 
lean_dec(v_a_1455_);
v_a_1461_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1463_ = v___x_1459_;
v_isShared_1464_ = v_isSharedCheck_1492_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1459_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1492_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
uint8_t v___x_1465_; 
v___x_1465_ = l_Lean_Exception_isInterrupt(v_a_1461_);
if (v___x_1465_ == 0)
{
uint8_t v___x_1466_; 
lean_inc(v_a_1461_);
v___x_1466_ = l_Lean_Exception_isRuntime(v_a_1461_);
if (v___x_1466_ == 0)
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
lean_del_object(v___x_1463_);
v___x_1467_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1468_ = l_Lean_MessageData_ofExpr(v_a_1458_);
v___x_1469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1467_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
v___x_1470_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1469_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = l_Lean_Exception_toMessageData(v_a_1461_);
v___x_1473_ = l_Lean_indentD(v___x_1472_);
v___x_1474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1471_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
v___x_1475_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1474_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
v___x_1477_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1476_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1477_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
else
{
lean_object* v___x_1487_; 
lean_dec(v_a_1458_);
if (v_isShared_1464_ == 0)
{
v___x_1487_ = v___x_1463_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1461_);
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
lean_object* v___x_1490_; 
lean_dec(v_a_1458_);
if (v_isShared_1464_ == 0)
{
v___x_1490_ = v___x_1463_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1461_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
}
}
v___jp_1493_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1501_ = lean_array_get_size(v_a_1500_);
v___x_1502_ = lean_unsigned_to_nat(0u);
v___x_1503_ = lean_nat_dec_eq(v___x_1501_, v___x_1502_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
lean_dec_ref(v___y_1495_);
lean_dec_ref(v___x_1446_);
v___x_1504_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1505_ = l_Lean_MessageData_ofConstName(v___x_1430_, v___x_1503_);
v___x_1506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1504_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
v___x_1507_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1506_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
v___x_1509_ = lean_array_to_list(v_a_1500_);
v___x_1510_ = lean_box(0);
v___x_1511_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1509_, v___x_1510_);
v___x_1512_ = l_Lean_MessageData_ofList(v___x_1511_);
v___x_1513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1508_);
lean_ctor_set(v___x_1513_, 1, v___x_1512_);
v___x_1514_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1513_, v___y_1497_, v___y_1494_, v___y_1496_, v___y_1498_);
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1514_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1514_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1518_ == 0)
{
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1515_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
else
{
lean_dec_ref(v_a_1500_);
lean_dec(v___x_1430_);
v___y_1448_ = v___y_1495_;
v___y_1449_ = v___y_1499_;
v___y_1450_ = v___y_1497_;
v___y_1451_ = v___y_1494_;
v___y_1452_ = v___y_1496_;
v___y_1453_ = v___y_1498_;
goto v___jp_1447_;
}
}
v___jp_1526_:
{
lean_object* v___x_1533_; size_t v_sz_1534_; lean_object* v___x_1535_; 
v___x_1533_ = lean_box(0);
v_sz_1534_ = lean_array_size(v___x_1525_);
v___x_1535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8(v___x_1525_, v_sz_1534_, v___x_1524_, v___x_1533_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; 
lean_dec_ref_known(v___x_1535_, 1);
v___x_1536_ = lean_unsigned_to_nat(0u);
v___x_1537_ = lean_array_get_size(v___x_1525_);
v___x_1538_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1539_ = lean_nat_dec_lt(v___x_1536_, v___x_1537_);
if (v___x_1539_ == 0)
{
lean_dec_ref(v___x_1525_);
v___y_1494_ = v___y_1530_;
v___y_1495_ = v___y_1527_;
v___y_1496_ = v___y_1531_;
v___y_1497_ = v___y_1529_;
v___y_1498_ = v___y_1532_;
v___y_1499_ = v___y_1528_;
v_a_1500_ = v___x_1538_;
goto v___jp_1493_;
}
else
{
size_t v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = lean_usize_of_nat(v___x_1537_);
v___x_1541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9(v___x_1525_, v___x_1524_, v___x_1540_, v___x_1538_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
lean_dec_ref(v___x_1525_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref_known(v___x_1541_, 1);
v___y_1494_ = v___y_1530_;
v___y_1495_ = v___y_1527_;
v___y_1496_ = v___y_1531_;
v___y_1497_ = v___y_1529_;
v___y_1498_ = v___y_1532_;
v___y_1499_ = v___y_1528_;
v_a_1500_ = v_a_1542_;
goto v___jp_1493_;
}
else
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
lean_dec_ref(v___y_1527_);
lean_dec_ref(v___x_1446_);
lean_dec(v___x_1430_);
v_a_1543_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1541_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1541_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
lean_dec_ref(v___y_1527_);
lean_dec_ref(v___x_1525_);
lean_dec_ref(v___x_1446_);
lean_dec(v___x_1430_);
v_a_1551_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1535_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1535_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1551_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
v___jp_1559_:
{
lean_object* v___x_1563_; 
lean_inc_ref(v_fst_1561_);
lean_inc_ref(v_e_1431_);
v___x_1563_ = l_Lean_Meta_isExprDefEq(v_e_1431_, v_fst_1561_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; uint8_t v___x_1565_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1563_, 1);
v___x_1565_ = lean_unbox(v_a_1564_);
lean_dec(v_a_1564_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec_ref(v_snd_1562_);
lean_dec_ref(v___x_1525_);
lean_dec_ref(v___x_1446_);
v___x_1566_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1567_ = l_Lean_MessageData_ofExpr(v_fst_1561_);
v___x_1568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1566_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
v___x_1569_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1568_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
v___x_1571_ = l_Lean_MessageData_ofConstName(v___x_1430_, v___x_1432_);
v___x_1572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1570_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
v___x_1573_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1572_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
v___x_1575_ = l_Lean_MessageData_ofExpr(v_e_1431_);
v___x_1576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1574_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
v___x_1578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1576_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1578_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1579_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
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
else
{
lean_dec_ref(v_fst_1561_);
lean_dec_ref(v_e_1431_);
v___y_1527_ = v_snd_1562_;
v___y_1528_ = v_fst_1560_;
v___y_1529_ = v___y_1435_;
v___y_1530_ = v___y_1436_;
v___y_1531_ = v___y_1437_;
v___y_1532_ = v___y_1438_;
goto v___jp_1526_;
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_dec_ref(v_snd_1562_);
lean_dec_ref(v_fst_1561_);
lean_dec_ref(v___x_1525_);
lean_dec_ref(v___x_1446_);
lean_dec_ref(v_e_1431_);
lean_dec(v___x_1430_);
v_a_1588_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1563_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1563_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4___boxed(lean_object* v___x_1623_, lean_object* v___x_1624_, lean_object* v_fst_1625_, lean_object* v___x_1626_, lean_object* v_e_1627_, lean_object* v___x_1628_, lean_object* v_snd_1629_, lean_object* v_____r_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
uint8_t v___x_90820__boxed_1636_; uint8_t v___x_90824__boxed_1637_; lean_object* v_res_1638_; 
v___x_90820__boxed_1636_ = lean_unbox(v___x_1623_);
v___x_90824__boxed_1637_ = lean_unbox(v___x_1628_);
v_res_1638_ = l_Lean_Meta_rwMatcher___lam__4(v___x_90820__boxed_1636_, v___x_1624_, v_fst_1625_, v___x_1626_, v_e_1627_, v___x_90824__boxed_1637_, v_snd_1629_, v_____r_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec_ref(v_snd_1629_);
return v_res_1638_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1639_; double v___x_1640_; 
v___x_1639_ = lean_unsigned_to_nat(0u);
v___x_1640_ = lean_float_of_nat(v___x_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(lean_object* v_cls_1644_, lean_object* v_msg_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_ref_1651_; lean_object* v___x_1652_; lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1698_; 
v_ref_1651_ = lean_ctor_get(v___y_1648_, 2);
v___x_1652_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3_spec__4(v_msg_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1655_ = v___x_1652_;
v_isShared_1656_ = v_isSharedCheck_1698_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1652_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1698_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1657_; lean_object* v_traceState_1658_; lean_object* v_env_1659_; lean_object* v_nextMacroScope_1660_; lean_object* v_ngen_1661_; lean_object* v_auxDeclNGen_1662_; lean_object* v_cache_1663_; lean_object* v_recordedDeps_1664_; lean_object* v_messages_1665_; lean_object* v_infoState_1666_; lean_object* v_snapshotTasks_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1697_; 
v___x_1657_ = lean_st_ref_take(v___y_1649_);
v_traceState_1658_ = lean_ctor_get(v___x_1657_, 4);
v_env_1659_ = lean_ctor_get(v___x_1657_, 0);
v_nextMacroScope_1660_ = lean_ctor_get(v___x_1657_, 1);
v_ngen_1661_ = lean_ctor_get(v___x_1657_, 2);
v_auxDeclNGen_1662_ = lean_ctor_get(v___x_1657_, 3);
v_cache_1663_ = lean_ctor_get(v___x_1657_, 5);
v_recordedDeps_1664_ = lean_ctor_get(v___x_1657_, 6);
v_messages_1665_ = lean_ctor_get(v___x_1657_, 7);
v_infoState_1666_ = lean_ctor_get(v___x_1657_, 8);
v_snapshotTasks_1667_ = lean_ctor_get(v___x_1657_, 9);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1669_ = v___x_1657_;
v_isShared_1670_ = v_isSharedCheck_1697_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_snapshotTasks_1667_);
lean_inc(v_infoState_1666_);
lean_inc(v_messages_1665_);
lean_inc(v_recordedDeps_1664_);
lean_inc(v_cache_1663_);
lean_inc(v_traceState_1658_);
lean_inc(v_auxDeclNGen_1662_);
lean_inc(v_ngen_1661_);
lean_inc(v_nextMacroScope_1660_);
lean_inc(v_env_1659_);
lean_dec(v___x_1657_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1697_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
uint64_t v_tid_1671_; lean_object* v_traces_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1696_; 
v_tid_1671_ = lean_ctor_get_uint64(v_traceState_1658_, sizeof(void*)*1);
v_traces_1672_ = lean_ctor_get(v_traceState_1658_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_traceState_1658_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1674_ = v_traceState_1658_;
v_isShared_1675_ = v_isSharedCheck_1696_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_traces_1672_);
lean_dec(v_traceState_1658_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1696_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; double v___x_1678_; uint8_t v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1687_; 
v___x_1676_ = lean_box(0);
v___x_1677_ = lean_box(0);
v___x_1678_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0);
v___x_1679_ = 0;
v___x_1680_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__1));
v___x_1681_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1681_, 0, v_cls_1644_);
lean_ctor_set(v___x_1681_, 1, v___x_1677_);
lean_ctor_set(v___x_1681_, 2, v___x_1680_);
lean_ctor_set_float(v___x_1681_, sizeof(void*)*3, v___x_1678_);
lean_ctor_set_float(v___x_1681_, sizeof(void*)*3 + 8, v___x_1678_);
lean_ctor_set_uint8(v___x_1681_, sizeof(void*)*3 + 16, v___x_1679_);
v___x_1682_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__2));
v___x_1683_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1681_);
lean_ctor_set(v___x_1683_, 1, v_a_1653_);
lean_ctor_set(v___x_1683_, 2, v___x_1682_);
lean_inc(v_ref_1651_);
v___x_1684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1684_, 0, v_ref_1651_);
lean_ctor_set(v___x_1684_, 1, v___x_1683_);
v___x_1685_ = l_Lean_PersistentArray_push___redArg(v_traces_1672_, v___x_1684_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 0, v___x_1685_);
v___x_1687_ = v___x_1674_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1685_);
lean_ctor_set_uint64(v_reuseFailAlloc_1695_, sizeof(void*)*1, v_tid_1671_);
v___x_1687_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1689_; 
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 4, v___x_1687_);
v___x_1689_ = v___x_1669_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_env_1659_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v_nextMacroScope_1660_);
lean_ctor_set(v_reuseFailAlloc_1694_, 2, v_ngen_1661_);
lean_ctor_set(v_reuseFailAlloc_1694_, 3, v_auxDeclNGen_1662_);
lean_ctor_set(v_reuseFailAlloc_1694_, 4, v___x_1687_);
lean_ctor_set(v_reuseFailAlloc_1694_, 5, v_cache_1663_);
lean_ctor_set(v_reuseFailAlloc_1694_, 6, v_recordedDeps_1664_);
lean_ctor_set(v_reuseFailAlloc_1694_, 7, v_messages_1665_);
lean_ctor_set(v_reuseFailAlloc_1694_, 8, v_infoState_1666_);
lean_ctor_set(v_reuseFailAlloc_1694_, 9, v_snapshotTasks_1667_);
v___x_1689_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1690_ = lean_st_ref_put(v___y_1649_, v___x_1689_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1676_);
v___x_1692_ = v___x_1655_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1676_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___boxed(lean_object* v_cls_1699_, lean_object* v_msg_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(v_cls_1699_, v_msg_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__17(lean_object* v_opts_1707_, lean_object* v_opt_1708_){
_start:
{
lean_object* v_name_1709_; lean_object* v_defValue_1710_; lean_object* v_map_1711_; lean_object* v___x_1712_; 
v_name_1709_ = lean_ctor_get(v_opt_1708_, 0);
v_defValue_1710_ = lean_ctor_get(v_opt_1708_, 1);
v_map_1711_ = lean_ctor_get(v_opts_1707_, 0);
v___x_1712_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1711_, v_name_1709_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_inc(v_defValue_1710_);
return v_defValue_1710_;
}
else
{
lean_object* v_val_1713_; 
v_val_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_val_1713_);
lean_dec_ref_known(v___x_1712_, 1);
if (lean_obj_tag(v_val_1713_) == 3)
{
lean_object* v_v_1714_; 
v_v_1714_ = lean_ctor_get(v_val_1713_, 0);
lean_inc(v_v_1714_);
lean_dec_ref_known(v_val_1713_, 1);
return v_v_1714_;
}
else
{
lean_dec(v_val_1713_);
lean_inc(v_defValue_1710_);
return v_defValue_1710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__17___boxed(lean_object* v_opts_1715_, lean_object* v_opt_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__17(v_opts_1715_, v_opt_1716_);
lean_dec_ref(v_opt_1716_);
lean_dec_ref(v_opts_1715_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___redArg(lean_object* v_x_1718_){
_start:
{
if (lean_obj_tag(v_x_1718_) == 0)
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
v_a_1720_ = lean_ctor_get(v_x_1718_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_x_1718_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1722_ = v_x_1718_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v_x_1718_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
lean_ctor_set_tag(v___x_1722_, 1);
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1720_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
v_a_1728_ = lean_ctor_get(v_x_1718_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v_x_1718_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v_x_1718_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v_x_1718_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
lean_ctor_set_tag(v___x_1730_, 0);
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 1, 0);
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
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___redArg___boxed(lean_object* v_x_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___redArg(v_x_1736_);
return v_res_1738_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16(lean_object* v_e_1739_){
_start:
{
if (lean_obj_tag(v_e_1739_) == 0)
{
uint8_t v___x_1740_; 
v___x_1740_ = 2;
return v___x_1740_;
}
else
{
uint8_t v___x_1741_; 
v___x_1741_ = 0;
return v___x_1741_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16___boxed(lean_object* v_e_1742_){
_start:
{
uint8_t v_res_1743_; lean_object* v_r_1744_; 
v_res_1743_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16(v_e_1742_);
lean_dec_ref(v_e_1742_);
v_r_1744_ = lean_box(v_res_1743_);
return v_r_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14_spec__16(size_t v_sz_1745_, size_t v_i_1746_, lean_object* v_bs_1747_){
_start:
{
uint8_t v___x_1748_; 
v___x_1748_ = lean_usize_dec_lt(v_i_1746_, v_sz_1745_);
if (v___x_1748_ == 0)
{
return v_bs_1747_;
}
else
{
lean_object* v_v_1749_; lean_object* v_msg_1750_; lean_object* v___x_1751_; lean_object* v_bs_x27_1752_; size_t v___x_1753_; size_t v___x_1754_; lean_object* v___x_1755_; 
v_v_1749_ = lean_array_uget_borrowed(v_bs_1747_, v_i_1746_);
v_msg_1750_ = lean_ctor_get(v_v_1749_, 1);
lean_inc_ref(v_msg_1750_);
v___x_1751_ = lean_unsigned_to_nat(0u);
v_bs_x27_1752_ = lean_array_uset(v_bs_1747_, v_i_1746_, v___x_1751_);
v___x_1753_ = ((size_t)1ULL);
v___x_1754_ = lean_usize_add(v_i_1746_, v___x_1753_);
v___x_1755_ = lean_array_uset(v_bs_x27_1752_, v_i_1746_, v_msg_1750_);
v_i_1746_ = v___x_1754_;
v_bs_1747_ = v___x_1755_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14_spec__16___boxed(lean_object* v_sz_1757_, lean_object* v_i_1758_, lean_object* v_bs_1759_){
_start:
{
size_t v_sz_boxed_1760_; size_t v_i_boxed_1761_; lean_object* v_res_1762_; 
v_sz_boxed_1760_ = lean_unbox_usize(v_sz_1757_);
lean_dec(v_sz_1757_);
v_i_boxed_1761_ = lean_unbox_usize(v_i_1758_);
lean_dec(v_i_1758_);
v_res_1762_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14_spec__16(v_sz_boxed_1760_, v_i_boxed_1761_, v_bs_1759_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14(lean_object* v_oldTraces_1763_, lean_object* v_data_1764_, lean_object* v_ref_1765_, lean_object* v_msg_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v_toCold_1772_; lean_object* v_currRecDepth_1773_; lean_object* v_ref_1774_; uint16_t v_optionFlags_1775_; uint8_t v_suppressElabErrors_1776_; uint8_t v_checkDeprecated_1777_; uint8_t v_isRecordingDeps_1778_; lean_object* v_ref_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v_traceState_1782_; lean_object* v_traces_1783_; lean_object* v___x_1784_; size_t v_sz_1785_; size_t v___x_1786_; lean_object* v___x_1787_; lean_object* v_msg_1788_; lean_object* v___x_1789_; lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1828_; 
v_toCold_1772_ = lean_ctor_get(v___y_1769_, 0);
v_currRecDepth_1773_ = lean_ctor_get(v___y_1769_, 1);
v_ref_1774_ = lean_ctor_get(v___y_1769_, 2);
v_optionFlags_1775_ = lean_ctor_get_uint16(v___y_1769_, sizeof(void*)*3);
v_suppressElabErrors_1776_ = lean_ctor_get_uint8(v___y_1769_, sizeof(void*)*3 + 2);
v_checkDeprecated_1777_ = lean_ctor_get_uint8(v___y_1769_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1778_ = lean_ctor_get_uint8(v___y_1769_, sizeof(void*)*3 + 4);
v_ref_1779_ = l_Lean_replaceRef(v_ref_1765_, v_ref_1774_);
lean_inc(v_currRecDepth_1773_);
lean_inc_ref(v_toCold_1772_);
v___x_1780_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1780_, 0, v_toCold_1772_);
lean_ctor_set(v___x_1780_, 1, v_currRecDepth_1773_);
lean_ctor_set(v___x_1780_, 2, v_ref_1779_);
lean_ctor_set_uint16(v___x_1780_, sizeof(void*)*3, v_optionFlags_1775_);
lean_ctor_set_uint8(v___x_1780_, sizeof(void*)*3 + 2, v_suppressElabErrors_1776_);
lean_ctor_set_uint8(v___x_1780_, sizeof(void*)*3 + 3, v_checkDeprecated_1777_);
lean_ctor_set_uint8(v___x_1780_, sizeof(void*)*3 + 4, v_isRecordingDeps_1778_);
v___x_1781_ = lean_st_ref_get(v___y_1770_);
v_traceState_1782_ = lean_ctor_get(v___x_1781_, 4);
lean_inc_ref(v_traceState_1782_);
lean_dec(v___x_1781_);
v_traces_1783_ = lean_ctor_get(v_traceState_1782_, 0);
lean_inc_ref(v_traces_1783_);
lean_dec_ref(v_traceState_1782_);
v___x_1784_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1783_);
lean_dec_ref(v_traces_1783_);
v_sz_1785_ = lean_array_size(v___x_1784_);
v___x_1786_ = ((size_t)0ULL);
v___x_1787_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14_spec__16(v_sz_1785_, v___x_1786_, v___x_1784_);
v_msg_1788_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1788_, 0, v_data_1764_);
lean_ctor_set(v_msg_1788_, 1, v_msg_1766_);
lean_ctor_set(v_msg_1788_, 2, v___x_1787_);
v___x_1789_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3_spec__4(v_msg_1788_, v___y_1767_, v___y_1768_, v___x_1780_, v___y_1770_);
lean_dec_ref_known(v___x_1780_, 3);
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1792_ = v___x_1789_;
v_isShared_1793_ = v_isSharedCheck_1828_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1789_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1828_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1794_; lean_object* v_traceState_1795_; lean_object* v_env_1796_; lean_object* v_nextMacroScope_1797_; lean_object* v_ngen_1798_; lean_object* v_auxDeclNGen_1799_; lean_object* v_cache_1800_; lean_object* v_recordedDeps_1801_; lean_object* v_messages_1802_; lean_object* v_infoState_1803_; lean_object* v_snapshotTasks_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1827_; 
v___x_1794_ = lean_st_ref_take(v___y_1770_);
v_traceState_1795_ = lean_ctor_get(v___x_1794_, 4);
v_env_1796_ = lean_ctor_get(v___x_1794_, 0);
v_nextMacroScope_1797_ = lean_ctor_get(v___x_1794_, 1);
v_ngen_1798_ = lean_ctor_get(v___x_1794_, 2);
v_auxDeclNGen_1799_ = lean_ctor_get(v___x_1794_, 3);
v_cache_1800_ = lean_ctor_get(v___x_1794_, 5);
v_recordedDeps_1801_ = lean_ctor_get(v___x_1794_, 6);
v_messages_1802_ = lean_ctor_get(v___x_1794_, 7);
v_infoState_1803_ = lean_ctor_get(v___x_1794_, 8);
v_snapshotTasks_1804_ = lean_ctor_get(v___x_1794_, 9);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1806_ = v___x_1794_;
v_isShared_1807_ = v_isSharedCheck_1827_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_snapshotTasks_1804_);
lean_inc(v_infoState_1803_);
lean_inc(v_messages_1802_);
lean_inc(v_recordedDeps_1801_);
lean_inc(v_cache_1800_);
lean_inc(v_traceState_1795_);
lean_inc(v_auxDeclNGen_1799_);
lean_inc(v_ngen_1798_);
lean_inc(v_nextMacroScope_1797_);
lean_inc(v_env_1796_);
lean_dec(v___x_1794_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1827_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
uint64_t v_tid_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1825_; 
v_tid_1808_ = lean_ctor_get_uint64(v_traceState_1795_, sizeof(void*)*1);
v_isSharedCheck_1825_ = !lean_is_exclusive(v_traceState_1795_);
if (v_isSharedCheck_1825_ == 0)
{
lean_object* v_unused_1826_; 
v_unused_1826_ = lean_ctor_get(v_traceState_1795_, 0);
lean_dec(v_unused_1826_);
v___x_1810_ = v_traceState_1795_;
v_isShared_1811_ = v_isSharedCheck_1825_;
goto v_resetjp_1809_;
}
else
{
lean_dec(v_traceState_1795_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1825_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1812_ = lean_box(0);
v___x_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1813_, 0, v_ref_1765_);
lean_ctor_set(v___x_1813_, 1, v_a_1790_);
v___x_1814_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1763_, v___x_1813_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 0, v___x_1814_);
v___x_1816_ = v___x_1810_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1814_);
lean_ctor_set_uint64(v_reuseFailAlloc_1824_, sizeof(void*)*1, v_tid_1808_);
v___x_1816_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
lean_object* v___x_1818_; 
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 4, v___x_1816_);
v___x_1818_ = v___x_1806_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_env_1796_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_nextMacroScope_1797_);
lean_ctor_set(v_reuseFailAlloc_1823_, 2, v_ngen_1798_);
lean_ctor_set(v_reuseFailAlloc_1823_, 3, v_auxDeclNGen_1799_);
lean_ctor_set(v_reuseFailAlloc_1823_, 4, v___x_1816_);
lean_ctor_set(v_reuseFailAlloc_1823_, 5, v_cache_1800_);
lean_ctor_set(v_reuseFailAlloc_1823_, 6, v_recordedDeps_1801_);
lean_ctor_set(v_reuseFailAlloc_1823_, 7, v_messages_1802_);
lean_ctor_set(v_reuseFailAlloc_1823_, 8, v_infoState_1803_);
lean_ctor_set(v_reuseFailAlloc_1823_, 9, v_snapshotTasks_1804_);
v___x_1818_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1819_ = lean_st_ref_put(v___y_1770_, v___x_1818_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 0, v___x_1812_);
v___x_1821_ = v___x_1792_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1812_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14___boxed(lean_object* v_oldTraces_1829_, lean_object* v_data_1830_, lean_object* v_ref_1831_, lean_object* v_msg_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14(v_oldTraces_1829_, v_data_1830_, v_ref_1831_, v_msg_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
return v_res_1838_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__1(void){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__0));
v___x_1841_ = l_Lean_stringToMessageData(v___x_1840_);
return v___x_1841_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__2(void){
_start:
{
lean_object* v___x_1842_; double v___x_1843_; 
v___x_1842_ = lean_unsigned_to_nat(1000u);
v___x_1843_ = lean_float_of_nat(v___x_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12(lean_object* v_cls_1844_, uint8_t v_collapsed_1845_, lean_object* v_tag_1846_, lean_object* v_opts_1847_, uint8_t v_clsEnabled_1848_, lean_object* v_oldTraces_1849_, lean_object* v_msg_1850_, lean_object* v_resStartStop_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v_fst_1857_; lean_object* v_snd_1858_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v_data_1862_; lean_object* v_fst_1873_; lean_object* v_snd_1874_; lean_object* v___x_1875_; uint8_t v___x_1876_; lean_object* v___y_1878_; lean_object* v_a_1879_; uint8_t v___y_1894_; double v___y_1926_; 
v_fst_1857_ = lean_ctor_get(v_resStartStop_1851_, 0);
lean_inc(v_fst_1857_);
v_snd_1858_ = lean_ctor_get(v_resStartStop_1851_, 1);
lean_inc(v_snd_1858_);
lean_dec_ref(v_resStartStop_1851_);
v_fst_1873_ = lean_ctor_get(v_snd_1858_, 0);
lean_inc(v_fst_1873_);
v_snd_1874_ = lean_ctor_get(v_snd_1858_, 1);
lean_inc(v_snd_1874_);
lean_dec(v_snd_1858_);
v___x_1875_ = l_Lean_trace_profiler;
v___x_1876_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11(v_opts_1847_, v___x_1875_);
if (v___x_1876_ == 0)
{
v___y_1894_ = v___x_1876_;
goto v___jp_1893_;
}
else
{
lean_object* v___x_1931_; uint8_t v___x_1932_; 
v___x_1931_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1932_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11(v_opts_1847_, v___x_1931_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1933_; lean_object* v___x_1934_; double v___x_1935_; double v___x_1936_; double v___x_1937_; 
v___x_1933_ = l_Lean_trace_profiler_threshold;
v___x_1934_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__17(v_opts_1847_, v___x_1933_);
v___x_1935_ = lean_float_of_nat(v___x_1934_);
v___x_1936_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__2);
v___x_1937_ = lean_float_div(v___x_1935_, v___x_1936_);
v___y_1926_ = v___x_1937_;
goto v___jp_1925_;
}
else
{
lean_object* v___x_1938_; lean_object* v___x_1939_; double v___x_1940_; 
v___x_1938_ = l_Lean_trace_profiler_threshold;
v___x_1939_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__17(v_opts_1847_, v___x_1938_);
v___x_1940_ = lean_float_of_nat(v___x_1939_);
v___y_1926_ = v___x_1940_;
goto v___jp_1925_;
}
}
v___jp_1859_:
{
lean_object* v___x_1863_; 
lean_inc(v___y_1861_);
v___x_1863_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14(v_oldTraces_1849_, v_data_1862_, v___y_1861_, v___y_1860_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v___x_1864_; 
lean_dec_ref_known(v___x_1863_, 1);
v___x_1864_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___redArg(v_fst_1857_);
return v___x_1864_;
}
else
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
lean_dec(v_fst_1857_);
v_a_1865_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1863_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1863_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1865_);
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
v___jp_1877_:
{
uint8_t v_result_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; double v___x_1883_; lean_object* v_data_1884_; 
v_result_1880_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16(v_fst_1857_);
v___x_1881_ = lean_box(v_result_1880_);
v___x_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
v___x_1883_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0);
lean_inc_ref(v_tag_1846_);
lean_inc_ref(v___x_1882_);
lean_inc(v_cls_1844_);
v_data_1884_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1884_, 0, v_cls_1844_);
lean_ctor_set(v_data_1884_, 1, v___x_1882_);
lean_ctor_set(v_data_1884_, 2, v_tag_1846_);
lean_ctor_set_float(v_data_1884_, sizeof(void*)*3, v___x_1883_);
lean_ctor_set_float(v_data_1884_, sizeof(void*)*3 + 8, v___x_1883_);
lean_ctor_set_uint8(v_data_1884_, sizeof(void*)*3 + 16, v_collapsed_1845_);
if (v___x_1876_ == 0)
{
lean_dec_ref_known(v___x_1882_, 1);
lean_dec(v_snd_1874_);
lean_dec(v_fst_1873_);
lean_dec_ref(v_tag_1846_);
lean_dec(v_cls_1844_);
v___y_1860_ = v_a_1879_;
v___y_1861_ = v___y_1878_;
v_data_1862_ = v_data_1884_;
goto v___jp_1859_;
}
else
{
lean_object* v_data_1885_; double v___x_1886_; double v___x_1887_; 
lean_dec_ref_known(v_data_1884_, 3);
v_data_1885_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1885_, 0, v_cls_1844_);
lean_ctor_set(v_data_1885_, 1, v___x_1882_);
lean_ctor_set(v_data_1885_, 2, v_tag_1846_);
v___x_1886_ = lean_unbox_float(v_fst_1873_);
lean_dec(v_fst_1873_);
lean_ctor_set_float(v_data_1885_, sizeof(void*)*3, v___x_1886_);
v___x_1887_ = lean_unbox_float(v_snd_1874_);
lean_dec(v_snd_1874_);
lean_ctor_set_float(v_data_1885_, sizeof(void*)*3 + 8, v___x_1887_);
lean_ctor_set_uint8(v_data_1885_, sizeof(void*)*3 + 16, v_collapsed_1845_);
v___y_1860_ = v_a_1879_;
v___y_1861_ = v___y_1878_;
v_data_1862_ = v_data_1885_;
goto v___jp_1859_;
}
}
v___jp_1888_:
{
lean_object* v_ref_1889_; lean_object* v___x_1890_; 
v_ref_1889_ = lean_ctor_get(v___y_1854_, 2);
lean_inc(v___y_1855_);
lean_inc_ref(v___y_1854_);
lean_inc(v___y_1853_);
lean_inc_ref(v___y_1852_);
lean_inc(v_fst_1857_);
v___x_1890_ = lean_apply_6(v_msg_1850_, v_fst_1857_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, lean_box(0));
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
lean_inc(v_a_1891_);
lean_dec_ref_known(v___x_1890_, 1);
v___y_1878_ = v_ref_1889_;
v_a_1879_ = v_a_1891_;
goto v___jp_1877_;
}
else
{
lean_object* v___x_1892_; 
lean_dec_ref_known(v___x_1890_, 1);
v___x_1892_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__1);
v___y_1878_ = v_ref_1889_;
v_a_1879_ = v___x_1892_;
goto v___jp_1877_;
}
}
v___jp_1893_:
{
if (v_clsEnabled_1848_ == 0)
{
if (v___y_1894_ == 0)
{
lean_object* v___x_1895_; lean_object* v_traceState_1896_; lean_object* v_env_1897_; lean_object* v_nextMacroScope_1898_; lean_object* v_ngen_1899_; lean_object* v_auxDeclNGen_1900_; lean_object* v_cache_1901_; lean_object* v_recordedDeps_1902_; lean_object* v_messages_1903_; lean_object* v_infoState_1904_; lean_object* v_snapshotTasks_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v_snd_1874_);
lean_dec(v_fst_1873_);
lean_dec_ref(v_msg_1850_);
lean_dec_ref(v_tag_1846_);
lean_dec(v_cls_1844_);
v___x_1895_ = lean_st_ref_take(v___y_1855_);
v_traceState_1896_ = lean_ctor_get(v___x_1895_, 4);
v_env_1897_ = lean_ctor_get(v___x_1895_, 0);
v_nextMacroScope_1898_ = lean_ctor_get(v___x_1895_, 1);
v_ngen_1899_ = lean_ctor_get(v___x_1895_, 2);
v_auxDeclNGen_1900_ = lean_ctor_get(v___x_1895_, 3);
v_cache_1901_ = lean_ctor_get(v___x_1895_, 5);
v_recordedDeps_1902_ = lean_ctor_get(v___x_1895_, 6);
v_messages_1903_ = lean_ctor_get(v___x_1895_, 7);
v_infoState_1904_ = lean_ctor_get(v___x_1895_, 8);
v_snapshotTasks_1905_ = lean_ctor_get(v___x_1895_, 9);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1907_ = v___x_1895_;
v_isShared_1908_ = v_isSharedCheck_1924_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_snapshotTasks_1905_);
lean_inc(v_infoState_1904_);
lean_inc(v_messages_1903_);
lean_inc(v_recordedDeps_1902_);
lean_inc(v_cache_1901_);
lean_inc(v_traceState_1896_);
lean_inc(v_auxDeclNGen_1900_);
lean_inc(v_ngen_1899_);
lean_inc(v_nextMacroScope_1898_);
lean_inc(v_env_1897_);
lean_dec(v___x_1895_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1924_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
uint64_t v_tid_1909_; lean_object* v_traces_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1923_; 
v_tid_1909_ = lean_ctor_get_uint64(v_traceState_1896_, sizeof(void*)*1);
v_traces_1910_ = lean_ctor_get(v_traceState_1896_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v_traceState_1896_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1912_ = v_traceState_1896_;
v_isShared_1913_ = v_isSharedCheck_1923_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_traces_1910_);
lean_dec(v_traceState_1896_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1923_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1914_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1849_, v_traces_1910_);
lean_dec_ref(v_traces_1910_);
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 0, v___x_1914_);
v___x_1916_ = v___x_1912_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1914_);
lean_ctor_set_uint64(v_reuseFailAlloc_1922_, sizeof(void*)*1, v_tid_1909_);
v___x_1916_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1918_; 
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 4, v___x_1916_);
v___x_1918_ = v___x_1907_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_env_1897_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v_nextMacroScope_1898_);
lean_ctor_set(v_reuseFailAlloc_1921_, 2, v_ngen_1899_);
lean_ctor_set(v_reuseFailAlloc_1921_, 3, v_auxDeclNGen_1900_);
lean_ctor_set(v_reuseFailAlloc_1921_, 4, v___x_1916_);
lean_ctor_set(v_reuseFailAlloc_1921_, 5, v_cache_1901_);
lean_ctor_set(v_reuseFailAlloc_1921_, 6, v_recordedDeps_1902_);
lean_ctor_set(v_reuseFailAlloc_1921_, 7, v_messages_1903_);
lean_ctor_set(v_reuseFailAlloc_1921_, 8, v_infoState_1904_);
lean_ctor_set(v_reuseFailAlloc_1921_, 9, v_snapshotTasks_1905_);
v___x_1918_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = lean_st_ref_put(v___y_1855_, v___x_1918_);
v___x_1920_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___redArg(v_fst_1857_);
return v___x_1920_;
}
}
}
}
}
else
{
goto v___jp_1888_;
}
}
else
{
goto v___jp_1888_;
}
}
v___jp_1925_:
{
double v___x_1927_; double v___x_1928_; double v___x_1929_; uint8_t v___x_1930_; 
v___x_1927_ = lean_unbox_float(v_snd_1874_);
v___x_1928_ = lean_unbox_float(v_fst_1873_);
v___x_1929_ = lean_float_sub(v___x_1927_, v___x_1928_);
v___x_1930_ = lean_float_decLt(v___y_1926_, v___x_1929_);
v___y_1894_ = v___x_1930_;
goto v___jp_1893_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___boxed(lean_object* v_cls_1941_, lean_object* v_collapsed_1942_, lean_object* v_tag_1943_, lean_object* v_opts_1944_, lean_object* v_clsEnabled_1945_, lean_object* v_oldTraces_1946_, lean_object* v_msg_1947_, lean_object* v_resStartStop_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
uint8_t v_collapsed_boxed_1954_; uint8_t v_clsEnabled_boxed_1955_; lean_object* v_res_1956_; 
v_collapsed_boxed_1954_ = lean_unbox(v_collapsed_1942_);
v_clsEnabled_boxed_1955_ = lean_unbox(v_clsEnabled_1945_);
v_res_1956_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12(v_cls_1941_, v_collapsed_boxed_1954_, v_tag_1943_, v_opts_1944_, v_clsEnabled_boxed_1955_, v_oldTraces_1946_, v_msg_1947_, v_resStartStop_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec_ref(v_opts_1944_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__0___redArg(lean_object* v_a_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_Lean_Meta_reduceRecMatcher_x3f(v_a_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1977_; 
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1966_ = v___x_1963_;
v_isShared_1967_ = v_isSharedCheck_1977_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1963_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1977_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
if (lean_obj_tag(v_a_1964_) == 1)
{
lean_object* v_val_1968_; lean_object* v___x_1969_; 
lean_del_object(v___x_1966_);
lean_dec_ref(v_a_1957_);
v_val_1968_ = lean_ctor_get(v_a_1964_, 0);
lean_inc(v_val_1968_);
lean_dec_ref_known(v_a_1964_, 1);
v___x_1969_ = l_Lean_Expr_headBeta(v_val_1968_);
v_a_1957_ = v___x_1969_;
goto _start;
}
else
{
lean_object* v___x_1971_; uint8_t v___x_1972_; 
lean_dec(v_a_1964_);
lean_inc_ref(v_a_1957_);
v___x_1971_ = l_Lean_Expr_headBeta(v_a_1957_);
v___x_1972_ = lean_expr_eqv(v_a_1957_, v___x_1971_);
if (v___x_1972_ == 0)
{
lean_del_object(v___x_1966_);
lean_dec_ref(v_a_1957_);
v_a_1957_ = v___x_1971_;
goto _start;
}
else
{
lean_object* v___x_1975_; 
lean_dec_ref(v___x_1971_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 0, v_a_1957_);
v___x_1975_ = v___x_1966_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1957_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_dec_ref(v_a_1957_);
v_a_1978_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1963_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1963_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__0___redArg___boxed(lean_object* v_a_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_a_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
return v_res_1992_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__11(void){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2012_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__8));
v___x_2013_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__10));
v___x_2014_ = l_Lean_Name_append(v___x_2013_, v___x_2012_);
return v___x_2014_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__13(void){
_start:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2016_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2017_ = l_Lean_stringToMessageData(v___x_2016_);
return v___x_2017_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__15(void){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__14));
v___x_2020_ = l_Lean_stringToMessageData(v___x_2019_);
return v___x_2020_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__17(void){
_start:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2022_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__16));
v___x_2023_ = l_Lean_stringToMessageData(v___x_2022_);
return v___x_2023_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__19(void){
_start:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__18));
v___x_2026_ = l_Lean_stringToMessageData(v___x_2025_);
return v___x_2026_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__21(void){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__20));
v___x_2029_ = l_Lean_stringToMessageData(v___x_2028_);
return v___x_2029_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__23(void){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__22));
v___x_2032_ = l_Lean_stringToMessageData(v___x_2031_);
return v___x_2032_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__24(void){
_start:
{
lean_object* v___x_2033_; lean_object* v_dummy_2034_; 
v___x_2033_ = lean_box(0);
v_dummy_2034_ = l_Lean_Expr_sort___override(v___x_2033_);
return v_dummy_2034_;
}
}
static double _init_l_Lean_Meta_rwMatcher___closed__25(void){
_start:
{
lean_object* v___x_2035_; double v___x_2036_; 
v___x_2035_ = lean_unsigned_to_nat(1000000000u);
v___x_2036_ = lean_float_of_nat(v___x_2035_);
return v___x_2036_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__27(void){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__26));
v___x_2039_ = l_Lean_stringToMessageData(v___x_2038_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher(lean_object* v_altIdx_2040_, lean_object* v_e_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_){
_start:
{
lean_object* v___y_2069_; lean_object* v___x_2079_; uint8_t v___x_2080_; 
v___x_2079_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__2));
v___x_2080_ = l_Lean_Expr_isAppOf(v_e_2041_, v___x_2079_);
if (v___x_2080_ == 0)
{
lean_object* v___x_2081_; uint8_t v___x_2082_; 
v___x_2081_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__4));
v___x_2082_ = l_Lean_Expr_isAppOf(v_e_2041_, v___x_2081_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2083_; uint8_t v___x_2084_; lean_object* v___y_2086_; lean_object* v_proof_2087_; lean_object* v___x_2102_; lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2535_; 
v___x_2083_ = lean_box(0);
v___x_2084_ = 1;
v___x_2102_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__2___redArg(v_e_2041_, v_a_2045_);
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2105_ = v___x_2102_;
v_isShared_2106_ = v_isSharedCheck_2535_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2102_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2535_;
goto v_resetjp_2104_;
}
v___jp_2085_:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2088_, 0, v_proof_2087_);
v___x_2089_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2089_, 0, v___y_2086_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
lean_ctor_set_uint8(v___x_2089_, sizeof(void*)*2, v___x_2084_);
v___x_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
return v___x_2090_;
}
v___jp_2091_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2092_ = lean_box(0);
v___x_2093_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2093_, 0, v_e_2041_);
lean_ctor_set(v___x_2093_, 1, v___x_2092_);
lean_ctor_set_uint8(v___x_2093_, sizeof(void*)*2, v___x_2084_);
v___x_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
return v___x_2094_;
}
v___jp_2095_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2096_ = lean_box(0);
v___x_2097_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2097_, 0, v_e_2041_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
lean_ctor_set_uint8(v___x_2097_, sizeof(void*)*2, v___x_2084_);
v___x_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
return v___x_2098_;
}
v___jp_2099_:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = lean_box(0);
v___x_2101_ = l_Lean_Meta_rwMatcher___lam__0(v_e_2041_, v___x_2084_, v___x_2100_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
v___y_2069_ = v___x_2101_;
goto v___jp_2068_;
}
v_resetjp_2104_:
{
uint8_t v___x_2107_; 
v___x_2107_ = lean_unbox(v_a_2103_);
lean_dec(v_a_2103_);
if (v___x_2107_ == 0)
{
lean_object* v_toCold_2108_; lean_object* v_options_2109_; uint8_t v_hasTrace_2110_; 
lean_del_object(v___x_2105_);
lean_dec(v_altIdx_2040_);
v_toCold_2108_ = lean_ctor_get(v_a_2044_, 0);
v_options_2109_ = lean_ctor_get(v_toCold_2108_, 2);
v_hasTrace_2110_ = lean_ctor_get_uint8(v_options_2109_, sizeof(void*)*1);
if (v_hasTrace_2110_ == 0)
{
goto v___jp_2091_;
}
else
{
lean_object* v_inheritedTraceOptions_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; uint8_t v___x_2114_; 
v_inheritedTraceOptions_2111_ = lean_ctor_get(v_toCold_2108_, 11);
v___x_2112_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__8));
v___x_2113_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__11, &l_Lean_Meta_rwMatcher___closed__11_once, _init_l_Lean_Meta_rwMatcher___closed__11);
v___x_2114_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2111_, v_options_2109_, v___x_2113_);
if (v___x_2114_ == 0)
{
goto v___jp_2091_;
}
else
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2115_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
lean_inc_ref(v_e_2041_);
v___x_2116_ = l_Lean_indentExpr(v_e_2041_);
v___x_2117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2115_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
v___x_2118_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(v___x_2112_, v___x_2117_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_dec_ref_known(v___x_2118_, 1);
goto v___jp_2091_;
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_dec_ref(v_e_2041_);
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2118_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
}
}
else
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2127_ = l_Lean_Expr_getAppFn(v_e_2041_);
v___x_2128_ = l_Lean_Expr_constName_x21(v___x_2127_);
lean_inc(v_a_2045_);
lean_inc_ref(v_a_2044_);
lean_inc(v_a_2043_);
lean_inc_ref(v_a_2042_);
lean_inc(v___x_2128_);
v___x_2129_ = lean_get_congr_match_equations_for(v___x_2128_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2526_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2132_ = v___x_2129_;
v_isShared_2133_ = v_isSharedCheck_2526_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2129_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2526_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2134_; uint8_t v___x_2135_; 
v___x_2134_ = lean_array_get_size(v_a_2130_);
v___x_2135_ = lean_nat_dec_lt(v_altIdx_2040_, v___x_2134_);
if (v___x_2135_ == 0)
{
lean_object* v_toCold_2136_; lean_object* v_options_2137_; uint8_t v_hasTrace_2138_; 
lean_del_object(v___x_2132_);
lean_dec(v_a_2130_);
lean_dec_ref(v___x_2127_);
v_toCold_2136_ = lean_ctor_get(v_a_2044_, 0);
v_options_2137_ = lean_ctor_get(v_toCold_2136_, 2);
v_hasTrace_2138_ = lean_ctor_get_uint8(v_options_2137_, sizeof(void*)*1);
if (v_hasTrace_2138_ == 0)
{
lean_dec(v___x_2128_);
lean_del_object(v___x_2105_);
lean_dec(v_altIdx_2040_);
goto v___jp_2095_;
}
else
{
lean_object* v_inheritedTraceOptions_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v_inheritedTraceOptions_2139_ = lean_ctor_get(v_toCold_2136_, 11);
v___x_2140_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__8));
v___x_2141_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__11, &l_Lean_Meta_rwMatcher___closed__11_once, _init_l_Lean_Meta_rwMatcher___closed__11);
v___x_2142_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2139_, v_options_2137_, v___x_2141_);
if (v___x_2142_ == 0)
{
lean_dec(v___x_2128_);
lean_del_object(v___x_2105_);
lean_dec(v_altIdx_2040_);
goto v___jp_2095_;
}
else
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2146_; 
v___x_2143_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__15, &l_Lean_Meta_rwMatcher___closed__15_once, _init_l_Lean_Meta_rwMatcher___closed__15);
v___x_2144_ = l_Nat_reprFast(v_altIdx_2040_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set_tag(v___x_2105_, 3);
lean_ctor_set(v___x_2105_, 0, v___x_2144_);
v___x_2146_ = v___x_2105_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2144_);
v___x_2146_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2147_ = l_Lean_MessageData_ofFormat(v___x_2146_);
v___x_2148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2143_);
lean_ctor_set(v___x_2148_, 1, v___x_2147_);
v___x_2149_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__17, &l_Lean_Meta_rwMatcher___closed__17_once, _init_l_Lean_Meta_rwMatcher___closed__17);
v___x_2150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2148_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v___x_2151_ = l_Nat_reprFast(v___x_2134_);
v___x_2152_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
v___x_2153_ = l_Lean_MessageData_ofFormat(v___x_2152_);
v___x_2154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2150_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__19, &l_Lean_Meta_rwMatcher___closed__19_once, _init_l_Lean_Meta_rwMatcher___closed__19);
v___x_2156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2154_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = l_Lean_MessageData_ofConstName(v___x_2128_, v___x_2135_);
v___x_2158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2156_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
v___x_2159_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(v___x_2140_, v___x_2158_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_dec_ref_known(v___x_2159_, 1);
goto v___jp_2095_;
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_dec_ref(v_e_2041_);
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2159_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2159_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
}
}
}
else
{
lean_object* v_toCold_2169_; lean_object* v_options_2170_; lean_object* v_inheritedTraceOptions_2171_; uint8_t v_hasTrace_2172_; lean_object* v_nargs_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v_a_2177_; lean_object* v___y_2208_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v_dummy_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
lean_dec(v___x_2128_);
v_toCold_2169_ = lean_ctor_get(v_a_2044_, 0);
v_options_2170_ = lean_ctor_get(v_toCold_2169_, 2);
v_inheritedTraceOptions_2171_ = lean_ctor_get(v_toCold_2169_, 11);
v_hasTrace_2172_ = lean_ctor_get_uint8(v_options_2170_, sizeof(void*)*1);
v_nargs_2173_ = l_Lean_Expr_getAppNumArgs(v_e_2041_);
v___x_2174_ = lean_array_get(v___x_2083_, v_a_2130_, v_altIdx_2040_);
lean_dec(v_altIdx_2040_);
lean_dec(v_a_2130_);
v___x_2175_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__8));
v___x_2210_ = l_Lean_Expr_constLevels_x21(v___x_2127_);
lean_dec_ref(v___x_2127_);
lean_inc(v___x_2174_);
v___x_2211_ = l_Lean_mkConst(v___x_2174_, v___x_2210_);
v_dummy_2212_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__24, &l_Lean_Meta_rwMatcher___closed__24_once, _init_l_Lean_Meta_rwMatcher___closed__24);
lean_inc(v_nargs_2173_);
v___x_2213_ = lean_mk_array(v_nargs_2173_, v_dummy_2212_);
v___x_2214_ = lean_unsigned_to_nat(1u);
v___x_2215_ = lean_nat_sub(v_nargs_2173_, v___x_2214_);
lean_dec(v_nargs_2173_);
lean_inc_ref(v_e_2041_);
v___x_2216_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2041_, v___x_2213_, v___x_2215_);
v___x_2217_ = l_Lean_mkAppN(v___x_2211_, v___x_2216_);
lean_dec_ref(v___x_2216_);
if (v_hasTrace_2172_ == 0)
{
lean_object* v___x_2218_; 
lean_del_object(v___x_2105_);
lean_inc(v_a_2045_);
lean_inc_ref(v_a_2044_);
lean_inc(v_a_2043_);
lean_inc_ref(v_a_2042_);
lean_inc_ref(v___x_2217_);
v___x_2218_ = lean_infer_type(v___x_2217_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v_a_2219_; uint8_t v___x_2220_; lean_object* v___x_2221_; 
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_a_2219_);
lean_dec_ref_known(v___x_2218_, 1);
v___x_2220_ = 0;
v___x_2221_ = l_Lean_Meta_forallMetaTelescope(v_a_2219_, v___x_2220_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v_snd_2223_; lean_object* v_fst_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2360_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2222_);
lean_dec_ref_known(v___x_2221_, 1);
v_snd_2223_ = lean_ctor_get(v_a_2222_, 1);
v_fst_2224_ = lean_ctor_get(v_a_2222_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v_a_2222_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2226_ = v_a_2222_;
v_isShared_2227_ = v_isSharedCheck_2360_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_snd_2223_);
lean_inc(v_fst_2224_);
lean_dec(v_a_2222_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2360_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v_snd_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2358_; 
v_snd_2228_ = lean_ctor_get(v_snd_2223_, 1);
v_isSharedCheck_2358_ = !lean_is_exclusive(v_snd_2223_);
if (v_isSharedCheck_2358_ == 0)
{
lean_object* v_unused_2359_; 
v_unused_2359_ = lean_ctor_get(v_snd_2223_, 0);
lean_dec(v_unused_2359_);
v___x_2230_ = v_snd_2223_;
v_isShared_2231_ = v_isSharedCheck_2358_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_snd_2228_);
lean_dec(v_snd_2223_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2358_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2232_; lean_object* v___y_2234_; uint8_t v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; uint8_t v___y_2272_; lean_object* v_a_2273_; size_t v_sz_2289_; size_t v___x_2290_; lean_object* v___x_2291_; lean_object* v___y_2293_; uint8_t v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; uint8_t v_fst_2312_; lean_object* v_fst_2313_; lean_object* v_snd_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___x_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; 
v___x_2232_ = l_Lean_mkAppN(v___x_2217_, v_fst_2224_);
v_sz_2289_ = lean_array_size(v_fst_2224_);
v___x_2290_ = ((size_t)0ULL);
v___x_2291_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4(v_sz_2289_, v___x_2290_, v_fst_2224_);
v___x_2338_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_2339_ = lean_unsigned_to_nat(4u);
v___x_2340_ = l_Lean_Expr_isAppOfArity(v_snd_2228_, v___x_2338_, v___x_2339_);
if (v___x_2340_ == 0)
{
lean_object* v___x_2341_; lean_object* v___x_2342_; uint8_t v___x_2343_; 
v___x_2341_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_2342_ = lean_unsigned_to_nat(3u);
v___x_2343_ = l_Lean_Expr_isAppOfArity(v_snd_2228_, v___x_2341_, v___x_2342_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v_a_2350_; 
lean_dec_ref(v___x_2291_);
lean_dec_ref(v___x_2232_);
lean_del_object(v___x_2230_);
lean_dec(v_snd_2228_);
lean_del_object(v___x_2226_);
v___x_2344_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
lean_inc(v___x_2174_);
v___x_2345_ = l_Lean_MessageData_ofConstName(v___x_2174_, v___x_2082_);
v___x_2346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2344_);
lean_ctor_set(v___x_2346_, 1, v___x_2345_);
v___x_2347_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_2348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2346_);
lean_ctor_set(v___x_2348_, 1, v___x_2347_);
v___x_2349_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_2348_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2350_);
lean_dec_ref(v___x_2349_);
v_a_2177_ = v_a_2350_;
goto v___jp_2176_;
}
else
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2351_ = l_Lean_Expr_appFn_x21(v_snd_2228_);
v___x_2352_ = l_Lean_Expr_appArg_x21(v___x_2351_);
lean_dec_ref(v___x_2351_);
v___x_2353_ = l_Lean_Expr_appArg_x21(v_snd_2228_);
lean_dec(v_snd_2228_);
v_fst_2312_ = v___x_2082_;
v_fst_2313_ = v___x_2352_;
v_snd_2314_ = v___x_2353_;
v___y_2315_ = v_a_2042_;
v___y_2316_ = v_a_2043_;
v___y_2317_ = v_a_2044_;
v___y_2318_ = v_a_2045_;
goto v___jp_2311_;
}
}
else
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2354_ = l_Lean_Expr_appFn_x21(v_snd_2228_);
v___x_2355_ = l_Lean_Expr_appFn_x21(v___x_2354_);
lean_dec_ref(v___x_2354_);
v___x_2356_ = l_Lean_Expr_appArg_x21(v___x_2355_);
lean_dec_ref(v___x_2355_);
v___x_2357_ = l_Lean_Expr_appArg_x21(v_snd_2228_);
lean_dec(v_snd_2228_);
v_fst_2312_ = v___x_2084_;
v_fst_2313_ = v___x_2356_;
v_snd_2314_ = v___x_2357_;
v___y_2315_ = v_a_2042_;
v___y_2316_ = v_a_2043_;
v___y_2317_ = v_a_2044_;
v___y_2318_ = v_a_2045_;
goto v___jp_2311_;
}
v___jp_2233_:
{
lean_object* v___x_2240_; lean_object* v_a_2241_; lean_object* v___x_2242_; 
v___x_2240_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___y_2234_, v___y_2237_);
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_a_2241_);
lean_dec_ref(v___x_2240_);
v___x_2242_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2232_, v___y_2237_);
if (v___y_2235_ == 0)
{
lean_object* v_a_2243_; 
lean_del_object(v___x_2230_);
lean_del_object(v___x_2226_);
lean_dec(v___x_2174_);
lean_del_object(v___x_2132_);
lean_dec_ref(v_e_2041_);
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
lean_inc(v_a_2243_);
lean_dec_ref(v___x_2242_);
v___y_2086_ = v_a_2241_;
v_proof_2087_ = v_a_2243_;
goto v___jp_2085_;
}
else
{
lean_object* v_a_2244_; lean_object* v___x_2245_; 
v_a_2244_ = lean_ctor_get(v___x_2242_, 0);
lean_inc_n(v_a_2244_, 2);
lean_dec_ref(v___x_2242_);
v___x_2245_ = l_Lean_Meta_mkEqOfHEq(v_a_2244_, v___x_2084_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; 
lean_dec(v_a_2244_);
lean_del_object(v___x_2230_);
lean_del_object(v___x_2226_);
lean_dec(v___x_2174_);
lean_del_object(v___x_2132_);
lean_dec_ref(v_e_2041_);
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_a_2246_);
lean_dec_ref_known(v___x_2245_, 1);
v___y_2086_ = v_a_2241_;
v_proof_2087_ = v_a_2246_;
goto v___jp_2085_;
}
else
{
lean_object* v_a_2247_; uint8_t v___x_2248_; 
lean_dec(v_a_2241_);
v_a_2247_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_a_2247_);
lean_dec_ref_known(v___x_2245_, 1);
v___x_2248_ = l_Lean_Exception_isInterrupt(v_a_2247_);
if (v___x_2248_ == 0)
{
uint8_t v___x_2249_; 
lean_inc(v_a_2247_);
v___x_2249_ = l_Lean_Exception_isRuntime(v_a_2247_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2253_; 
v___x_2250_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_2251_ = l_Lean_MessageData_ofExpr(v_a_2244_);
if (v_isShared_2231_ == 0)
{
lean_ctor_set_tag(v___x_2230_, 7);
lean_ctor_set(v___x_2230_, 1, v___x_2251_);
lean_ctor_set(v___x_2230_, 0, v___x_2250_);
v___x_2253_ = v___x_2230_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2250_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v___x_2251_);
v___x_2253_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
lean_object* v___x_2254_; lean_object* v___x_2256_; 
v___x_2254_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
if (v_isShared_2227_ == 0)
{
lean_ctor_set_tag(v___x_2226_, 7);
lean_ctor_set(v___x_2226_, 1, v___x_2254_);
lean_ctor_set(v___x_2226_, 0, v___x_2253_);
v___x_2256_ = v___x_2226_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2253_);
lean_ctor_set(v_reuseFailAlloc_2264_, 1, v___x_2254_);
v___x_2256_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v_a_2263_; 
v___x_2257_ = l_Lean_Exception_toMessageData(v_a_2247_);
v___x_2258_ = l_Lean_indentD(v___x_2257_);
v___x_2259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2256_);
lean_ctor_set(v___x_2259_, 1, v___x_2258_);
v___x_2260_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_2261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2259_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
v___x_2262_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_2261_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc(v_a_2263_);
lean_dec_ref(v___x_2262_);
v_a_2177_ = v_a_2263_;
goto v___jp_2176_;
}
}
}
else
{
lean_dec(v_a_2244_);
lean_del_object(v___x_2230_);
lean_del_object(v___x_2226_);
v_a_2177_ = v_a_2247_;
goto v___jp_2176_;
}
}
else
{
lean_dec(v_a_2244_);
lean_del_object(v___x_2230_);
lean_del_object(v___x_2226_);
v_a_2177_ = v_a_2247_;
goto v___jp_2176_;
}
}
}
}
v___jp_2266_:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; uint8_t v___x_2276_; 
v___x_2274_ = lean_array_get_size(v_a_2273_);
v___x_2275_ = lean_unsigned_to_nat(0u);
v___x_2276_ = lean_nat_dec_eq(v___x_2274_, v___x_2275_);
if (v___x_2276_ == 0)
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v_a_2288_; 
lean_dec_ref(v___y_2267_);
lean_dec_ref(v___x_2232_);
lean_del_object(v___x_2230_);
lean_del_object(v___x_2226_);
v___x_2277_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
lean_inc(v___x_2174_);
v___x_2278_ = l_Lean_MessageData_ofConstName(v___x_2174_, v___x_2276_);
v___x_2279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2277_);
lean_ctor_set(v___x_2279_, 1, v___x_2278_);
v___x_2280_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_2281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2279_);
lean_ctor_set(v___x_2281_, 1, v___x_2280_);
v___x_2282_ = lean_array_to_list(v_a_2273_);
v___x_2283_ = lean_box(0);
v___x_2284_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_2282_, v___x_2283_);
v___x_2285_ = l_Lean_MessageData_ofList(v___x_2284_);
v___x_2286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2281_);
lean_ctor_set(v___x_2286_, 1, v___x_2285_);
v___x_2287_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_2286_, v___y_2269_, v___y_2271_, v___y_2268_, v___y_2270_);
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref(v___x_2287_);
v_a_2177_ = v_a_2288_;
goto v___jp_2176_;
}
else
{
lean_dec_ref(v_a_2273_);
v___y_2234_ = v___y_2267_;
v___y_2235_ = v___y_2272_;
v___y_2236_ = v___y_2269_;
v___y_2237_ = v___y_2271_;
v___y_2238_ = v___y_2268_;
v___y_2239_ = v___y_2270_;
goto v___jp_2233_;
}
}
v___jp_2292_:
{
lean_object* v___x_2299_; size_t v_sz_2300_; lean_object* v___x_2301_; 
v___x_2299_ = lean_box(0);
v_sz_2300_ = lean_array_size(v___x_2291_);
v___x_2301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8(v___x_2291_, v_sz_2300_, v___x_2290_, v___x_2299_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; uint8_t v___x_2305_; 
lean_dec_ref_known(v___x_2301_, 1);
v___x_2302_ = lean_unsigned_to_nat(0u);
v___x_2303_ = lean_array_get_size(v___x_2291_);
v___x_2304_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_2305_ = lean_nat_dec_lt(v___x_2302_, v___x_2303_);
if (v___x_2305_ == 0)
{
lean_dec_ref(v___x_2291_);
v___y_2267_ = v___y_2293_;
v___y_2268_ = v___y_2297_;
v___y_2269_ = v___y_2295_;
v___y_2270_ = v___y_2298_;
v___y_2271_ = v___y_2296_;
v___y_2272_ = v___y_2294_;
v_a_2273_ = v___x_2304_;
goto v___jp_2266_;
}
else
{
size_t v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = lean_usize_of_nat(v___x_2303_);
v___x_2307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9(v___x_2291_, v___x_2290_, v___x_2306_, v___x_2304_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
lean_dec_ref(v___x_2291_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2308_);
lean_dec_ref_known(v___x_2307_, 1);
v___y_2267_ = v___y_2293_;
v___y_2268_ = v___y_2297_;
v___y_2269_ = v___y_2295_;
v___y_2270_ = v___y_2298_;
v___y_2271_ = v___y_2296_;
v___y_2272_ = v___y_2294_;
v_a_2273_ = v_a_2308_;
goto v___jp_2266_;
}
else
{
lean_object* v_a_2309_; 
lean_dec_ref(v___y_2293_);
lean_dec_ref(v___x_2232_);
lean_del_object(v___x_2230_);
lean_del_object(v___x_2226_);
v_a_2309_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2309_);
lean_dec_ref_known(v___x_2307_, 1);
v_a_2177_ = v_a_2309_;
goto v___jp_2176_;
}
}
}
else
{
lean_object* v_a_2310_; 
lean_dec_ref(v___y_2293_);
lean_dec_ref(v___x_2291_);
lean_dec_ref(v___x_2232_);
lean_del_object(v___x_2230_);
lean_del_object(v___x_2226_);
v_a_2310_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2310_);
lean_dec_ref_known(v___x_2301_, 1);
v_a_2177_ = v_a_2310_;
goto v___jp_2176_;
}
}
v___jp_2311_:
{
lean_object* v___x_2319_; 
lean_inc_ref(v_fst_2313_);
lean_inc_ref(v_e_2041_);
v___x_2319_ = l_Lean_Meta_isExprDefEq(v_e_2041_, v_fst_2313_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; uint8_t v___x_2321_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2320_);
lean_dec_ref_known(v___x_2319_, 1);
v___x_2321_ = lean_unbox(v_a_2320_);
lean_dec(v_a_2320_);
if (v___x_2321_ == 0)
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v_a_2336_; 
lean_dec_ref(v_snd_2314_);
lean_dec_ref(v___x_2291_);
lean_dec_ref(v___x_2232_);
lean_del_object(v___x_2230_);
lean_del_object(v___x_2226_);
v___x_2322_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_2323_ = l_Lean_MessageData_ofExpr(v_fst_2313_);
v___x_2324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2322_);
lean_ctor_set(v___x_2324_, 1, v___x_2323_);
v___x_2325_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_2326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2324_);
lean_ctor_set(v___x_2326_, 1, v___x_2325_);
lean_inc(v___x_2174_);
v___x_2327_ = l_Lean_MessageData_ofConstName(v___x_2174_, v___x_2082_);
v___x_2328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2326_);
lean_ctor_set(v___x_2328_, 1, v___x_2327_);
v___x_2329_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_2330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2328_);
lean_ctor_set(v___x_2330_, 1, v___x_2329_);
lean_inc_ref(v_e_2041_);
v___x_2331_ = l_Lean_MessageData_ofExpr(v_e_2041_);
v___x_2332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2330_);
lean_ctor_set(v___x_2332_, 1, v___x_2331_);
v___x_2333_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
v___x_2334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2332_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
v___x_2335_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_2334_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2336_);
lean_dec_ref(v___x_2335_);
v_a_2177_ = v_a_2336_;
goto v___jp_2176_;
}
else
{
lean_dec_ref(v_fst_2313_);
v___y_2293_ = v_snd_2314_;
v___y_2294_ = v_fst_2312_;
v___y_2295_ = v___y_2315_;
v___y_2296_ = v___y_2316_;
v___y_2297_ = v___y_2317_;
v___y_2298_ = v___y_2318_;
goto v___jp_2292_;
}
}
else
{
lean_object* v_a_2337_; 
lean_dec_ref(v_snd_2314_);
lean_dec_ref(v_fst_2313_);
lean_dec_ref(v___x_2291_);
lean_dec_ref(v___x_2232_);
lean_del_object(v___x_2230_);
lean_del_object(v___x_2226_);
v_a_2337_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2319_, 1);
v_a_2177_ = v_a_2337_;
goto v___jp_2176_;
}
}
}
}
}
else
{
lean_object* v_a_2361_; 
lean_dec_ref(v___x_2217_);
v_a_2361_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2361_);
lean_dec_ref_known(v___x_2221_, 1);
v_a_2177_ = v_a_2361_;
goto v___jp_2176_;
}
}
else
{
lean_object* v_a_2362_; 
lean_dec_ref(v___x_2217_);
v_a_2362_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2218_, 1);
v_a_2177_ = v_a_2362_;
goto v___jp_2176_;
}
}
else
{
lean_object* v___x_2363_; lean_object* v___f_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; uint8_t v___x_2367_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v_a_2371_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v_a_2386_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v_a_2406_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v_a_2418_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; 
v___x_2363_ = lean_box(v___x_2082_);
lean_inc_ref(v_e_2041_);
lean_inc(v___x_2174_);
v___f_2364_ = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__1___boxed), 9, 3);
lean_closure_set(v___f_2364_, 0, v___x_2174_);
lean_closure_set(v___f_2364_, 1, v___x_2363_);
lean_closure_set(v___f_2364_, 2, v_e_2041_);
v___x_2365_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__1));
v___x_2366_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__11, &l_Lean_Meta_rwMatcher___closed__11_once, _init_l_Lean_Meta_rwMatcher___closed__11);
v___x_2367_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2171_, v_options_2170_, v___x_2366_);
if (v___x_2367_ == 0)
{
lean_object* v___x_2496_; uint8_t v___x_2497_; 
v___x_2496_ = l_Lean_trace_profiler;
v___x_2497_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11(v_options_2170_, v___x_2496_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2498_; 
lean_dec_ref(v___f_2364_);
lean_del_object(v___x_2105_);
lean_inc(v_a_2045_);
lean_inc_ref(v_a_2044_);
lean_inc(v_a_2043_);
lean_inc_ref(v_a_2042_);
lean_inc_ref(v___x_2217_);
v___x_2498_ = lean_infer_type(v___x_2217_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; uint8_t v___x_2500_; lean_object* v___x_2501_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_a_2499_);
lean_dec_ref_known(v___x_2498_, 1);
v___x_2500_ = 0;
v___x_2501_ = l_Lean_Meta_forallMetaTelescope(v_a_2499_, v___x_2500_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_a_2502_; lean_object* v_snd_2503_; 
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_a_2502_);
lean_dec_ref_known(v___x_2501_, 1);
v_snd_2503_ = lean_ctor_get(v_a_2502_, 1);
lean_inc(v_snd_2503_);
if (v___x_2367_ == 0)
{
lean_object* v_fst_2504_; lean_object* v_snd_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v_fst_2504_ = lean_ctor_get(v_a_2502_, 0);
lean_inc(v_fst_2504_);
lean_dec(v_a_2502_);
v_snd_2505_ = lean_ctor_get(v_snd_2503_, 1);
lean_inc(v_snd_2505_);
lean_dec(v_snd_2503_);
v___x_2506_ = lean_box(0);
lean_inc_ref(v_e_2041_);
lean_inc(v___x_2174_);
v___x_2507_ = l_Lean_Meta_rwMatcher___lam__4(v___x_2084_, v___x_2217_, v_fst_2504_, v___x_2174_, v_e_2041_, v___x_2082_, v_snd_2505_, v___x_2506_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
lean_dec(v_snd_2505_);
v___y_2208_ = v___x_2507_;
goto v___jp_2207_;
}
else
{
lean_object* v_fst_2508_; lean_object* v_snd_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2522_; 
v_fst_2508_ = lean_ctor_get(v_a_2502_, 0);
lean_inc(v_fst_2508_);
lean_dec(v_a_2502_);
v_snd_2509_ = lean_ctor_get(v_snd_2503_, 1);
v_isSharedCheck_2522_ = !lean_is_exclusive(v_snd_2503_);
if (v_isSharedCheck_2522_ == 0)
{
lean_object* v_unused_2523_; 
v_unused_2523_ = lean_ctor_get(v_snd_2503_, 0);
lean_dec(v_unused_2523_);
v___x_2511_ = v_snd_2503_;
v_isShared_2512_ = v_isSharedCheck_2522_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_snd_2509_);
lean_dec(v_snd_2503_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2522_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2516_; 
v___x_2513_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__27, &l_Lean_Meta_rwMatcher___closed__27_once, _init_l_Lean_Meta_rwMatcher___closed__27);
lean_inc(v_snd_2509_);
v___x_2514_ = l_Lean_indentExpr(v_snd_2509_);
if (v_isShared_2512_ == 0)
{
lean_ctor_set_tag(v___x_2511_, 7);
lean_ctor_set(v___x_2511_, 1, v___x_2514_);
lean_ctor_set(v___x_2511_, 0, v___x_2513_);
v___x_2516_ = v___x_2511_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2513_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v___x_2514_);
v___x_2516_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v___x_2517_; 
v___x_2517_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(v___x_2175_, v___x_2516_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2519_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
lean_inc(v_a_2518_);
lean_dec_ref_known(v___x_2517_, 1);
lean_inc_ref(v_e_2041_);
lean_inc(v___x_2174_);
v___x_2519_ = l_Lean_Meta_rwMatcher___lam__4(v___x_2084_, v___x_2217_, v_fst_2508_, v___x_2174_, v_e_2041_, v___x_2082_, v_snd_2509_, v_a_2518_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
lean_dec(v_snd_2509_);
v___y_2208_ = v___x_2519_;
goto v___jp_2207_;
}
else
{
lean_object* v_a_2520_; 
lean_dec(v_snd_2509_);
lean_dec(v_fst_2508_);
lean_dec_ref(v___x_2217_);
v_a_2520_ = lean_ctor_get(v___x_2517_, 0);
lean_inc(v_a_2520_);
lean_dec_ref_known(v___x_2517_, 1);
v_a_2177_ = v_a_2520_;
goto v___jp_2176_;
}
}
}
}
}
else
{
lean_object* v_a_2524_; 
lean_dec_ref(v___x_2217_);
v_a_2524_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_a_2524_);
lean_dec_ref_known(v___x_2501_, 1);
v_a_2177_ = v_a_2524_;
goto v___jp_2176_;
}
}
else
{
lean_object* v_a_2525_; 
lean_dec_ref(v___x_2217_);
v_a_2525_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_a_2525_);
lean_dec_ref_known(v___x_2498_, 1);
v_a_2177_ = v_a_2525_;
goto v___jp_2176_;
}
}
else
{
goto v___jp_2433_;
}
}
else
{
goto v___jp_2433_;
}
v___jp_2368_:
{
lean_object* v___x_2372_; double v___x_2373_; double v___x_2374_; double v___x_2375_; double v___x_2376_; double v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2372_ = lean_io_mono_nanos_now();
v___x_2373_ = lean_float_of_nat(v___y_2369_);
v___x_2374_ = lean_float_once(&l_Lean_Meta_rwMatcher___closed__25, &l_Lean_Meta_rwMatcher___closed__25_once, _init_l_Lean_Meta_rwMatcher___closed__25);
v___x_2375_ = lean_float_div(v___x_2373_, v___x_2374_);
v___x_2376_ = lean_float_of_nat(v___x_2372_);
v___x_2377_ = lean_float_div(v___x_2376_, v___x_2374_);
v___x_2378_ = lean_box_float(v___x_2375_);
v___x_2379_ = lean_box_float(v___x_2377_);
v___x_2380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2378_);
lean_ctor_set(v___x_2380_, 1, v___x_2379_);
v___x_2381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2381_, 0, v_a_2371_);
lean_ctor_set(v___x_2381_, 1, v___x_2380_);
v___x_2382_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12(v___x_2175_, v___x_2084_, v___x_2365_, v_options_2170_, v___x_2367_, v___y_2370_, v___f_2364_, v___x_2381_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
v___y_2208_ = v___x_2382_;
goto v___jp_2207_;
}
v___jp_2383_:
{
lean_object* v___x_2388_; 
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 0, v_a_2386_);
v___x_2388_ = v___x_2105_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2386_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
v___y_2369_ = v___y_2384_;
v___y_2370_ = v___y_2385_;
v_a_2371_ = v___x_2388_;
goto v___jp_2368_;
}
}
v___jp_2390_:
{
if (lean_obj_tag(v___y_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2401_; 
lean_del_object(v___x_2105_);
v_a_2394_ = lean_ctor_get(v___y_2393_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___y_2393_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2396_ = v___y_2393_;
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___y_2393_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
if (v_isShared_2397_ == 0)
{
lean_ctor_set_tag(v___x_2396_, 1);
v___x_2399_ = v___x_2396_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2394_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
v___y_2369_ = v___y_2391_;
v___y_2370_ = v___y_2392_;
v_a_2371_ = v___x_2399_;
goto v___jp_2368_;
}
}
}
else
{
lean_object* v_a_2402_; 
v_a_2402_ = lean_ctor_get(v___y_2393_, 0);
lean_inc(v_a_2402_);
lean_dec_ref_known(v___y_2393_, 1);
v___y_2384_ = v___y_2391_;
v___y_2385_ = v___y_2392_;
v_a_2386_ = v_a_2402_;
goto v___jp_2383_;
}
}
v___jp_2403_:
{
lean_object* v___x_2407_; double v___x_2408_; double v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2407_ = lean_io_get_num_heartbeats();
v___x_2408_ = lean_float_of_nat(v___y_2404_);
v___x_2409_ = lean_float_of_nat(v___x_2407_);
v___x_2410_ = lean_box_float(v___x_2408_);
v___x_2411_ = lean_box_float(v___x_2409_);
v___x_2412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2410_);
lean_ctor_set(v___x_2412_, 1, v___x_2411_);
v___x_2413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2413_, 0, v_a_2406_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
v___x_2414_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12(v___x_2175_, v___x_2084_, v___x_2365_, v_options_2170_, v___x_2367_, v___y_2405_, v___f_2364_, v___x_2413_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
v___y_2208_ = v___x_2414_;
goto v___jp_2207_;
}
v___jp_2415_:
{
lean_object* v___x_2419_; 
v___x_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2419_, 0, v_a_2418_);
v___y_2404_ = v___y_2416_;
v___y_2405_ = v___y_2417_;
v_a_2406_ = v___x_2419_;
goto v___jp_2403_;
}
v___jp_2420_:
{
if (lean_obj_tag(v___y_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
v_a_2424_ = lean_ctor_get(v___y_2423_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___y_2423_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2426_ = v___y_2423_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___y_2423_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
lean_ctor_set_tag(v___x_2426_, 1);
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2424_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
v___y_2404_ = v___y_2421_;
v___y_2405_ = v___y_2422_;
v_a_2406_ = v___x_2429_;
goto v___jp_2403_;
}
}
}
else
{
lean_object* v_a_2432_; 
v_a_2432_ = lean_ctor_get(v___y_2423_, 0);
lean_inc(v_a_2432_);
lean_dec_ref_known(v___y_2423_, 1);
v___y_2416_ = v___y_2421_;
v___y_2417_ = v___y_2422_;
v_a_2418_ = v_a_2432_;
goto v___jp_2415_;
}
}
v___jp_2433_:
{
lean_object* v___x_2434_; lean_object* v_a_2435_; lean_object* v___x_2436_; uint8_t v___x_2437_; 
v___x_2434_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg(v_a_2045_);
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_a_2435_);
lean_dec_ref(v___x_2434_);
v___x_2436_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2437_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11(v_options_2170_, v___x_2436_);
if (v___x_2437_ == 0)
{
lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2438_ = lean_io_mono_nanos_now();
lean_inc(v_a_2045_);
lean_inc_ref(v_a_2044_);
lean_inc(v_a_2043_);
lean_inc_ref(v_a_2042_);
lean_inc_ref(v___x_2217_);
v___x_2439_ = lean_infer_type(v___x_2217_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v_a_2440_; uint8_t v___x_2441_; lean_object* v___x_2442_; 
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_a_2440_);
lean_dec_ref_known(v___x_2439_, 1);
v___x_2441_ = 0;
v___x_2442_ = l_Lean_Meta_forallMetaTelescope(v_a_2440_, v___x_2441_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v_snd_2444_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_a_2443_);
lean_dec_ref_known(v___x_2442_, 1);
v_snd_2444_ = lean_ctor_get(v_a_2443_, 1);
lean_inc(v_snd_2444_);
if (v___x_2367_ == 0)
{
lean_object* v_fst_2445_; lean_object* v_snd_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v_fst_2445_ = lean_ctor_get(v_a_2443_, 0);
lean_inc(v_fst_2445_);
lean_dec(v_a_2443_);
v_snd_2446_ = lean_ctor_get(v_snd_2444_, 1);
lean_inc(v_snd_2446_);
lean_dec(v_snd_2444_);
v___x_2447_ = lean_box(0);
lean_inc_ref(v_e_2041_);
lean_inc(v___x_2174_);
v___x_2448_ = l_Lean_Meta_rwMatcher___lam__2(v___x_2084_, v___x_2217_, v_fst_2445_, v___x_2174_, v_e_2041_, v___x_2082_, v_snd_2446_, v___x_2447_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
lean_dec(v_snd_2446_);
v___y_2391_ = v___x_2438_;
v___y_2392_ = v_a_2435_;
v___y_2393_ = v___x_2448_;
goto v___jp_2390_;
}
else
{
lean_object* v_fst_2449_; lean_object* v_snd_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2463_; 
v_fst_2449_ = lean_ctor_get(v_a_2443_, 0);
lean_inc(v_fst_2449_);
lean_dec(v_a_2443_);
v_snd_2450_ = lean_ctor_get(v_snd_2444_, 1);
v_isSharedCheck_2463_ = !lean_is_exclusive(v_snd_2444_);
if (v_isSharedCheck_2463_ == 0)
{
lean_object* v_unused_2464_; 
v_unused_2464_ = lean_ctor_get(v_snd_2444_, 0);
lean_dec(v_unused_2464_);
v___x_2452_ = v_snd_2444_;
v_isShared_2453_ = v_isSharedCheck_2463_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_snd_2450_);
lean_dec(v_snd_2444_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2463_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2457_; 
v___x_2454_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__27, &l_Lean_Meta_rwMatcher___closed__27_once, _init_l_Lean_Meta_rwMatcher___closed__27);
lean_inc(v_snd_2450_);
v___x_2455_ = l_Lean_indentExpr(v_snd_2450_);
if (v_isShared_2453_ == 0)
{
lean_ctor_set_tag(v___x_2452_, 7);
lean_ctor_set(v___x_2452_, 1, v___x_2455_);
lean_ctor_set(v___x_2452_, 0, v___x_2454_);
v___x_2457_ = v___x_2452_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2462_, 1, v___x_2455_);
v___x_2457_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(v___x_2175_, v___x_2457_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2460_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_a_2459_);
lean_dec_ref_known(v___x_2458_, 1);
lean_inc_ref(v_e_2041_);
lean_inc(v___x_2174_);
v___x_2460_ = l_Lean_Meta_rwMatcher___lam__2(v___x_2084_, v___x_2217_, v_fst_2449_, v___x_2174_, v_e_2041_, v___x_2082_, v_snd_2450_, v_a_2459_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
lean_dec(v_snd_2450_);
v___y_2391_ = v___x_2438_;
v___y_2392_ = v_a_2435_;
v___y_2393_ = v___x_2460_;
goto v___jp_2390_;
}
else
{
lean_object* v_a_2461_; 
lean_dec(v_snd_2450_);
lean_dec(v_fst_2449_);
lean_dec_ref(v___x_2217_);
v_a_2461_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_a_2461_);
lean_dec_ref_known(v___x_2458_, 1);
v___y_2384_ = v___x_2438_;
v___y_2385_ = v_a_2435_;
v_a_2386_ = v_a_2461_;
goto v___jp_2383_;
}
}
}
}
}
else
{
lean_object* v_a_2465_; 
lean_dec_ref(v___x_2217_);
v_a_2465_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_a_2465_);
lean_dec_ref_known(v___x_2442_, 1);
v___y_2384_ = v___x_2438_;
v___y_2385_ = v_a_2435_;
v_a_2386_ = v_a_2465_;
goto v___jp_2383_;
}
}
else
{
lean_object* v_a_2466_; 
lean_dec_ref(v___x_2217_);
v_a_2466_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_a_2466_);
lean_dec_ref_known(v___x_2439_, 1);
v___y_2384_ = v___x_2438_;
v___y_2385_ = v_a_2435_;
v_a_2386_ = v_a_2466_;
goto v___jp_2383_;
}
}
else
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
lean_del_object(v___x_2105_);
v___x_2467_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2045_);
lean_inc_ref(v_a_2044_);
lean_inc(v_a_2043_);
lean_inc_ref(v_a_2042_);
lean_inc_ref(v___x_2217_);
v___x_2468_ = lean_infer_type(v___x_2217_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; uint8_t v___x_2470_; lean_object* v___x_2471_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_a_2469_);
lean_dec_ref_known(v___x_2468_, 1);
v___x_2470_ = 0;
v___x_2471_ = l_Lean_Meta_forallMetaTelescope(v_a_2469_, v___x_2470_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; lean_object* v_snd_2473_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2472_);
lean_dec_ref_known(v___x_2471_, 1);
v_snd_2473_ = lean_ctor_get(v_a_2472_, 1);
lean_inc(v_snd_2473_);
if (v___x_2367_ == 0)
{
lean_object* v_fst_2474_; lean_object* v_snd_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v_fst_2474_ = lean_ctor_get(v_a_2472_, 0);
lean_inc(v_fst_2474_);
lean_dec(v_a_2472_);
v_snd_2475_ = lean_ctor_get(v_snd_2473_, 1);
lean_inc(v_snd_2475_);
lean_dec(v_snd_2473_);
v___x_2476_ = lean_box(0);
lean_inc_ref(v_e_2041_);
lean_inc(v___x_2174_);
v___x_2477_ = l_Lean_Meta_rwMatcher___lam__3(v___x_2084_, v___x_2217_, v_fst_2474_, v___x_2174_, v_e_2041_, v___x_2082_, v_snd_2475_, v___x_2476_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
lean_dec(v_snd_2475_);
v___y_2421_ = v___x_2467_;
v___y_2422_ = v_a_2435_;
v___y_2423_ = v___x_2477_;
goto v___jp_2420_;
}
else
{
lean_object* v_fst_2478_; lean_object* v_snd_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2492_; 
v_fst_2478_ = lean_ctor_get(v_a_2472_, 0);
lean_inc(v_fst_2478_);
lean_dec(v_a_2472_);
v_snd_2479_ = lean_ctor_get(v_snd_2473_, 1);
v_isSharedCheck_2492_ = !lean_is_exclusive(v_snd_2473_);
if (v_isSharedCheck_2492_ == 0)
{
lean_object* v_unused_2493_; 
v_unused_2493_ = lean_ctor_get(v_snd_2473_, 0);
lean_dec(v_unused_2493_);
v___x_2481_ = v_snd_2473_;
v_isShared_2482_ = v_isSharedCheck_2492_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_snd_2479_);
lean_dec(v_snd_2473_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2492_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2486_; 
v___x_2483_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__27, &l_Lean_Meta_rwMatcher___closed__27_once, _init_l_Lean_Meta_rwMatcher___closed__27);
lean_inc(v_snd_2479_);
v___x_2484_ = l_Lean_indentExpr(v_snd_2479_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set_tag(v___x_2481_, 7);
lean_ctor_set(v___x_2481_, 1, v___x_2484_);
lean_ctor_set(v___x_2481_, 0, v___x_2483_);
v___x_2486_ = v___x_2481_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2483_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v___x_2484_);
v___x_2486_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
lean_object* v___x_2487_; 
v___x_2487_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(v___x_2175_, v___x_2486_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2488_; lean_object* v___x_2489_; 
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_a_2488_);
lean_dec_ref_known(v___x_2487_, 1);
lean_inc_ref(v_e_2041_);
lean_inc(v___x_2174_);
v___x_2489_ = l_Lean_Meta_rwMatcher___lam__3(v___x_2084_, v___x_2217_, v_fst_2478_, v___x_2174_, v_e_2041_, v___x_2082_, v_snd_2479_, v_a_2488_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
lean_dec(v_snd_2479_);
v___y_2421_ = v___x_2467_;
v___y_2422_ = v_a_2435_;
v___y_2423_ = v___x_2489_;
goto v___jp_2420_;
}
else
{
lean_object* v_a_2490_; 
lean_dec(v_snd_2479_);
lean_dec(v_fst_2478_);
lean_dec_ref(v___x_2217_);
v_a_2490_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_a_2490_);
lean_dec_ref_known(v___x_2487_, 1);
v___y_2416_ = v___x_2467_;
v___y_2417_ = v_a_2435_;
v_a_2418_ = v_a_2490_;
goto v___jp_2415_;
}
}
}
}
}
else
{
lean_object* v_a_2494_; 
lean_dec_ref(v___x_2217_);
v_a_2494_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2494_);
lean_dec_ref_known(v___x_2471_, 1);
v___y_2416_ = v___x_2467_;
v___y_2417_ = v_a_2435_;
v_a_2418_ = v_a_2494_;
goto v___jp_2415_;
}
}
else
{
lean_object* v_a_2495_; 
lean_dec_ref(v___x_2217_);
v_a_2495_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_a_2495_);
lean_dec_ref_known(v___x_2468_, 1);
v___y_2416_ = v___x_2467_;
v___y_2417_ = v_a_2435_;
v_a_2418_ = v_a_2495_;
goto v___jp_2415_;
}
}
}
}
v___jp_2176_:
{
uint8_t v___x_2178_; 
v___x_2178_ = l_Lean_Exception_isInterrupt(v_a_2177_);
if (v___x_2178_ == 0)
{
uint8_t v___x_2179_; 
lean_inc_ref(v_a_2177_);
v___x_2179_ = l_Lean_Exception_isRuntime(v_a_2177_);
if (v___x_2179_ == 0)
{
lean_del_object(v___x_2132_);
if (v_hasTrace_2172_ == 0)
{
lean_dec_ref(v_a_2177_);
lean_dec(v___x_2174_);
goto v___jp_2099_;
}
else
{
lean_object* v___x_2180_; uint8_t v___x_2181_; 
v___x_2180_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__11, &l_Lean_Meta_rwMatcher___closed__11_once, _init_l_Lean_Meta_rwMatcher___closed__11);
v___x_2181_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2171_, v_options_2170_, v___x_2180_);
if (v___x_2181_ == 0)
{
lean_dec_ref(v_a_2177_);
lean_dec(v___x_2174_);
goto v___jp_2099_;
}
else
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2182_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__21, &l_Lean_Meta_rwMatcher___closed__21_once, _init_l_Lean_Meta_rwMatcher___closed__21);
v___x_2183_ = l_Lean_MessageData_ofConstName(v___x_2174_, v___x_2082_);
v___x_2184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2182_);
lean_ctor_set(v___x_2184_, 1, v___x_2183_);
v___x_2185_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__23, &l_Lean_Meta_rwMatcher___closed__23_once, _init_l_Lean_Meta_rwMatcher___closed__23);
v___x_2186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2184_);
lean_ctor_set(v___x_2186_, 1, v___x_2185_);
v___x_2187_ = l_Lean_Exception_toMessageData(v_a_2177_);
v___x_2188_ = l_Lean_indentD(v___x_2187_);
v___x_2189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2186_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
v___x_2190_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(v___x_2175_, v___x_2189_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v___x_2192_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2191_);
lean_dec_ref_known(v___x_2190_, 1);
v___x_2192_ = l_Lean_Meta_rwMatcher___lam__0(v_e_2041_, v___x_2084_, v_a_2191_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
v___y_2069_ = v___x_2192_;
goto v___jp_2068_;
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_dec_ref(v_e_2041_);
v_a_2193_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2190_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2190_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
}
}
else
{
lean_object* v___x_2202_; 
lean_dec(v___x_2174_);
lean_dec_ref(v_e_2041_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set_tag(v___x_2132_, 1);
lean_ctor_set(v___x_2132_, 0, v_a_2177_);
v___x_2202_ = v___x_2132_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2177_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
else
{
lean_object* v___x_2205_; 
lean_dec(v___x_2174_);
lean_dec_ref(v_e_2041_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set_tag(v___x_2132_, 1);
lean_ctor_set(v___x_2132_, 0, v_a_2177_);
v___x_2205_ = v___x_2132_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2177_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
v___jp_2207_:
{
if (lean_obj_tag(v___y_2208_) == 0)
{
lean_dec(v___x_2174_);
lean_del_object(v___x_2132_);
lean_dec_ref(v_e_2041_);
return v___y_2208_;
}
else
{
lean_object* v_a_2209_; 
v_a_2209_ = lean_ctor_get(v___y_2208_, 0);
lean_inc(v_a_2209_);
lean_dec_ref_known(v___y_2208_, 1);
v_a_2177_ = v_a_2209_;
goto v___jp_2176_;
}
}
}
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
lean_dec(v___x_2128_);
lean_dec_ref(v___x_2127_);
lean_del_object(v___x_2105_);
lean_dec_ref(v_e_2041_);
lean_dec(v_altIdx_2040_);
v_a_2527_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2129_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2129_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
}
}
else
{
lean_dec(v_altIdx_2040_);
goto v___jp_2047_;
}
}
else
{
lean_dec(v_altIdx_2040_);
goto v___jp_2047_;
}
v___jp_2047_:
{
uint8_t v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = 1;
v___x_2049_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_e_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2059_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2052_ = v___x_2049_;
v_isShared_2053_ = v_isSharedCheck_2059_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2049_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2059_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2057_; 
v___x_2054_ = lean_box(0);
v___x_2055_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2055_, 0, v_a_2050_);
lean_ctor_set(v___x_2055_, 1, v___x_2054_);
lean_ctor_set_uint8(v___x_2055_, sizeof(void*)*2, v___x_2048_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 0, v___x_2055_);
v___x_2057_ = v___x_2052_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v___x_2055_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
v_a_2060_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2049_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2049_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
v___jp_2068_:
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2078_; 
v_a_2070_ = lean_ctor_get(v___y_2069_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___y_2069_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2072_ = v___y_2069_;
v_isShared_2073_ = v_isSharedCheck_2078_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___y_2069_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2078_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v_a_2074_; lean_object* v___x_2076_; 
v_a_2074_ = lean_ctor_get(v_a_2070_, 0);
lean_inc(v_a_2074_);
lean_dec(v_a_2070_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 0, v_a_2074_);
v___x_2076_ = v___x_2072_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2074_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___boxed(lean_object* v_altIdx_2536_, lean_object* v_e_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l_Lean_Meta_rwMatcher(v_altIdx_2536_, v_e_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_);
lean_dec(v_a_2541_);
lean_dec_ref(v_a_2540_);
lean_dec(v_a_2539_);
lean_dec_ref(v_a_2538_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__0(lean_object* v_inst_2544_, lean_object* v_a_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_){
_start:
{
lean_object* v___x_2551_; 
v___x_2551_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_a_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__0___boxed(lean_object* v_inst_2552_, lean_object* v_a_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__0(v_inst_2552_, v_a_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1(lean_object* v_mvarId_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v___x_2566_; 
v___x_2566_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1___redArg(v_mvarId_2560_, v___y_2562_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1___boxed(lean_object* v_mvarId_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1(v_mvarId_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
lean_dec(v_mvarId_2567_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6(lean_object* v_00_u03b1_2574_, lean_object* v_msg_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v___x_2581_; 
v___x_2581_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v_msg_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___boxed(lean_object* v_00_u03b1_2582_, lean_object* v_msg_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6(v_00_u03b1_2582_, v_msg_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15(lean_object* v_00_u03b1_2590_, lean_object* v_x_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___redArg(v_x_2591_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___boxed(lean_object* v_00_u03b1_2598_, lean_object* v_x_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15(v_00_u03b1_2598_, v_x_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
return v_res_2605_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1(lean_object* v_00_u03b2_2606_, lean_object* v_x_2607_, lean_object* v_x_2608_){
_start:
{
uint8_t v___x_2609_; 
v___x_2609_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1___redArg(v_x_2607_, v_x_2608_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2610_, lean_object* v_x_2611_, lean_object* v_x_2612_){
_start:
{
uint8_t v_res_2613_; lean_object* v_r_2614_; 
v_res_2613_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1(v_00_u03b2_2610_, v_x_2611_, v_x_2612_);
lean_dec(v_x_2612_);
lean_dec_ref(v_x_2611_);
v_r_2614_ = lean_box(v_res_2613_);
return v_r_2614_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6(lean_object* v_00_u03b2_2615_, lean_object* v_x_2616_, size_t v_x_2617_, lean_object* v_x_2618_){
_start:
{
uint8_t v___x_2619_; 
v___x_2619_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6___redArg(v_x_2616_, v_x_2617_, v_x_2618_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b2_2620_, lean_object* v_x_2621_, lean_object* v_x_2622_, lean_object* v_x_2623_){
_start:
{
size_t v_x_92976__boxed_2624_; uint8_t v_res_2625_; lean_object* v_r_2626_; 
v_x_92976__boxed_2624_ = lean_unbox_usize(v_x_2622_);
lean_dec(v_x_2622_);
v_res_2625_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6(v_00_u03b2_2620_, v_x_2621_, v_x_92976__boxed_2624_, v_x_2623_);
lean_dec(v_x_2623_);
lean_dec_ref(v_x_2621_);
v_r_2626_ = lean_box(v_res_2625_);
return v_r_2626_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6_spec__18(lean_object* v_00_u03b2_2627_, lean_object* v_keys_2628_, lean_object* v_vals_2629_, lean_object* v_heq_2630_, lean_object* v_i_2631_, lean_object* v_k_2632_){
_start:
{
uint8_t v___x_2633_; 
v___x_2633_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6_spec__18___redArg(v_keys_2628_, v_i_2631_, v_k_2632_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6_spec__18___boxed(lean_object* v_00_u03b2_2634_, lean_object* v_keys_2635_, lean_object* v_vals_2636_, lean_object* v_heq_2637_, lean_object* v_i_2638_, lean_object* v_k_2639_){
_start:
{
uint8_t v_res_2640_; lean_object* v_r_2641_; 
v_res_2640_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6_spec__18(v_00_u03b2_2634_, v_keys_2635_, v_vals_2636_, v_heq_2637_, v_i_2638_, v_k_2639_);
lean_dec(v_k_2639_);
lean_dec_ref(v_vals_2636_);
lean_dec_ref(v_keys_2635_);
v_r_2641_ = lean_box(v_res_2640_);
return v_r_2641_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
