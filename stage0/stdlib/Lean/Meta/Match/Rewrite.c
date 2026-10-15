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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Meta_isMatcherAppCore(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_trace_profiler;
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_100_ = l_Lean_mkConst(v___x_99_, v___x_81_);
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
lean_dec(v___x_81_);
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
lean_dec(v___x_81_);
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
v___x_133_ = l_Lean_mkConst(v___x_132_, v___x_81_);
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
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
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
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
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
v___x_188_ = l_Lean_mkConst(v___x_187_, v___x_165_);
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
lean_dec(v___x_165_);
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
lean_dec(v___x_165_);
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
v___x_225_ = l_Lean_mkConst(v___x_224_, v___x_165_);
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
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
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
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
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
lean_inc_ref(v_arg_67_);
v___x_261_ = l_Lean_Meta_mkEq(v_arg_67_, v___x_260_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
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
lean_dec(v___x_257_);
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
v___x_281_ = l_Lean_mkConst(v___x_280_, v___x_257_);
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
lean_dec(v___x_257_);
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
lean_dec(v___x_257_);
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
lean_dec(v___x_257_);
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
v___x_321_ = l_Lean_mkConst(v___x_320_, v___x_257_);
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
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
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
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
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
lean_dec_ref(v_arg_67_);
lean_dec_ref(v_arg_64_);
lean_dec_ref(v_arg_61_);
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
v___x_422_ = lean_st_ref_put(v___y_403_, v___x_421_);
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
uint8_t v___x_84075__boxed_538_; lean_object* v_res_539_; 
v___x_84075__boxed_538_ = lean_unbox(v___x_531_);
v_res_539_ = l_Lean_Meta_rwMatcher___lam__0(v_e_530_, v___x_84075__boxed_538_, v_____r_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
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
uint8_t v___y_84117__boxed_572_; lean_object* v_res_573_; 
v___y_84117__boxed_572_ = lean_unbox(v___y_564_);
v_res_573_ = l_Lean_Meta_rwMatcher___lam__1(v___x_563_, v___y_84117__boxed_572_, v_e_565_, v_x_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
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
lean_object* v___x_598_; lean_object* v_env_599_; uint8_t v___x_600_; lean_object* v_env_601_; lean_object* v___x_602_; lean_object* v_toCold_603_; lean_object* v_mctx_604_; lean_object* v_lctx_605_; lean_object* v_options_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_598_ = lean_st_ref_get(v___y_596_);
v_env_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc_ref(v_env_599_);
lean_dec(v___x_598_);
v___x_600_ = 0;
v_env_601_ = l_Lean_Environment_setRecordingDeps(v_env_599_, v___x_600_);
v___x_602_ = lean_st_ref_get(v___y_594_);
v_toCold_603_ = lean_ctor_get(v___y_595_, 0);
v_mctx_604_ = lean_ctor_get(v___x_602_, 0);
lean_inc_ref(v_mctx_604_);
lean_dec(v___x_602_);
v_lctx_605_ = lean_ctor_get(v___y_593_, 2);
v_options_606_ = lean_ctor_get(v_toCold_603_, 2);
lean_inc_ref(v_options_606_);
lean_inc_ref(v_lctx_605_);
v___x_607_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_607_, 0, v_env_601_);
lean_ctor_set(v___x_607_, 1, v_mctx_604_);
lean_ctor_set(v___x_607_, 2, v_lctx_605_);
lean_ctor_set(v___x_607_, 3, v_options_606_);
v___x_608_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
lean_ctor_set(v___x_608_, 1, v_msgData_592_);
v___x_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3___boxed(lean_object* v_msgData_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msgData_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(lean_object* v_msg_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_ref_623_; lean_object* v___x_624_; lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_633_; 
v_ref_623_ = lean_ctor_get(v___y_620_, 2);
v___x_624_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
v_a_625_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_633_ == 0)
{
v___x_627_ = v___x_624_;
v_isShared_628_ = v_isSharedCheck_633_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_624_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_633_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_631_; 
lean_inc(v_ref_623_);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v_ref_623_);
lean_ctor_set(v___x_629_, 1, v_a_625_);
if (v_isShared_628_ == 0)
{
lean_ctor_set_tag(v___x_627_, 1);
lean_ctor_set(v___x_627_, 0, v___x_629_);
v___x_631_ = v___x_627_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg___boxed(lean_object* v_msg_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v_msg_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
return v_res_640_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(lean_object* v_keys_641_, lean_object* v_i_642_, lean_object* v_k_643_){
_start:
{
lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_644_ = lean_array_get_size(v_keys_641_);
v___x_645_ = lean_nat_dec_lt(v_i_642_, v___x_644_);
if (v___x_645_ == 0)
{
lean_dec(v_i_642_);
return v___x_645_;
}
else
{
lean_object* v_k_x27_646_; uint8_t v___x_647_; 
v_k_x27_646_ = lean_array_fget_borrowed(v_keys_641_, v_i_642_);
v___x_647_ = l_Lean_instBEqMVarId_beq(v_k_643_, v_k_x27_646_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_unsigned_to_nat(1u);
v___x_649_ = lean_nat_add(v_i_642_, v___x_648_);
lean_dec(v_i_642_);
v_i_642_ = v___x_649_;
goto _start;
}
else
{
lean_dec(v_i_642_);
return v___x_645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg___boxed(lean_object* v_keys_651_, lean_object* v_i_652_, lean_object* v_k_653_){
_start:
{
uint8_t v_res_654_; lean_object* v_r_655_; 
v_res_654_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(v_keys_651_, v_i_652_, v_k_653_);
lean_dec(v_k_653_);
lean_dec_ref(v_keys_651_);
v_r_655_ = lean_box(v_res_654_);
return v_r_655_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(lean_object* v_x_656_, size_t v_x_657_, lean_object* v_x_658_){
_start:
{
if (lean_obj_tag(v_x_656_) == 0)
{
lean_object* v_es_659_; lean_object* v___x_660_; size_t v___x_661_; size_t v___x_662_; lean_object* v_j_663_; lean_object* v___x_664_; 
v_es_659_ = lean_ctor_get(v_x_656_, 0);
v___x_660_ = lean_box(2);
v___x_661_ = ((size_t)31ULL);
v___x_662_ = lean_usize_land(v_x_657_, v___x_661_);
v_j_663_ = lean_usize_to_nat(v___x_662_);
v___x_664_ = lean_array_get_borrowed(v___x_660_, v_es_659_, v_j_663_);
lean_dec(v_j_663_);
switch(lean_obj_tag(v___x_664_))
{
case 0:
{
lean_object* v_key_665_; uint8_t v___x_666_; 
v_key_665_ = lean_ctor_get(v___x_664_, 0);
v___x_666_ = l_Lean_instBEqMVarId_beq(v_x_658_, v_key_665_);
return v___x_666_;
}
case 1:
{
lean_object* v_node_667_; size_t v___x_668_; size_t v___x_669_; 
v_node_667_ = lean_ctor_get(v___x_664_, 0);
v___x_668_ = ((size_t)5ULL);
v___x_669_ = lean_usize_shift_right(v_x_657_, v___x_668_);
v_x_656_ = v_node_667_;
v_x_657_ = v___x_669_;
goto _start;
}
default: 
{
uint8_t v___x_671_; 
v___x_671_ = 0;
return v___x_671_;
}
}
}
else
{
lean_object* v_ks_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v_ks_672_ = lean_ctor_get(v_x_656_, 0);
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(v_ks_672_, v___x_673_, v_x_658_);
return v___x_674_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_675_, lean_object* v_x_676_, lean_object* v_x_677_){
_start:
{
size_t v_x_84252__boxed_678_; uint8_t v_res_679_; lean_object* v_r_680_; 
v_x_84252__boxed_678_ = lean_unbox_usize(v_x_676_);
lean_dec(v_x_676_);
v_res_679_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_675_, v_x_84252__boxed_678_, v_x_677_);
lean_dec(v_x_677_);
lean_dec_ref(v_x_675_);
v_r_680_ = lean_box(v_res_679_);
return v_r_680_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(lean_object* v_x_681_, lean_object* v_x_682_){
_start:
{
uint64_t v___x_683_; size_t v___x_684_; uint8_t v___x_685_; 
v___x_683_ = l_Lean_instHashableMVarId_hash(v_x_682_);
v___x_684_ = lean_uint64_to_usize(v___x_683_);
v___x_685_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_681_, v___x_684_, v_x_682_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg___boxed(lean_object* v_x_686_, lean_object* v_x_687_){
_start:
{
uint8_t v_res_688_; lean_object* v_r_689_; 
v_res_688_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_x_686_, v_x_687_);
lean_dec(v_x_687_);
lean_dec_ref(v_x_686_);
v_r_689_ = lean_box(v_res_688_);
return v_r_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(lean_object* v_mvarId_690_, lean_object* v___y_691_){
_start:
{
lean_object* v___x_693_; lean_object* v_mctx_694_; lean_object* v_eAssignment_695_; uint8_t v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_693_ = lean_st_ref_get(v___y_691_);
v_mctx_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc_ref(v_mctx_694_);
lean_dec(v___x_693_);
v_eAssignment_695_ = lean_ctor_get(v_mctx_694_, 8);
lean_inc_ref(v_eAssignment_695_);
lean_dec_ref(v_mctx_694_);
v___x_696_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_eAssignment_695_, v_mvarId_690_);
lean_dec_ref(v_eAssignment_695_);
v___x_697_ = lean_box(v___x_696_);
v___x_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg___boxed(lean_object* v_mvarId_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_mvarId_699_, v___y_700_);
lean_dec(v___y_700_);
lean_dec(v_mvarId_699_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(lean_object* v_as_703_, size_t v_i_704_, size_t v_stop_705_, lean_object* v_b_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_a_713_; uint8_t v___x_717_; 
v___x_717_ = lean_usize_dec_eq(v_i_704_, v_stop_705_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_721_; 
v___x_718_ = lean_array_uget_borrowed(v_as_703_, v_i_704_);
v___x_721_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v___x_718_, v___y_708_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; uint8_t v___x_723_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
lean_dec_ref_known(v___x_721_, 1);
v___x_723_ = lean_unbox(v_a_722_);
lean_dec(v_a_722_);
if (v___x_723_ == 0)
{
goto v___jp_719_;
}
else
{
v_a_713_ = v_b_706_;
goto v___jp_712_;
}
}
else
{
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_724_; uint8_t v___x_725_; 
v_a_724_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_724_);
lean_dec_ref_known(v___x_721_, 1);
v___x_725_ = lean_unbox(v_a_724_);
lean_dec(v_a_724_);
if (v___x_725_ == 0)
{
v_a_713_ = v_b_706_;
goto v___jp_712_;
}
else
{
goto v___jp_719_;
}
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
lean_dec_ref(v_b_706_);
v_a_726_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_721_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_721_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
v___jp_719_:
{
lean_object* v___x_720_; 
lean_inc(v___x_718_);
v___x_720_ = lean_array_push(v_b_706_, v___x_718_);
v_a_713_ = v___x_720_;
goto v___jp_712_;
}
}
else
{
lean_object* v___x_734_; 
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v_b_706_);
return v___x_734_;
}
v___jp_712_:
{
size_t v___x_714_; size_t v___x_715_; 
v___x_714_ = ((size_t)1ULL);
v___x_715_ = lean_usize_add(v_i_704_, v___x_714_);
v_i_704_ = v___x_715_;
v_b_706_ = v_a_713_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8___boxed(lean_object* v_as_735_, lean_object* v_i_736_, lean_object* v_stop_737_, lean_object* v_b_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
size_t v_i_boxed_744_; size_t v_stop_boxed_745_; lean_object* v_res_746_; 
v_i_boxed_744_ = lean_unbox_usize(v_i_736_);
lean_dec(v_i_736_);
v_stop_boxed_745_ = lean_unbox_usize(v_stop_737_);
lean_dec(v_stop_737_);
v_res_746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v_as_735_, v_i_boxed_744_, v_stop_boxed_745_, v_b_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec_ref(v_as_735_);
return v_res_746_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__0));
v___x_749_ = l_Lean_stringToMessageData(v___x_748_);
return v___x_749_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__2));
v___x_752_ = l_Lean_stringToMessageData(v___x_751_);
return v___x_752_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__4));
v___x_755_ = l_Lean_stringToMessageData(v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(lean_object* v_as_756_, size_t v_sz_757_, size_t v_i_758_, lean_object* v_b_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_a_766_; uint8_t v___x_770_; 
v___x_770_ = lean_usize_dec_lt(v_i_758_, v_sz_757_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; 
v___x_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_771_, 0, v_b_759_);
return v___x_771_;
}
else
{
lean_object* v___x_772_; lean_object* v___y_774_; lean_object* v___y_776_; lean_object* v___y_778_; lean_object* v_a_779_; lean_object* v___y_781_; lean_object* v___y_782_; uint8_t v___y_783_; lean_object* v___y_799_; lean_object* v___y_800_; uint8_t v___y_801_; lean_object* v___x_816_; 
v___x_772_ = lean_box(0);
v_a_779_ = lean_array_uget_borrowed(v_as_756_, v_i_758_);
v___x_816_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_a_779_, v___y_761_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; uint8_t v___x_818_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref_known(v___x_816_, 1);
v___x_818_ = lean_unbox(v_a_817_);
lean_dec(v_a_817_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; 
lean_inc(v_a_779_);
v___x_819_ = l_Lean_MVarId_getType(v_a_779_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; uint8_t v___x_821_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc_n(v_a_820_, 2);
lean_dec_ref_known(v___x_819_, 1);
v___x_821_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_a_820_);
if (v___x_821_ == 0)
{
uint8_t v___x_822_; 
v___x_822_ = l_Lean_Expr_isEq(v_a_820_);
if (v___x_822_ == 0)
{
uint8_t v___x_823_; 
v___x_823_ = l_Lean_Expr_isHEq(v_a_820_);
lean_dec(v_a_820_);
if (v___x_823_ == 0)
{
v_a_766_ = v___x_772_;
goto v___jp_765_;
}
else
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_Meta_saveState___redArg(v___y_761_, v___y_763_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_a_825_; lean_object* v___x_826_; 
v_a_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_a_825_);
lean_dec_ref_known(v___x_824_, 1);
lean_inc(v_a_779_);
v___x_826_ = l_Lean_MVarId_assumption(v_a_779_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_dec(v_a_825_);
v___y_776_ = v___x_826_;
goto v___jp_775_;
}
else
{
lean_object* v_a_827_; uint8_t v___y_829_; uint8_t v___x_845_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
v___x_845_ = l_Lean_Exception_isInterrupt(v_a_827_);
if (v___x_845_ == 0)
{
uint8_t v___x_846_; 
lean_inc(v_a_827_);
v___x_846_ = l_Lean_Exception_isRuntime(v_a_827_);
v___y_829_ = v___x_846_;
goto v___jp_828_;
}
else
{
v___y_829_ = v___x_845_;
goto v___jp_828_;
}
v___jp_828_:
{
if (v___y_829_ == 0)
{
lean_object* v___x_830_; 
lean_dec_ref_known(v___x_826_, 1);
v___x_830_ = l_Lean_Meta_SavedState_restore___redArg(v_a_825_, v___y_761_, v___y_763_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v___x_831_; 
lean_dec_ref_known(v___x_830_, 1);
v___x_831_ = l_Lean_Meta_saveState___redArg(v___y_761_, v___y_763_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; lean_object* v___x_833_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_832_);
lean_dec_ref_known(v___x_831_, 1);
lean_inc(v_a_779_);
v___x_833_ = l_Lean_MVarId_hrefl(v_a_779_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_dec(v_a_832_);
v___y_776_ = v___x_833_;
goto v___jp_775_;
}
else
{
lean_object* v_a_834_; uint8_t v___x_835_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
v___x_835_ = l_Lean_Exception_isInterrupt(v_a_834_);
if (v___x_835_ == 0)
{
uint8_t v___x_836_; 
lean_inc(v_a_834_);
v___x_836_ = l_Lean_Exception_isRuntime(v_a_834_);
v___y_799_ = v___x_833_;
v___y_800_ = v_a_832_;
v___y_801_ = v___x_836_;
goto v___jp_798_;
}
else
{
v___y_799_ = v___x_833_;
v___y_800_ = v_a_832_;
v___y_801_ = v___x_835_;
goto v___jp_798_;
}
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
v_a_837_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_831_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_831_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
else
{
v___y_776_ = v___x_830_;
goto v___jp_775_;
}
}
else
{
lean_dec(v_a_825_);
v___y_776_ = v___x_826_;
goto v___jp_775_;
}
}
}
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
v_a_847_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_824_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_824_);
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
}
else
{
lean_object* v___x_855_; 
lean_dec(v_a_820_);
v___x_855_ = l_Lean_Meta_saveState___redArg(v___y_761_, v___y_763_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_857_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref_known(v___x_855_, 1);
lean_inc(v_a_779_);
v___x_857_ = l_Lean_MVarId_assumption(v_a_779_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_dec(v_a_856_);
v___y_778_ = v___x_857_;
goto v___jp_777_;
}
else
{
lean_object* v_a_858_; uint8_t v___y_860_; uint8_t v___x_876_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
v___x_876_ = l_Lean_Exception_isInterrupt(v_a_858_);
if (v___x_876_ == 0)
{
uint8_t v___x_877_; 
lean_inc(v_a_858_);
v___x_877_ = l_Lean_Exception_isRuntime(v_a_858_);
v___y_860_ = v___x_877_;
goto v___jp_859_;
}
else
{
v___y_860_ = v___x_876_;
goto v___jp_859_;
}
v___jp_859_:
{
if (v___y_860_ == 0)
{
lean_object* v___x_861_; 
lean_dec_ref_known(v___x_857_, 1);
v___x_861_ = l_Lean_Meta_SavedState_restore___redArg(v_a_856_, v___y_761_, v___y_763_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v___x_862_; 
lean_dec_ref_known(v___x_861_, 1);
v___x_862_ = l_Lean_Meta_saveState___redArg(v___y_761_, v___y_763_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_864_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref_known(v___x_862_, 1);
lean_inc(v_a_779_);
v___x_864_ = l_Lean_MVarId_refl(v_a_779_, v___x_770_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_dec(v_a_863_);
v___y_778_ = v___x_864_;
goto v___jp_777_;
}
else
{
lean_object* v_a_865_; uint8_t v___x_866_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v___x_866_ = l_Lean_Exception_isInterrupt(v_a_865_);
if (v___x_866_ == 0)
{
uint8_t v___x_867_; 
lean_inc(v_a_865_);
v___x_867_ = l_Lean_Exception_isRuntime(v_a_865_);
v___y_781_ = v_a_863_;
v___y_782_ = v___x_864_;
v___y_783_ = v___x_867_;
goto v___jp_780_;
}
else
{
v___y_781_ = v_a_863_;
v___y_782_ = v___x_864_;
v___y_783_ = v___x_866_;
goto v___jp_780_;
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
v_a_868_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_862_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_862_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
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
v___y_778_ = v___x_861_;
goto v___jp_777_;
}
}
else
{
lean_dec(v_a_856_);
v___y_778_ = v___x_857_;
goto v___jp_777_;
}
}
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
v_a_878_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_855_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_855_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
}
else
{
lean_object* v___x_886_; 
lean_dec(v_a_820_);
v___x_886_ = l_Lean_Meta_saveState___redArg(v___y_761_, v___y_763_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v___x_888_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_887_);
lean_dec_ref_known(v___x_886_, 1);
lean_inc(v_a_779_);
v___x_888_ = l_Lean_MVarId_assumption(v_a_779_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_dec(v_a_887_);
v___y_774_ = v___x_888_;
goto v___jp_773_;
}
else
{
lean_object* v_a_889_; uint8_t v___y_891_; uint8_t v___x_906_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v___x_906_ = l_Lean_Exception_isInterrupt(v_a_889_);
if (v___x_906_ == 0)
{
uint8_t v___x_907_; 
lean_inc(v_a_889_);
v___x_907_ = l_Lean_Exception_isRuntime(v_a_889_);
v___y_891_ = v___x_907_;
goto v___jp_890_;
}
else
{
v___y_891_ = v___x_906_;
goto v___jp_890_;
}
v___jp_890_:
{
if (v___y_891_ == 0)
{
lean_object* v___x_892_; 
lean_dec_ref_known(v___x_888_, 1);
v___x_892_ = l_Lean_Meta_SavedState_restore___redArg(v_a_887_, v___y_761_, v___y_763_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_904_; 
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_904_ == 0)
{
lean_object* v_unused_905_; 
v_unused_905_ = lean_ctor_get(v___x_892_, 0);
lean_dec(v_unused_905_);
v___x_894_ = v___x_892_;
v_isShared_895_ = v_isSharedCheck_904_;
goto v_resetjp_893_;
}
else
{
lean_dec(v___x_892_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_904_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_896_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5);
lean_inc(v_a_779_);
if (v_isShared_895_ == 0)
{
lean_ctor_set_tag(v___x_894_, 1);
lean_ctor_set(v___x_894_, 0, v_a_779_);
v___x_898_ = v___x_894_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_779_);
v___x_898_ = v_reuseFailAlloc_903_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_896_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_899_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_902_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_901_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
v___y_774_ = v___x_902_;
goto v___jp_773_;
}
}
}
else
{
v___y_774_ = v___x_892_;
goto v___jp_773_;
}
}
else
{
lean_dec(v_a_887_);
v___y_774_ = v___x_888_;
goto v___jp_773_;
}
}
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
v_a_908_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_886_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_886_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
v_a_916_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_819_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_819_);
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
else
{
v_a_766_ = v___x_772_;
goto v___jp_765_;
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
v_a_924_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_816_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_816_);
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
v___jp_773_:
{
if (lean_obj_tag(v___y_774_) == 0)
{
lean_dec_ref_known(v___y_774_, 1);
v_a_766_ = v___x_772_;
goto v___jp_765_;
}
else
{
return v___y_774_;
}
}
v___jp_775_:
{
if (lean_obj_tag(v___y_776_) == 0)
{
lean_dec_ref_known(v___y_776_, 1);
v_a_766_ = v___x_772_;
goto v___jp_765_;
}
else
{
return v___y_776_;
}
}
v___jp_777_:
{
if (lean_obj_tag(v___y_778_) == 0)
{
lean_dec_ref_known(v___y_778_, 1);
v_a_766_ = v___x_772_;
goto v___jp_765_;
}
else
{
return v___y_778_;
}
}
v___jp_780_:
{
if (v___y_783_ == 0)
{
lean_object* v___x_784_; 
lean_dec_ref(v___y_782_);
v___x_784_ = l_Lean_Meta_SavedState_restore___redArg(v___y_781_, v___y_761_, v___y_763_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_796_; 
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; 
v_unused_797_ = lean_ctor_get(v___x_784_, 0);
lean_dec(v_unused_797_);
v___x_786_ = v___x_784_;
v_isShared_787_ = v_isSharedCheck_796_;
goto v_resetjp_785_;
}
else
{
lean_dec(v___x_784_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_796_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_788_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1);
lean_inc(v_a_779_);
if (v_isShared_787_ == 0)
{
lean_ctor_set_tag(v___x_786_, 1);
lean_ctor_set(v___x_786_, 0, v_a_779_);
v___x_790_ = v___x_786_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_779_);
v___x_790_ = v_reuseFailAlloc_795_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_788_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
v___x_792_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_791_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_793_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
v___y_778_ = v___x_794_;
goto v___jp_777_;
}
}
}
else
{
v___y_778_ = v___x_784_;
goto v___jp_777_;
}
}
else
{
lean_dec_ref(v___y_781_);
v___y_778_ = v___y_782_;
goto v___jp_777_;
}
}
v___jp_798_:
{
if (v___y_801_ == 0)
{
lean_object* v___x_802_; 
lean_dec_ref(v___y_799_);
v___x_802_ = l_Lean_Meta_SavedState_restore___redArg(v___y_800_, v___y_761_, v___y_763_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_814_; 
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; 
v_unused_815_ = lean_ctor_get(v___x_802_, 0);
lean_dec(v_unused_815_);
v___x_804_ = v___x_802_;
v_isShared_805_ = v_isSharedCheck_814_;
goto v_resetjp_803_;
}
else
{
lean_dec(v___x_802_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_814_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_808_; 
v___x_806_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1);
lean_inc(v_a_779_);
if (v_isShared_805_ == 0)
{
lean_ctor_set_tag(v___x_804_, 1);
lean_ctor_set(v___x_804_, 0, v_a_779_);
v___x_808_ = v___x_804_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_779_);
v___x_808_ = v_reuseFailAlloc_813_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_806_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_809_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_811_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
v___y_776_ = v___x_812_;
goto v___jp_775_;
}
}
}
else
{
v___y_776_ = v___x_802_;
goto v___jp_775_;
}
}
else
{
lean_dec_ref(v___y_800_);
v___y_776_ = v___y_799_;
goto v___jp_775_;
}
}
}
v___jp_765_:
{
size_t v___x_767_; size_t v___x_768_; 
v___x_767_ = ((size_t)1ULL);
v___x_768_ = lean_usize_add(v_i_758_, v___x_767_);
v_i_758_ = v___x_768_;
v_b_759_ = v_a_766_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___boxed(lean_object* v_as_932_, lean_object* v_sz_933_, lean_object* v_i_934_, lean_object* v_b_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
size_t v_sz_boxed_941_; size_t v_i_boxed_942_; lean_object* v_res_943_; 
v_sz_boxed_941_ = lean_unbox_usize(v_sz_933_);
lean_dec(v_sz_933_);
v_i_boxed_942_ = lean_unbox_usize(v_i_934_);
lean_dec(v_i_934_);
v_res_943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v_as_932_, v_sz_boxed_941_, v_i_boxed_942_, v_b_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec_ref(v_as_932_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
if (lean_obj_tag(v_a_944_) == 0)
{
lean_object* v___x_946_; 
v___x_946_ = l_List_reverse___redArg(v_a_945_);
return v___x_946_;
}
else
{
lean_object* v_head_947_; lean_object* v_tail_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_957_; 
v_head_947_ = lean_ctor_get(v_a_944_, 0);
v_tail_948_ = lean_ctor_get(v_a_944_, 1);
v_isSharedCheck_957_ = !lean_is_exclusive(v_a_944_);
if (v_isSharedCheck_957_ == 0)
{
v___x_950_ = v_a_944_;
v_isShared_951_ = v_isSharedCheck_957_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_tail_948_);
lean_inc(v_head_947_);
lean_dec(v_a_944_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_957_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; lean_object* v___x_954_; 
v___x_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_952_, 0, v_head_947_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 1, v_a_945_);
lean_ctor_set(v___x_950_, 0, v___x_952_);
v___x_954_ = v___x_950_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_952_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_a_945_);
v___x_954_ = v_reuseFailAlloc_956_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
v_a_944_ = v_tail_948_;
v_a_945_ = v___x_954_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__1(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__0));
v___x_960_ = l_Lean_stringToMessageData(v___x_959_);
return v___x_960_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__3(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__2));
v___x_963_ = l_Lean_stringToMessageData(v___x_962_);
return v___x_963_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__5(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__4));
v___x_966_ = l_Lean_stringToMessageData(v___x_965_);
return v___x_966_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__7(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__6));
v___x_969_ = l_Lean_stringToMessageData(v___x_968_);
return v___x_969_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__9(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__8));
v___x_972_ = l_Lean_stringToMessageData(v___x_971_);
return v___x_972_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__12(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__11));
v___x_977_ = l_Lean_stringToMessageData(v___x_976_);
return v___x_977_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__14(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__13));
v___x_980_ = l_Lean_stringToMessageData(v___x_979_);
return v___x_980_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__16(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__15));
v___x_983_ = l_Lean_stringToMessageData(v___x_982_);
return v___x_983_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__22(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__21));
v___x_992_ = l_Lean_stringToMessageData(v___x_991_);
return v___x_992_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__24(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__23));
v___x_995_ = l_Lean_stringToMessageData(v___x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2(uint8_t v___x_996_, lean_object* v___x_997_, lean_object* v_fst_998_, lean_object* v___x_999_, lean_object* v_e_1000_, uint8_t v___y_1001_, lean_object* v_snd_1002_, lean_object* v_____r_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v___y_1010_; lean_object* v_proof_1011_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; uint8_t v___y_1036_; lean_object* v___x_1048_; uint8_t v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; uint8_t v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v_a_1072_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; uint8_t v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; size_t v_sz_1112_; size_t v___x_1113_; lean_object* v___x_1114_; uint8_t v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; uint8_t v_fst_1143_; lean_object* v_fst_1144_; lean_object* v_snd_1145_; lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1048_ = l_Lean_mkAppN(v___x_997_, v_fst_998_);
v_sz_1112_ = lean_array_size(v_fst_998_);
v___x_1113_ = ((size_t)0ULL);
v___x_1114_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_1112_, v___x_1113_, v_fst_998_);
v___x_1179_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1180_ = lean_unsigned_to_nat(4u);
v___x_1181_ = l_Lean_Expr_isAppOfArity(v_snd_1002_, v___x_1179_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; 
v___x_1182_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1183_ = lean_unsigned_to_nat(3u);
v___x_1184_ = l_Lean_Expr_isAppOfArity(v_snd_1002_, v___x_1182_, v___x_1183_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
lean_dec_ref(v___x_1114_);
lean_dec_ref(v___x_1048_);
lean_dec_ref(v_e_1000_);
v___x_1185_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1186_ = l_Lean_MessageData_ofConstName(v___x_999_, v___y_1001_);
v___x_1187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1185_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v___x_1188_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1187_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
v___x_1190_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1189_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
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
v___x_1199_ = l_Lean_Expr_appFn_x21(v_snd_1002_);
v___x_1200_ = l_Lean_Expr_appArg_x21(v___x_1199_);
lean_dec_ref(v___x_1199_);
v___x_1201_ = l_Lean_Expr_appArg_x21(v_snd_1002_);
v_fst_1143_ = v___y_1001_;
v_fst_1144_ = v___x_1200_;
v_snd_1145_ = v___x_1201_;
goto v___jp_1142_;
}
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1202_ = l_Lean_Expr_appFn_x21(v_snd_1002_);
v___x_1203_ = l_Lean_Expr_appFn_x21(v___x_1202_);
lean_dec_ref(v___x_1202_);
v___x_1204_ = l_Lean_Expr_appArg_x21(v___x_1203_);
lean_dec_ref(v___x_1203_);
v___x_1205_ = l_Lean_Expr_appArg_x21(v_snd_1002_);
v_fst_1143_ = v___x_996_;
v_fst_1144_ = v___x_1204_;
v_snd_1145_ = v___x_1205_;
goto v___jp_1142_;
}
v___jp_1009_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1012_, 0, v_proof_1011_);
v___x_1013_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1013_, 0, v___y_1010_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
lean_ctor_set_uint8(v___x_1013_, sizeof(void*)*2, v___x_996_);
v___x_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
return v___x_1014_;
}
v___jp_1015_:
{
if (lean_obj_tag(v___y_1017_) == 0)
{
lean_object* v_a_1018_; 
v_a_1018_ = lean_ctor_get(v___y_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref_known(v___y_1017_, 1);
v___y_1010_ = v___y_1016_;
v_proof_1011_ = v_a_1018_;
goto v___jp_1009_;
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec_ref(v___y_1016_);
v_a_1019_ = lean_ctor_get(v___y_1017_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___y_1017_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___y_1017_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___y_1017_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
v___jp_1027_:
{
if (v___y_1036_ == 0)
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_dec_ref(v___y_1029_);
v___x_1037_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1038_ = l_Lean_MessageData_ofExpr(v___y_1028_);
v___x_1039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1039_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = l_Lean_Exception_toMessageData(v___y_1035_);
v___x_1043_ = l_Lean_indentD(v___x_1042_);
v___x_1044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1041_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v___x_1045_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1046_, v___y_1034_, v___y_1032_, v___y_1031_, v___y_1033_);
v___y_1016_ = v___y_1030_;
v___y_1017_ = v___x_1047_;
goto v___jp_1015_;
}
else
{
lean_dec_ref(v___y_1035_);
lean_dec_ref(v___y_1028_);
v___y_1016_ = v___y_1030_;
v___y_1017_ = v___y_1029_;
goto v___jp_1015_;
}
}
v___jp_1049_:
{
lean_object* v___x_1056_; lean_object* v_a_1057_; lean_object* v___x_1058_; 
v___x_1056_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_1051_, v___y_1053_);
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1057_);
lean_dec_ref(v___x_1056_);
v___x_1058_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___x_1048_, v___y_1053_);
if (v___y_1050_ == 0)
{
lean_object* v_a_1059_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_a_1059_);
lean_dec_ref(v___x_1058_);
v___y_1010_ = v_a_1057_;
v_proof_1011_ = v_a_1059_;
goto v___jp_1009_;
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1061_; 
v_a_1060_ = lean_ctor_get(v___x_1058_, 0);
lean_inc_n(v_a_1060_, 2);
lean_dec_ref(v___x_1058_);
v___x_1061_ = l_Lean_Meta_mkEqOfHEq(v_a_1060_, v___x_996_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_dec(v_a_1060_);
v___y_1016_ = v_a_1057_;
v___y_1017_ = v___x_1061_;
goto v___jp_1015_;
}
else
{
lean_object* v_a_1062_; uint8_t v___x_1063_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_a_1062_);
v___x_1063_ = l_Lean_Exception_isInterrupt(v_a_1062_);
if (v___x_1063_ == 0)
{
uint8_t v___x_1064_; 
lean_inc(v_a_1062_);
v___x_1064_ = l_Lean_Exception_isRuntime(v_a_1062_);
v___y_1028_ = v_a_1060_;
v___y_1029_ = v___x_1061_;
v___y_1030_ = v_a_1057_;
v___y_1031_ = v___y_1054_;
v___y_1032_ = v___y_1053_;
v___y_1033_ = v___y_1055_;
v___y_1034_ = v___y_1052_;
v___y_1035_ = v_a_1062_;
v___y_1036_ = v___x_1064_;
goto v___jp_1027_;
}
else
{
v___y_1028_ = v_a_1060_;
v___y_1029_ = v___x_1061_;
v___y_1030_ = v_a_1057_;
v___y_1031_ = v___y_1054_;
v___y_1032_ = v___y_1053_;
v___y_1033_ = v___y_1055_;
v___y_1034_ = v___y_1052_;
v___y_1035_ = v_a_1062_;
v___y_1036_ = v___x_1063_;
goto v___jp_1027_;
}
}
}
}
v___jp_1065_:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1073_ = lean_array_get_size(v_a_1072_);
v___x_1074_ = lean_unsigned_to_nat(0u);
v___x_1075_ = lean_nat_dec_eq(v___x_1073_, v___x_1074_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec_ref(v___y_1070_);
lean_dec_ref(v___x_1048_);
v___x_1076_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1077_ = l_Lean_MessageData_ofConstName(v___x_999_, v___x_1075_);
v___x_1078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1076_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_array_to_list(v_a_1072_);
v___x_1082_ = lean_box(0);
v___x_1083_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_1081_, v___x_1082_);
v___x_1084_ = l_Lean_MessageData_ofList(v___x_1083_);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1080_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1085_, v___y_1068_, v___y_1067_, v___y_1066_, v___y_1071_);
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1086_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
else
{
lean_dec_ref(v_a_1072_);
lean_dec(v___x_999_);
v___y_1050_ = v___y_1069_;
v___y_1051_ = v___y_1070_;
v___y_1052_ = v___y_1068_;
v___y_1053_ = v___y_1067_;
v___y_1054_ = v___y_1066_;
v___y_1055_ = v___y_1071_;
goto v___jp_1049_;
}
}
v___jp_1095_:
{
if (lean_obj_tag(v___y_1102_) == 0)
{
lean_object* v_a_1103_; 
v_a_1103_ = lean_ctor_get(v___y_1102_, 0);
lean_inc(v_a_1103_);
lean_dec_ref_known(v___y_1102_, 1);
v___y_1066_ = v___y_1096_;
v___y_1067_ = v___y_1098_;
v___y_1068_ = v___y_1097_;
v___y_1069_ = v___y_1099_;
v___y_1070_ = v___y_1101_;
v___y_1071_ = v___y_1100_;
v_a_1072_ = v_a_1103_;
goto v___jp_1065_;
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_dec_ref(v___y_1101_);
lean_dec_ref(v___x_1048_);
lean_dec(v___x_999_);
v_a_1104_ = lean_ctor_get(v___y_1102_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___y_1102_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___y_1102_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___y_1102_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
v___jp_1115_:
{
lean_object* v___x_1122_; size_t v_sz_1123_; lean_object* v___x_1124_; 
v___x_1122_ = lean_box(0);
v_sz_1123_ = lean_array_size(v___x_1114_);
v___x_1124_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1114_, v_sz_1123_, v___x_1113_, v___x_1122_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; 
lean_dec_ref_known(v___x_1124_, 1);
v___x_1125_ = lean_unsigned_to_nat(0u);
v___x_1126_ = lean_array_get_size(v___x_1114_);
v___x_1127_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1128_ = lean_nat_dec_lt(v___x_1125_, v___x_1126_);
if (v___x_1128_ == 0)
{
lean_dec_ref(v___x_1114_);
v___y_1066_ = v___y_1120_;
v___y_1067_ = v___y_1119_;
v___y_1068_ = v___y_1118_;
v___y_1069_ = v___y_1116_;
v___y_1070_ = v___y_1117_;
v___y_1071_ = v___y_1121_;
v_a_1072_ = v___x_1127_;
goto v___jp_1065_;
}
else
{
uint8_t v___x_1129_; 
v___x_1129_ = lean_nat_dec_le(v___x_1126_, v___x_1126_);
if (v___x_1129_ == 0)
{
if (v___x_1128_ == 0)
{
lean_dec_ref(v___x_1114_);
v___y_1066_ = v___y_1120_;
v___y_1067_ = v___y_1119_;
v___y_1068_ = v___y_1118_;
v___y_1069_ = v___y_1116_;
v___y_1070_ = v___y_1117_;
v___y_1071_ = v___y_1121_;
v_a_1072_ = v___x_1127_;
goto v___jp_1065_;
}
else
{
size_t v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_usize_of_nat(v___x_1126_);
v___x_1131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1114_, v___x_1113_, v___x_1130_, v___x_1127_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
lean_dec_ref(v___x_1114_);
v___y_1096_ = v___y_1120_;
v___y_1097_ = v___y_1118_;
v___y_1098_ = v___y_1119_;
v___y_1099_ = v___y_1116_;
v___y_1100_ = v___y_1121_;
v___y_1101_ = v___y_1117_;
v___y_1102_ = v___x_1131_;
goto v___jp_1095_;
}
}
else
{
size_t v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = lean_usize_of_nat(v___x_1126_);
v___x_1133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1114_, v___x_1113_, v___x_1132_, v___x_1127_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
lean_dec_ref(v___x_1114_);
v___y_1096_ = v___y_1120_;
v___y_1097_ = v___y_1118_;
v___y_1098_ = v___y_1119_;
v___y_1099_ = v___y_1116_;
v___y_1100_ = v___y_1121_;
v___y_1101_ = v___y_1117_;
v___y_1102_ = v___x_1133_;
goto v___jp_1095_;
}
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec_ref(v___y_1117_);
lean_dec_ref(v___x_1114_);
lean_dec_ref(v___x_1048_);
lean_dec(v___x_999_);
v_a_1134_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1124_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1124_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
v___jp_1142_:
{
lean_object* v___x_1146_; 
lean_inc_ref(v_fst_1144_);
lean_inc_ref(v_e_1000_);
v___x_1146_ = l_Lean_Meta_isExprDefEq(v_e_1000_, v_fst_1144_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; uint8_t v___x_1148_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref_known(v___x_1146_, 1);
v___x_1148_ = lean_unbox(v_a_1147_);
lean_dec(v_a_1147_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
lean_dec_ref(v_snd_1145_);
lean_dec_ref(v___x_1114_);
lean_dec_ref(v___x_1048_);
v___x_1149_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1150_ = l_Lean_MessageData_ofExpr(v_fst_1144_);
v___x_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1149_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1151_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = l_Lean_MessageData_ofConstName(v___x_999_, v___y_1001_);
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
v___x_1160_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1159_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v___x_1162_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1161_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
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
else
{
lean_dec_ref(v_fst_1144_);
lean_dec_ref(v_e_1000_);
v___y_1116_ = v_fst_1143_;
v___y_1117_ = v_snd_1145_;
v___y_1118_ = v___y_1004_;
v___y_1119_ = v___y_1005_;
v___y_1120_ = v___y_1006_;
v___y_1121_ = v___y_1007_;
goto v___jp_1115_;
}
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
lean_dec_ref(v_snd_1145_);
lean_dec_ref(v_fst_1144_);
lean_dec_ref(v___x_1114_);
lean_dec_ref(v___x_1048_);
lean_dec_ref(v_e_1000_);
lean_dec(v___x_999_);
v_a_1171_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1146_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1146_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2___boxed(lean_object* v___x_1206_, lean_object* v___x_1207_, lean_object* v_fst_1208_, lean_object* v___x_1209_, lean_object* v_e_1210_, lean_object* v___y_1211_, lean_object* v_snd_1212_, lean_object* v_____r_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
uint8_t v___x_84890__boxed_1219_; uint8_t v___y_84894__boxed_1220_; lean_object* v_res_1221_; 
v___x_84890__boxed_1219_ = lean_unbox(v___x_1206_);
v___y_84894__boxed_1220_ = lean_unbox(v___y_1211_);
v_res_1221_ = l_Lean_Meta_rwMatcher___lam__2(v___x_84890__boxed_1219_, v___x_1207_, v_fst_1208_, v___x_1209_, v_e_1210_, v___y_84894__boxed_1220_, v_snd_1212_, v_____r_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec_ref(v_snd_1212_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3(uint8_t v___x_1222_, lean_object* v___x_1223_, lean_object* v_fst_1224_, lean_object* v___x_1225_, lean_object* v_e_1226_, uint8_t v___y_1227_, lean_object* v_snd_1228_, lean_object* v_____r_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v___y_1236_; lean_object* v_proof_1237_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; uint8_t v___y_1262_; lean_object* v___x_1274_; lean_object* v___y_1276_; uint8_t v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; uint8_t v___y_1297_; lean_object* v_a_1298_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; uint8_t v___y_1327_; lean_object* v___y_1328_; size_t v_sz_1338_; size_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___y_1342_; uint8_t v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; uint8_t v_fst_1369_; lean_object* v_fst_1370_; lean_object* v_snd_1371_; lean_object* v___x_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v___x_1274_ = l_Lean_mkAppN(v___x_1223_, v_fst_1224_);
v_sz_1338_ = lean_array_size(v_fst_1224_);
v___x_1339_ = ((size_t)0ULL);
v___x_1340_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_1338_, v___x_1339_, v_fst_1224_);
v___x_1405_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1406_ = lean_unsigned_to_nat(4u);
v___x_1407_ = l_Lean_Expr_isAppOfArity(v_snd_1228_, v___x_1405_, v___x_1406_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1408_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1409_ = lean_unsigned_to_nat(3u);
v___x_1410_ = l_Lean_Expr_isAppOfArity(v_snd_1228_, v___x_1408_, v___x_1409_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_dec_ref(v___x_1340_);
lean_dec_ref(v___x_1274_);
lean_dec_ref(v_e_1226_);
v___x_1411_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1412_ = l_Lean_MessageData_ofConstName(v___x_1225_, v___y_1227_);
v___x_1413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1411_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
v___x_1414_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1413_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
v___x_1416_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1415_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1416_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1416_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
else
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1425_ = l_Lean_Expr_appFn_x21(v_snd_1228_);
v___x_1426_ = l_Lean_Expr_appArg_x21(v___x_1425_);
lean_dec_ref(v___x_1425_);
v___x_1427_ = l_Lean_Expr_appArg_x21(v_snd_1228_);
v_fst_1369_ = v___y_1227_;
v_fst_1370_ = v___x_1426_;
v_snd_1371_ = v___x_1427_;
goto v___jp_1368_;
}
}
else
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1428_ = l_Lean_Expr_appFn_x21(v_snd_1228_);
v___x_1429_ = l_Lean_Expr_appFn_x21(v___x_1428_);
lean_dec_ref(v___x_1428_);
v___x_1430_ = l_Lean_Expr_appArg_x21(v___x_1429_);
lean_dec_ref(v___x_1429_);
v___x_1431_ = l_Lean_Expr_appArg_x21(v_snd_1228_);
v_fst_1369_ = v___x_1222_;
v_fst_1370_ = v___x_1430_;
v_snd_1371_ = v___x_1431_;
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
lean_dec_ref(v___y_1258_);
v___x_1263_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1264_ = l_Lean_MessageData_ofExpr(v___y_1255_);
v___x_1265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1263_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
v___x_1266_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1265_);
lean_ctor_set(v___x_1267_, 1, v___x_1266_);
v___x_1268_ = l_Lean_Exception_toMessageData(v___y_1260_);
v___x_1269_ = l_Lean_indentD(v___x_1268_);
v___x_1270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1267_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
v___x_1271_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1270_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
v___x_1273_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1272_, v___y_1259_, v___y_1261_, v___y_1257_, v___y_1254_);
v___y_1242_ = v___y_1256_;
v___y_1243_ = v___x_1273_;
goto v___jp_1241_;
}
else
{
lean_dec_ref(v___y_1260_);
lean_dec_ref(v___y_1255_);
v___y_1242_ = v___y_1256_;
v___y_1243_ = v___y_1258_;
goto v___jp_1241_;
}
}
v___jp_1275_:
{
lean_object* v___x_1282_; lean_object* v_a_1283_; lean_object* v___x_1284_; 
v___x_1282_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_1276_, v___y_1279_);
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
lean_dec_ref(v___x_1282_);
v___x_1284_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___x_1274_, v___y_1279_);
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
v___y_1254_ = v___y_1281_;
v___y_1255_ = v_a_1286_;
v___y_1256_ = v_a_1283_;
v___y_1257_ = v___y_1280_;
v___y_1258_ = v___x_1287_;
v___y_1259_ = v___y_1278_;
v___y_1260_ = v_a_1288_;
v___y_1261_ = v___y_1279_;
v___y_1262_ = v___x_1290_;
goto v___jp_1253_;
}
else
{
v___y_1254_ = v___y_1281_;
v___y_1255_ = v_a_1286_;
v___y_1256_ = v_a_1283_;
v___y_1257_ = v___y_1280_;
v___y_1258_ = v___x_1287_;
v___y_1259_ = v___y_1278_;
v___y_1260_ = v_a_1288_;
v___y_1261_ = v___y_1279_;
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
v___x_1303_ = l_Lean_MessageData_ofConstName(v___x_1225_, v___x_1301_);
v___x_1304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1302_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
v___x_1305_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1304_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
v___x_1307_ = lean_array_to_list(v_a_1298_);
v___x_1308_ = lean_box(0);
v___x_1309_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_1307_, v___x_1308_);
v___x_1310_ = l_Lean_MessageData_ofList(v___x_1309_);
v___x_1311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1306_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
v___x_1312_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1311_, v___y_1296_, v___y_1295_, v___y_1294_, v___y_1292_);
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
v___y_1277_ = v___y_1297_;
v___y_1278_ = v___y_1296_;
v___y_1279_ = v___y_1295_;
v___y_1280_ = v___y_1294_;
v___y_1281_ = v___y_1292_;
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
v___y_1293_ = v___y_1325_;
v___y_1294_ = v___y_1324_;
v___y_1295_ = v___y_1323_;
v___y_1296_ = v___y_1326_;
v___y_1297_ = v___y_1327_;
v_a_1298_ = v_a_1329_;
goto v___jp_1291_;
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_dec_ref(v___y_1325_);
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
v___x_1350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1340_, v_sz_1349_, v___x_1339_, v___x_1348_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
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
v___y_1292_ = v___y_1347_;
v___y_1293_ = v___y_1342_;
v___y_1294_ = v___y_1346_;
v___y_1295_ = v___y_1345_;
v___y_1296_ = v___y_1344_;
v___y_1297_ = v___y_1343_;
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
v___y_1292_ = v___y_1347_;
v___y_1293_ = v___y_1342_;
v___y_1294_ = v___y_1346_;
v___y_1295_ = v___y_1345_;
v___y_1296_ = v___y_1344_;
v___y_1297_ = v___y_1343_;
v_a_1298_ = v___x_1353_;
goto v___jp_1291_;
}
else
{
size_t v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_usize_of_nat(v___x_1352_);
v___x_1357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1340_, v___x_1339_, v___x_1356_, v___x_1353_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
lean_dec_ref(v___x_1340_);
v___y_1322_ = v___y_1347_;
v___y_1323_ = v___y_1345_;
v___y_1324_ = v___y_1346_;
v___y_1325_ = v___y_1342_;
v___y_1326_ = v___y_1344_;
v___y_1327_ = v___y_1343_;
v___y_1328_ = v___x_1357_;
goto v___jp_1321_;
}
}
else
{
size_t v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = lean_usize_of_nat(v___x_1352_);
v___x_1359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1340_, v___x_1339_, v___x_1358_, v___x_1353_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
lean_dec_ref(v___x_1340_);
v___y_1322_ = v___y_1347_;
v___y_1323_ = v___y_1345_;
v___y_1324_ = v___y_1346_;
v___y_1325_ = v___y_1342_;
v___y_1326_ = v___y_1344_;
v___y_1327_ = v___y_1343_;
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
lean_inc_ref(v_e_1226_);
v___x_1372_ = l_Lean_Meta_isExprDefEq(v_e_1226_, v_fst_1370_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; uint8_t v___x_1374_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1373_);
lean_dec_ref_known(v___x_1372_, 1);
v___x_1374_ = lean_unbox(v_a_1373_);
lean_dec(v_a_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_dec_ref(v_snd_1371_);
lean_dec_ref(v___x_1340_);
lean_dec_ref(v___x_1274_);
v___x_1375_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1376_ = l_Lean_MessageData_ofExpr(v_fst_1370_);
v___x_1377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1375_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
v___x_1378_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1377_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
v___x_1380_ = l_Lean_MessageData_ofConstName(v___x_1225_, v___y_1227_);
v___x_1381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1379_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1381_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
v___x_1384_ = l_Lean_MessageData_ofExpr(v_e_1226_);
v___x_1385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1383_);
lean_ctor_set(v___x_1385_, 1, v___x_1384_);
v___x_1386_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_1387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1385_);
lean_ctor_set(v___x_1387_, 1, v___x_1386_);
v___x_1388_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1387_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1388_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1388_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
else
{
lean_dec_ref(v_fst_1370_);
lean_dec_ref(v_e_1226_);
v___y_1342_ = v_snd_1371_;
v___y_1343_ = v_fst_1369_;
v___y_1344_ = v___y_1230_;
v___y_1345_ = v___y_1231_;
v___y_1346_ = v___y_1232_;
v___y_1347_ = v___y_1233_;
goto v___jp_1341_;
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
lean_dec_ref(v_snd_1371_);
lean_dec_ref(v_fst_1370_);
lean_dec_ref(v___x_1340_);
lean_dec_ref(v___x_1274_);
lean_dec_ref(v_e_1226_);
lean_dec(v___x_1225_);
v_a_1397_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1372_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1372_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3___boxed(lean_object* v___x_1432_, lean_object* v___x_1433_, lean_object* v_fst_1434_, lean_object* v___x_1435_, lean_object* v_e_1436_, lean_object* v___y_1437_, lean_object* v_snd_1438_, lean_object* v_____r_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
uint8_t v___x_85400__boxed_1445_; uint8_t v___y_85404__boxed_1446_; lean_object* v_res_1447_; 
v___x_85400__boxed_1445_ = lean_unbox(v___x_1432_);
v___y_85404__boxed_1446_ = lean_unbox(v___y_1437_);
v_res_1447_ = l_Lean_Meta_rwMatcher___lam__3(v___x_85400__boxed_1445_, v___x_1433_, v_fst_1434_, v___x_1435_, v_e_1436_, v___y_85404__boxed_1446_, v_snd_1438_, v_____r_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec_ref(v_snd_1438_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4(uint8_t v___x_1448_, lean_object* v___x_1449_, lean_object* v_fst_1450_, lean_object* v___x_1451_, lean_object* v_e_1452_, uint8_t v___y_1453_, lean_object* v_snd_1454_, lean_object* v_____r_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v___y_1462_; lean_object* v_proof_1463_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; uint8_t v___y_1488_; lean_object* v___x_1500_; lean_object* v___y_1502_; uint8_t v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; uint8_t v___y_1523_; lean_object* v_a_1524_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; uint8_t v___y_1553_; lean_object* v___y_1554_; size_t v_sz_1564_; size_t v___x_1565_; lean_object* v___x_1566_; lean_object* v___y_1568_; uint8_t v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; uint8_t v_fst_1595_; lean_object* v_fst_1596_; lean_object* v_snd_1597_; lean_object* v___x_1631_; lean_object* v___x_1632_; uint8_t v___x_1633_; 
v___x_1500_ = l_Lean_mkAppN(v___x_1449_, v_fst_1450_);
v_sz_1564_ = lean_array_size(v_fst_1450_);
v___x_1565_ = ((size_t)0ULL);
v___x_1566_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_1564_, v___x_1565_, v_fst_1450_);
v___x_1631_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1632_ = lean_unsigned_to_nat(4u);
v___x_1633_ = l_Lean_Expr_isAppOfArity(v_snd_1454_, v___x_1631_, v___x_1632_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1634_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1635_ = lean_unsigned_to_nat(3u);
v___x_1636_ = l_Lean_Expr_isAppOfArity(v_snd_1454_, v___x_1634_, v___x_1635_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
lean_dec_ref(v___x_1566_);
lean_dec_ref(v___x_1500_);
lean_dec_ref(v_e_1452_);
v___x_1637_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1638_ = l_Lean_MessageData_ofConstName(v___x_1451_, v___y_1453_);
v___x_1639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1637_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1639_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v___x_1642_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1641_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1651_ = l_Lean_Expr_appFn_x21(v_snd_1454_);
v___x_1652_ = l_Lean_Expr_appArg_x21(v___x_1651_);
lean_dec_ref(v___x_1651_);
v___x_1653_ = l_Lean_Expr_appArg_x21(v_snd_1454_);
v_fst_1595_ = v___y_1453_;
v_fst_1596_ = v___x_1652_;
v_snd_1597_ = v___x_1653_;
goto v___jp_1594_;
}
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1654_ = l_Lean_Expr_appFn_x21(v_snd_1454_);
v___x_1655_ = l_Lean_Expr_appFn_x21(v___x_1654_);
lean_dec_ref(v___x_1654_);
v___x_1656_ = l_Lean_Expr_appArg_x21(v___x_1655_);
lean_dec_ref(v___x_1655_);
v___x_1657_ = l_Lean_Expr_appArg_x21(v_snd_1454_);
v_fst_1595_ = v___x_1448_;
v_fst_1596_ = v___x_1656_;
v_snd_1597_ = v___x_1657_;
goto v___jp_1594_;
}
v___jp_1461_:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1464_, 0, v_proof_1463_);
v___x_1465_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1465_, 0, v___y_1462_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
lean_ctor_set_uint8(v___x_1465_, sizeof(void*)*2, v___x_1448_);
v___x_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
return v___x_1466_;
}
v___jp_1467_:
{
if (lean_obj_tag(v___y_1469_) == 0)
{
lean_object* v_a_1470_; 
v_a_1470_ = lean_ctor_get(v___y_1469_, 0);
lean_inc(v_a_1470_);
lean_dec_ref_known(v___y_1469_, 1);
v___y_1462_ = v___y_1468_;
v_proof_1463_ = v_a_1470_;
goto v___jp_1461_;
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec_ref(v___y_1468_);
v_a_1471_ = lean_ctor_get(v___y_1469_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___y_1469_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___y_1469_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___y_1469_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
v___jp_1479_:
{
if (v___y_1488_ == 0)
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
lean_dec_ref(v___y_1483_);
v___x_1489_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1490_ = l_Lean_MessageData_ofExpr(v___y_1485_);
v___x_1491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1489_);
lean_ctor_set(v___x_1491_, 1, v___x_1490_);
v___x_1492_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1491_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
v___x_1494_ = l_Lean_Exception_toMessageData(v___y_1484_);
v___x_1495_ = l_Lean_indentD(v___x_1494_);
v___x_1496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1493_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v___x_1497_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1496_);
lean_ctor_set(v___x_1498_, 1, v___x_1497_);
v___x_1499_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1498_, v___y_1481_, v___y_1486_, v___y_1482_, v___y_1480_);
v___y_1468_ = v___y_1487_;
v___y_1469_ = v___x_1499_;
goto v___jp_1467_;
}
else
{
lean_dec_ref(v___y_1485_);
lean_dec_ref(v___y_1484_);
v___y_1468_ = v___y_1487_;
v___y_1469_ = v___y_1483_;
goto v___jp_1467_;
}
}
v___jp_1501_:
{
lean_object* v___x_1508_; lean_object* v_a_1509_; lean_object* v___x_1510_; 
v___x_1508_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_1502_, v___y_1505_);
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_a_1509_);
lean_dec_ref(v___x_1508_);
v___x_1510_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___x_1500_, v___y_1505_);
if (v___y_1503_ == 0)
{
lean_object* v_a_1511_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_a_1511_);
lean_dec_ref(v___x_1510_);
v___y_1462_ = v_a_1509_;
v_proof_1463_ = v_a_1511_;
goto v___jp_1461_;
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1513_; 
v_a_1512_ = lean_ctor_get(v___x_1510_, 0);
lean_inc_n(v_a_1512_, 2);
lean_dec_ref(v___x_1510_);
v___x_1513_ = l_Lean_Meta_mkEqOfHEq(v_a_1512_, v___x_1448_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_dec(v_a_1512_);
v___y_1468_ = v_a_1509_;
v___y_1469_ = v___x_1513_;
goto v___jp_1467_;
}
else
{
lean_object* v_a_1514_; uint8_t v___x_1515_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_a_1514_);
v___x_1515_ = l_Lean_Exception_isInterrupt(v_a_1514_);
if (v___x_1515_ == 0)
{
uint8_t v___x_1516_; 
lean_inc(v_a_1514_);
v___x_1516_ = l_Lean_Exception_isRuntime(v_a_1514_);
v___y_1480_ = v___y_1507_;
v___y_1481_ = v___y_1504_;
v___y_1482_ = v___y_1506_;
v___y_1483_ = v___x_1513_;
v___y_1484_ = v_a_1514_;
v___y_1485_ = v_a_1512_;
v___y_1486_ = v___y_1505_;
v___y_1487_ = v_a_1509_;
v___y_1488_ = v___x_1516_;
goto v___jp_1479_;
}
else
{
v___y_1480_ = v___y_1507_;
v___y_1481_ = v___y_1504_;
v___y_1482_ = v___y_1506_;
v___y_1483_ = v___x_1513_;
v___y_1484_ = v_a_1514_;
v___y_1485_ = v_a_1512_;
v___y_1486_ = v___y_1505_;
v___y_1487_ = v_a_1509_;
v___y_1488_ = v___x_1515_;
goto v___jp_1479_;
}
}
}
}
v___jp_1517_:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; uint8_t v___x_1527_; 
v___x_1525_ = lean_array_get_size(v_a_1524_);
v___x_1526_ = lean_unsigned_to_nat(0u);
v___x_1527_ = lean_nat_dec_eq(v___x_1525_, v___x_1526_);
if (v___x_1527_ == 0)
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1546_; 
lean_dec_ref(v___y_1518_);
lean_dec_ref(v___x_1500_);
v___x_1528_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1529_ = l_Lean_MessageData_ofConstName(v___x_1451_, v___x_1527_);
v___x_1530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1528_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
v___x_1531_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1530_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
v___x_1533_ = lean_array_to_list(v_a_1524_);
v___x_1534_ = lean_box(0);
v___x_1535_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_1533_, v___x_1534_);
v___x_1536_ = l_Lean_MessageData_ofList(v___x_1535_);
v___x_1537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1532_);
lean_ctor_set(v___x_1537_, 1, v___x_1536_);
v___x_1538_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1537_, v___y_1521_, v___y_1520_, v___y_1522_, v___y_1519_);
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1541_ = v___x_1538_;
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1538_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
if (v_isShared_1542_ == 0)
{
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1539_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
else
{
lean_dec_ref(v_a_1524_);
lean_dec(v___x_1451_);
v___y_1502_ = v___y_1518_;
v___y_1503_ = v___y_1523_;
v___y_1504_ = v___y_1521_;
v___y_1505_ = v___y_1520_;
v___y_1506_ = v___y_1522_;
v___y_1507_ = v___y_1519_;
goto v___jp_1501_;
}
}
v___jp_1547_:
{
if (lean_obj_tag(v___y_1554_) == 0)
{
lean_object* v_a_1555_; 
v_a_1555_ = lean_ctor_get(v___y_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___y_1554_, 1);
v___y_1518_ = v___y_1548_;
v___y_1519_ = v___y_1550_;
v___y_1520_ = v___y_1549_;
v___y_1521_ = v___y_1551_;
v___y_1522_ = v___y_1552_;
v___y_1523_ = v___y_1553_;
v_a_1524_ = v_a_1555_;
goto v___jp_1517_;
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec_ref(v___y_1548_);
lean_dec_ref(v___x_1500_);
lean_dec(v___x_1451_);
v_a_1556_ = lean_ctor_get(v___y_1554_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___y_1554_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___y_1554_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___y_1554_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
v___jp_1567_:
{
lean_object* v___x_1574_; size_t v_sz_1575_; lean_object* v___x_1576_; 
v___x_1574_ = lean_box(0);
v_sz_1575_ = lean_array_size(v___x_1566_);
v___x_1576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1566_, v_sz_1575_, v___x_1565_, v___x_1574_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; uint8_t v___x_1580_; 
lean_dec_ref_known(v___x_1576_, 1);
v___x_1577_ = lean_unsigned_to_nat(0u);
v___x_1578_ = lean_array_get_size(v___x_1566_);
v___x_1579_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1580_ = lean_nat_dec_lt(v___x_1577_, v___x_1578_);
if (v___x_1580_ == 0)
{
lean_dec_ref(v___x_1566_);
v___y_1518_ = v___y_1568_;
v___y_1519_ = v___y_1573_;
v___y_1520_ = v___y_1571_;
v___y_1521_ = v___y_1570_;
v___y_1522_ = v___y_1572_;
v___y_1523_ = v___y_1569_;
v_a_1524_ = v___x_1579_;
goto v___jp_1517_;
}
else
{
uint8_t v___x_1581_; 
v___x_1581_ = lean_nat_dec_le(v___x_1578_, v___x_1578_);
if (v___x_1581_ == 0)
{
if (v___x_1580_ == 0)
{
lean_dec_ref(v___x_1566_);
v___y_1518_ = v___y_1568_;
v___y_1519_ = v___y_1573_;
v___y_1520_ = v___y_1571_;
v___y_1521_ = v___y_1570_;
v___y_1522_ = v___y_1572_;
v___y_1523_ = v___y_1569_;
v_a_1524_ = v___x_1579_;
goto v___jp_1517_;
}
else
{
size_t v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = lean_usize_of_nat(v___x_1578_);
v___x_1583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1566_, v___x_1565_, v___x_1582_, v___x_1579_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec_ref(v___x_1566_);
v___y_1548_ = v___y_1568_;
v___y_1549_ = v___y_1571_;
v___y_1550_ = v___y_1573_;
v___y_1551_ = v___y_1570_;
v___y_1552_ = v___y_1572_;
v___y_1553_ = v___y_1569_;
v___y_1554_ = v___x_1583_;
goto v___jp_1547_;
}
}
else
{
size_t v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = lean_usize_of_nat(v___x_1578_);
v___x_1585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1566_, v___x_1565_, v___x_1584_, v___x_1579_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec_ref(v___x_1566_);
v___y_1548_ = v___y_1568_;
v___y_1549_ = v___y_1571_;
v___y_1550_ = v___y_1573_;
v___y_1551_ = v___y_1570_;
v___y_1552_ = v___y_1572_;
v___y_1553_ = v___y_1569_;
v___y_1554_ = v___x_1585_;
goto v___jp_1547_;
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec_ref(v___y_1568_);
lean_dec_ref(v___x_1566_);
lean_dec_ref(v___x_1500_);
lean_dec(v___x_1451_);
v_a_1586_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1576_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1576_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
v___jp_1594_:
{
lean_object* v___x_1598_; 
lean_inc_ref(v_fst_1596_);
lean_inc_ref(v_e_1452_);
v___x_1598_ = l_Lean_Meta_isExprDefEq(v_e_1452_, v_fst_1596_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; uint8_t v___x_1600_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1598_, 1);
v___x_1600_ = lean_unbox(v_a_1599_);
lean_dec(v_a_1599_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec_ref(v_snd_1597_);
lean_dec_ref(v___x_1566_);
lean_dec_ref(v___x_1500_);
v___x_1601_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1602_ = l_Lean_MessageData_ofExpr(v_fst_1596_);
v___x_1603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1601_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
v___x_1604_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1603_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
v___x_1606_ = l_Lean_MessageData_ofConstName(v___x_1451_, v___y_1453_);
v___x_1607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1605_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
v___x_1608_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1607_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
v___x_1610_ = l_Lean_MessageData_ofExpr(v_e_1452_);
v___x_1611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1609_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
v___x_1612_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_1613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1611_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
v___x_1614_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1613_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1614_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1614_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
else
{
lean_dec_ref(v_fst_1596_);
lean_dec_ref(v_e_1452_);
v___y_1568_ = v_snd_1597_;
v___y_1569_ = v_fst_1595_;
v___y_1570_ = v___y_1456_;
v___y_1571_ = v___y_1457_;
v___y_1572_ = v___y_1458_;
v___y_1573_ = v___y_1459_;
goto v___jp_1567_;
}
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec_ref(v_snd_1597_);
lean_dec_ref(v_fst_1596_);
lean_dec_ref(v___x_1566_);
lean_dec_ref(v___x_1500_);
lean_dec_ref(v_e_1452_);
lean_dec(v___x_1451_);
v_a_1623_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1598_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1598_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4___boxed(lean_object* v___x_1658_, lean_object* v___x_1659_, lean_object* v_fst_1660_, lean_object* v___x_1661_, lean_object* v_e_1662_, lean_object* v___y_1663_, lean_object* v_snd_1664_, lean_object* v_____r_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
uint8_t v___x_85885__boxed_1671_; uint8_t v___y_85889__boxed_1672_; lean_object* v_res_1673_; 
v___x_85885__boxed_1671_ = lean_unbox(v___x_1658_);
v___y_85889__boxed_1672_ = lean_unbox(v___y_1663_);
v_res_1673_ = l_Lean_Meta_rwMatcher___lam__4(v___x_85885__boxed_1671_, v___x_1659_, v_fst_1660_, v___x_1661_, v_e_1662_, v___y_85889__boxed_1672_, v_snd_1664_, v_____r_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec_ref(v_snd_1664_);
return v_res_1673_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1674_; double v___x_1675_; 
v___x_1674_ = lean_unsigned_to_nat(0u);
v___x_1675_ = lean_float_of_nat(v___x_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(lean_object* v_cls_1679_, lean_object* v_msg_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v_ref_1686_; lean_object* v___x_1687_; lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1733_; 
v_ref_1686_ = lean_ctor_get(v___y_1683_, 2);
v___x_1687_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1690_ = v___x_1687_;
v_isShared_1691_ = v_isSharedCheck_1733_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1687_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1733_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1692_; lean_object* v_traceState_1693_; lean_object* v_env_1694_; lean_object* v_nextMacroScope_1695_; lean_object* v_ngen_1696_; lean_object* v_auxDeclNGen_1697_; lean_object* v_cache_1698_; lean_object* v_recordedDeps_1699_; lean_object* v_messages_1700_; lean_object* v_infoState_1701_; lean_object* v_snapshotTasks_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1732_; 
v___x_1692_ = lean_st_ref_take(v___y_1684_);
v_traceState_1693_ = lean_ctor_get(v___x_1692_, 4);
v_env_1694_ = lean_ctor_get(v___x_1692_, 0);
v_nextMacroScope_1695_ = lean_ctor_get(v___x_1692_, 1);
v_ngen_1696_ = lean_ctor_get(v___x_1692_, 2);
v_auxDeclNGen_1697_ = lean_ctor_get(v___x_1692_, 3);
v_cache_1698_ = lean_ctor_get(v___x_1692_, 5);
v_recordedDeps_1699_ = lean_ctor_get(v___x_1692_, 6);
v_messages_1700_ = lean_ctor_get(v___x_1692_, 7);
v_infoState_1701_ = lean_ctor_get(v___x_1692_, 8);
v_snapshotTasks_1702_ = lean_ctor_get(v___x_1692_, 9);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1704_ = v___x_1692_;
v_isShared_1705_ = v_isSharedCheck_1732_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_snapshotTasks_1702_);
lean_inc(v_infoState_1701_);
lean_inc(v_messages_1700_);
lean_inc(v_recordedDeps_1699_);
lean_inc(v_cache_1698_);
lean_inc(v_traceState_1693_);
lean_inc(v_auxDeclNGen_1697_);
lean_inc(v_ngen_1696_);
lean_inc(v_nextMacroScope_1695_);
lean_inc(v_env_1694_);
lean_dec(v___x_1692_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1732_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
uint64_t v_tid_1706_; lean_object* v_traces_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1731_; 
v_tid_1706_ = lean_ctor_get_uint64(v_traceState_1693_, sizeof(void*)*1);
v_traces_1707_ = lean_ctor_get(v_traceState_1693_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_traceState_1693_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1709_ = v_traceState_1693_;
v_isShared_1710_ = v_isSharedCheck_1731_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_traces_1707_);
lean_dec(v_traceState_1693_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1731_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; double v___x_1713_; uint8_t v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1722_; 
v___x_1711_ = lean_box(0);
v___x_1712_ = lean_box(0);
v___x_1713_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0);
v___x_1714_ = 0;
v___x_1715_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1));
v___x_1716_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1716_, 0, v_cls_1679_);
lean_ctor_set(v___x_1716_, 1, v___x_1712_);
lean_ctor_set(v___x_1716_, 2, v___x_1715_);
lean_ctor_set_float(v___x_1716_, sizeof(void*)*3, v___x_1713_);
lean_ctor_set_float(v___x_1716_, sizeof(void*)*3 + 8, v___x_1713_);
lean_ctor_set_uint8(v___x_1716_, sizeof(void*)*3 + 16, v___x_1714_);
v___x_1717_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__2));
v___x_1718_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1716_);
lean_ctor_set(v___x_1718_, 1, v_a_1688_);
lean_ctor_set(v___x_1718_, 2, v___x_1717_);
lean_inc(v_ref_1686_);
v___x_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1719_, 0, v_ref_1686_);
lean_ctor_set(v___x_1719_, 1, v___x_1718_);
v___x_1720_ = l_Lean_PersistentArray_push___redArg(v_traces_1707_, v___x_1719_);
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v___x_1720_);
v___x_1722_ = v___x_1709_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1720_);
lean_ctor_set_uint64(v_reuseFailAlloc_1730_, sizeof(void*)*1, v_tid_1706_);
v___x_1722_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
lean_object* v___x_1724_; 
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 4, v___x_1722_);
v___x_1724_ = v___x_1704_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_env_1694_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_nextMacroScope_1695_);
lean_ctor_set(v_reuseFailAlloc_1729_, 2, v_ngen_1696_);
lean_ctor_set(v_reuseFailAlloc_1729_, 3, v_auxDeclNGen_1697_);
lean_ctor_set(v_reuseFailAlloc_1729_, 4, v___x_1722_);
lean_ctor_set(v_reuseFailAlloc_1729_, 5, v_cache_1698_);
lean_ctor_set(v_reuseFailAlloc_1729_, 6, v_recordedDeps_1699_);
lean_ctor_set(v_reuseFailAlloc_1729_, 7, v_messages_1700_);
lean_ctor_set(v_reuseFailAlloc_1729_, 8, v_infoState_1701_);
lean_ctor_set(v_reuseFailAlloc_1729_, 9, v_snapshotTasks_1702_);
v___x_1724_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_object* v___x_1725_; lean_object* v___x_1727_; 
v___x_1725_ = lean_st_ref_put(v___y_1684_, v___x_1724_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 0, v___x_1711_);
v___x_1727_ = v___x_1690_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1711_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___boxed(lean_object* v_cls_1734_, lean_object* v_msg_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v_cls_1734_, v_msg_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(lean_object* v_a_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Lean_Meta_reduceRecMatcher_x3f(v_a_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1762_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1751_ = v___x_1748_;
v_isShared_1752_ = v_isSharedCheck_1762_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1748_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1762_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
if (lean_obj_tag(v_a_1749_) == 1)
{
lean_object* v_val_1753_; lean_object* v___x_1754_; 
lean_del_object(v___x_1751_);
lean_dec_ref(v_a_1742_);
v_val_1753_ = lean_ctor_get(v_a_1749_, 0);
lean_inc(v_val_1753_);
lean_dec_ref_known(v_a_1749_, 1);
v___x_1754_ = l_Lean_Expr_headBeta(v_val_1753_);
v_a_1742_ = v___x_1754_;
goto _start;
}
else
{
lean_object* v___x_1756_; uint8_t v___x_1757_; 
lean_dec(v_a_1749_);
lean_inc_ref(v_a_1742_);
v___x_1756_ = l_Lean_Expr_headBeta(v_a_1742_);
v___x_1757_ = lean_expr_eqv(v_a_1742_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_del_object(v___x_1751_);
lean_dec_ref(v_a_1742_);
v_a_1742_ = v___x_1756_;
goto _start;
}
else
{
lean_object* v___x_1760_; 
lean_dec_ref(v___x_1756_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v_a_1742_);
v___x_1760_ = v___x_1751_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1742_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
lean_dec_ref(v_a_1742_);
v_a_1763_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1748_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1748_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg___boxed(lean_object* v_a_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(v_a_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(lean_object* v_opts_1778_, lean_object* v_opt_1779_){
_start:
{
lean_object* v_name_1780_; lean_object* v_defValue_1781_; lean_object* v_map_1782_; lean_object* v___x_1783_; 
v_name_1780_ = lean_ctor_get(v_opt_1779_, 0);
v_defValue_1781_ = lean_ctor_get(v_opt_1779_, 1);
v_map_1782_ = lean_ctor_get(v_opts_1778_, 0);
v___x_1783_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1782_, v_name_1780_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_inc(v_defValue_1781_);
return v_defValue_1781_;
}
else
{
lean_object* v_val_1784_; 
v_val_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_val_1784_);
lean_dec_ref_known(v___x_1783_, 1);
if (lean_obj_tag(v_val_1784_) == 3)
{
lean_object* v_v_1785_; 
v_v_1785_ = lean_ctor_get(v_val_1784_, 0);
lean_inc(v_v_1785_);
lean_dec_ref_known(v_val_1784_, 1);
return v_v_1785_;
}
else
{
lean_dec(v_val_1784_);
lean_inc(v_defValue_1781_);
return v_defValue_1781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16___boxed(lean_object* v_opts_1786_, lean_object* v_opt_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_1786_, v_opt_1787_);
lean_dec_ref(v_opt_1787_);
lean_dec_ref(v_opts_1786_);
return v_res_1788_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(lean_object* v_e_1789_){
_start:
{
if (lean_obj_tag(v_e_1789_) == 0)
{
uint8_t v___x_1790_; 
v___x_1790_ = 2;
return v___x_1790_;
}
else
{
uint8_t v___x_1791_; 
v___x_1791_ = 0;
return v___x_1791_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___boxed(lean_object* v_e_1792_){
_start:
{
uint8_t v_res_1793_; lean_object* v_r_1794_; 
v_res_1793_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(v_e_1792_);
lean_dec_ref(v_e_1792_);
v_r_1794_ = lean_box(v_res_1793_);
return v_r_1794_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(lean_object* v_x_1795_){
_start:
{
if (lean_obj_tag(v_x_1795_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
v_a_1797_ = lean_ctor_get(v_x_1795_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v_x_1795_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v_x_1795_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v_x_1795_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
lean_ctor_set_tag(v___x_1799_, 1);
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
else
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
v_a_1805_ = lean_ctor_get(v_x_1795_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v_x_1795_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v_x_1795_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v_x_1795_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
lean_ctor_set_tag(v___x_1807_, 0);
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg___boxed(lean_object* v_x_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(v_x_1813_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15(size_t v_sz_1816_, size_t v_i_1817_, lean_object* v_bs_1818_){
_start:
{
uint8_t v___x_1819_; 
v___x_1819_ = lean_usize_dec_lt(v_i_1817_, v_sz_1816_);
if (v___x_1819_ == 0)
{
return v_bs_1818_;
}
else
{
lean_object* v_v_1820_; lean_object* v_msg_1821_; lean_object* v___x_1822_; lean_object* v_bs_x27_1823_; size_t v___x_1824_; size_t v___x_1825_; lean_object* v___x_1826_; 
v_v_1820_ = lean_array_uget_borrowed(v_bs_1818_, v_i_1817_);
v_msg_1821_ = lean_ctor_get(v_v_1820_, 1);
lean_inc_ref(v_msg_1821_);
v___x_1822_ = lean_unsigned_to_nat(0u);
v_bs_x27_1823_ = lean_array_uset(v_bs_1818_, v_i_1817_, v___x_1822_);
v___x_1824_ = ((size_t)1ULL);
v___x_1825_ = lean_usize_add(v_i_1817_, v___x_1824_);
v___x_1826_ = lean_array_uset(v_bs_x27_1823_, v_i_1817_, v_msg_1821_);
v_i_1817_ = v___x_1825_;
v_bs_1818_ = v___x_1826_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15___boxed(lean_object* v_sz_1828_, lean_object* v_i_1829_, lean_object* v_bs_1830_){
_start:
{
size_t v_sz_boxed_1831_; size_t v_i_boxed_1832_; lean_object* v_res_1833_; 
v_sz_boxed_1831_ = lean_unbox_usize(v_sz_1828_);
lean_dec(v_sz_1828_);
v_i_boxed_1832_ = lean_unbox_usize(v_i_1829_);
lean_dec(v_i_1829_);
v_res_1833_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15(v_sz_boxed_1831_, v_i_boxed_1832_, v_bs_1830_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(lean_object* v_oldTraces_1834_, lean_object* v_data_1835_, lean_object* v_ref_1836_, lean_object* v_msg_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v_toCold_1843_; lean_object* v_currRecDepth_1844_; lean_object* v_ref_1845_; uint16_t v_optionFlags_1846_; uint8_t v_suppressElabErrors_1847_; uint8_t v_isRecordingDeps_1848_; lean_object* v_ref_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v_traceState_1852_; lean_object* v_traces_1853_; lean_object* v___x_1854_; size_t v_sz_1855_; size_t v___x_1856_; lean_object* v___x_1857_; lean_object* v_msg_1858_; lean_object* v___x_1859_; lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1898_; 
v_toCold_1843_ = lean_ctor_get(v___y_1840_, 0);
v_currRecDepth_1844_ = lean_ctor_get(v___y_1840_, 1);
v_ref_1845_ = lean_ctor_get(v___y_1840_, 2);
v_optionFlags_1846_ = lean_ctor_get_uint16(v___y_1840_, sizeof(void*)*3);
v_suppressElabErrors_1847_ = lean_ctor_get_uint8(v___y_1840_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1848_ = lean_ctor_get_uint8(v___y_1840_, sizeof(void*)*3 + 3);
v_ref_1849_ = l_Lean_replaceRef(v_ref_1836_, v_ref_1845_);
lean_inc(v_currRecDepth_1844_);
lean_inc_ref(v_toCold_1843_);
v___x_1850_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1850_, 0, v_toCold_1843_);
lean_ctor_set(v___x_1850_, 1, v_currRecDepth_1844_);
lean_ctor_set(v___x_1850_, 2, v_ref_1849_);
lean_ctor_set_uint16(v___x_1850_, sizeof(void*)*3, v_optionFlags_1846_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*3 + 2, v_suppressElabErrors_1847_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*3 + 3, v_isRecordingDeps_1848_);
v___x_1851_ = lean_st_ref_get(v___y_1841_);
v_traceState_1852_ = lean_ctor_get(v___x_1851_, 4);
lean_inc_ref(v_traceState_1852_);
lean_dec(v___x_1851_);
v_traces_1853_ = lean_ctor_get(v_traceState_1852_, 0);
lean_inc_ref(v_traces_1853_);
lean_dec_ref(v_traceState_1852_);
v___x_1854_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1853_);
lean_dec_ref(v_traces_1853_);
v_sz_1855_ = lean_array_size(v___x_1854_);
v___x_1856_ = ((size_t)0ULL);
v___x_1857_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15(v_sz_1855_, v___x_1856_, v___x_1854_);
v_msg_1858_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1858_, 0, v_data_1835_);
lean_ctor_set(v_msg_1858_, 1, v_msg_1837_);
lean_ctor_set(v_msg_1858_, 2, v___x_1857_);
v___x_1859_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_1858_, v___y_1838_, v___y_1839_, v___x_1850_, v___y_1841_);
lean_dec_ref_known(v___x_1850_, 3);
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1862_ = v___x_1859_;
v_isShared_1863_ = v_isSharedCheck_1898_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1859_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1898_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1864_; lean_object* v_traceState_1865_; lean_object* v_env_1866_; lean_object* v_nextMacroScope_1867_; lean_object* v_ngen_1868_; lean_object* v_auxDeclNGen_1869_; lean_object* v_cache_1870_; lean_object* v_recordedDeps_1871_; lean_object* v_messages_1872_; lean_object* v_infoState_1873_; lean_object* v_snapshotTasks_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1897_; 
v___x_1864_ = lean_st_ref_take(v___y_1841_);
v_traceState_1865_ = lean_ctor_get(v___x_1864_, 4);
v_env_1866_ = lean_ctor_get(v___x_1864_, 0);
v_nextMacroScope_1867_ = lean_ctor_get(v___x_1864_, 1);
v_ngen_1868_ = lean_ctor_get(v___x_1864_, 2);
v_auxDeclNGen_1869_ = lean_ctor_get(v___x_1864_, 3);
v_cache_1870_ = lean_ctor_get(v___x_1864_, 5);
v_recordedDeps_1871_ = lean_ctor_get(v___x_1864_, 6);
v_messages_1872_ = lean_ctor_get(v___x_1864_, 7);
v_infoState_1873_ = lean_ctor_get(v___x_1864_, 8);
v_snapshotTasks_1874_ = lean_ctor_get(v___x_1864_, 9);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1876_ = v___x_1864_;
v_isShared_1877_ = v_isSharedCheck_1897_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_snapshotTasks_1874_);
lean_inc(v_infoState_1873_);
lean_inc(v_messages_1872_);
lean_inc(v_recordedDeps_1871_);
lean_inc(v_cache_1870_);
lean_inc(v_traceState_1865_);
lean_inc(v_auxDeclNGen_1869_);
lean_inc(v_ngen_1868_);
lean_inc(v_nextMacroScope_1867_);
lean_inc(v_env_1866_);
lean_dec(v___x_1864_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1897_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
uint64_t v_tid_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1895_; 
v_tid_1878_ = lean_ctor_get_uint64(v_traceState_1865_, sizeof(void*)*1);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_traceState_1865_);
if (v_isSharedCheck_1895_ == 0)
{
lean_object* v_unused_1896_; 
v_unused_1896_ = lean_ctor_get(v_traceState_1865_, 0);
lean_dec(v_unused_1896_);
v___x_1880_ = v_traceState_1865_;
v_isShared_1881_ = v_isSharedCheck_1895_;
goto v_resetjp_1879_;
}
else
{
lean_dec(v_traceState_1865_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1895_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1886_; 
v___x_1882_ = lean_box(0);
v___x_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1883_, 0, v_ref_1836_);
lean_ctor_set(v___x_1883_, 1, v_a_1860_);
v___x_1884_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1834_, v___x_1883_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v___x_1884_);
v___x_1886_ = v___x_1880_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1884_);
lean_ctor_set_uint64(v_reuseFailAlloc_1894_, sizeof(void*)*1, v_tid_1878_);
v___x_1886_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
lean_object* v___x_1888_; 
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 4, v___x_1886_);
v___x_1888_ = v___x_1876_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_env_1866_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v_nextMacroScope_1867_);
lean_ctor_set(v_reuseFailAlloc_1893_, 2, v_ngen_1868_);
lean_ctor_set(v_reuseFailAlloc_1893_, 3, v_auxDeclNGen_1869_);
lean_ctor_set(v_reuseFailAlloc_1893_, 4, v___x_1886_);
lean_ctor_set(v_reuseFailAlloc_1893_, 5, v_cache_1870_);
lean_ctor_set(v_reuseFailAlloc_1893_, 6, v_recordedDeps_1871_);
lean_ctor_set(v_reuseFailAlloc_1893_, 7, v_messages_1872_);
lean_ctor_set(v_reuseFailAlloc_1893_, 8, v_infoState_1873_);
lean_ctor_set(v_reuseFailAlloc_1893_, 9, v_snapshotTasks_1874_);
v___x_1888_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1889_; lean_object* v___x_1891_; 
v___x_1889_ = lean_st_ref_put(v___y_1841_, v___x_1888_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v___x_1882_);
v___x_1891_ = v___x_1862_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1882_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13___boxed(lean_object* v_oldTraces_1899_, lean_object* v_data_1900_, lean_object* v_ref_1901_, lean_object* v_msg_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(v_oldTraces_1899_, v_data_1900_, v_ref_1901_, v_msg_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
return v_res_1908_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1(void){
_start:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1910_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__0));
v___x_1911_ = l_Lean_stringToMessageData(v___x_1910_);
return v___x_1911_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2(void){
_start:
{
lean_object* v___x_1912_; double v___x_1913_; 
v___x_1912_ = lean_unsigned_to_nat(1000u);
v___x_1913_ = lean_float_of_nat(v___x_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(lean_object* v_cls_1914_, uint8_t v_collapsed_1915_, lean_object* v_tag_1916_, lean_object* v_opts_1917_, uint8_t v_clsEnabled_1918_, lean_object* v_oldTraces_1919_, lean_object* v_msg_1920_, lean_object* v_resStartStop_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v_fst_1927_; lean_object* v_snd_1928_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v_data_1932_; lean_object* v_fst_1943_; lean_object* v_snd_1944_; lean_object* v___x_1945_; uint8_t v___x_1946_; lean_object* v___y_1948_; lean_object* v_a_1949_; uint8_t v___y_1964_; double v___y_1996_; 
v_fst_1927_ = lean_ctor_get(v_resStartStop_1921_, 0);
lean_inc(v_fst_1927_);
v_snd_1928_ = lean_ctor_get(v_resStartStop_1921_, 1);
lean_inc(v_snd_1928_);
lean_dec_ref(v_resStartStop_1921_);
v_fst_1943_ = lean_ctor_get(v_snd_1928_, 0);
lean_inc(v_fst_1943_);
v_snd_1944_ = lean_ctor_get(v_snd_1928_, 1);
lean_inc(v_snd_1944_);
lean_dec(v_snd_1928_);
v___x_1945_ = l_Lean_trace_profiler;
v___x_1946_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_opts_1917_, v___x_1945_);
if (v___x_1946_ == 0)
{
v___y_1964_ = v___x_1946_;
goto v___jp_1963_;
}
else
{
lean_object* v___x_2001_; uint8_t v___x_2002_; 
v___x_2001_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2002_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_opts_1917_, v___x_2001_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; lean_object* v___x_2004_; double v___x_2005_; double v___x_2006_; double v___x_2007_; 
v___x_2003_ = l_Lean_trace_profiler_threshold;
v___x_2004_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_1917_, v___x_2003_);
v___x_2005_ = lean_float_of_nat(v___x_2004_);
v___x_2006_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2);
v___x_2007_ = lean_float_div(v___x_2005_, v___x_2006_);
v___y_1996_ = v___x_2007_;
goto v___jp_1995_;
}
else
{
lean_object* v___x_2008_; lean_object* v___x_2009_; double v___x_2010_; 
v___x_2008_ = l_Lean_trace_profiler_threshold;
v___x_2009_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_1917_, v___x_2008_);
v___x_2010_ = lean_float_of_nat(v___x_2009_);
v___y_1996_ = v___x_2010_;
goto v___jp_1995_;
}
}
v___jp_1929_:
{
lean_object* v___x_1933_; 
lean_inc(v___y_1931_);
v___x_1933_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(v_oldTraces_1919_, v_data_1932_, v___y_1931_, v___y_1930_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v___x_1934_; 
lean_dec_ref_known(v___x_1933_, 1);
v___x_1934_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(v_fst_1927_);
return v___x_1934_;
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1942_; 
lean_dec(v_fst_1927_);
v_a_1935_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1937_ = v___x_1933_;
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1933_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1935_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
v___jp_1947_:
{
uint8_t v_result_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; double v___x_1953_; lean_object* v_data_1954_; 
v_result_1950_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(v_fst_1927_);
v___x_1951_ = lean_box(v_result_1950_);
v___x_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
v___x_1953_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0);
lean_inc_ref(v_tag_1916_);
lean_inc_ref(v___x_1952_);
lean_inc(v_cls_1914_);
v_data_1954_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1954_, 0, v_cls_1914_);
lean_ctor_set(v_data_1954_, 1, v___x_1952_);
lean_ctor_set(v_data_1954_, 2, v_tag_1916_);
lean_ctor_set_float(v_data_1954_, sizeof(void*)*3, v___x_1953_);
lean_ctor_set_float(v_data_1954_, sizeof(void*)*3 + 8, v___x_1953_);
lean_ctor_set_uint8(v_data_1954_, sizeof(void*)*3 + 16, v_collapsed_1915_);
if (v___x_1946_ == 0)
{
lean_dec_ref_known(v___x_1952_, 1);
lean_dec(v_snd_1944_);
lean_dec(v_fst_1943_);
lean_dec_ref(v_tag_1916_);
lean_dec(v_cls_1914_);
v___y_1930_ = v_a_1949_;
v___y_1931_ = v___y_1948_;
v_data_1932_ = v_data_1954_;
goto v___jp_1929_;
}
else
{
lean_object* v_data_1955_; double v___x_1956_; double v___x_1957_; 
lean_dec_ref_known(v_data_1954_, 3);
v_data_1955_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1955_, 0, v_cls_1914_);
lean_ctor_set(v_data_1955_, 1, v___x_1952_);
lean_ctor_set(v_data_1955_, 2, v_tag_1916_);
v___x_1956_ = lean_unbox_float(v_fst_1943_);
lean_dec(v_fst_1943_);
lean_ctor_set_float(v_data_1955_, sizeof(void*)*3, v___x_1956_);
v___x_1957_ = lean_unbox_float(v_snd_1944_);
lean_dec(v_snd_1944_);
lean_ctor_set_float(v_data_1955_, sizeof(void*)*3 + 8, v___x_1957_);
lean_ctor_set_uint8(v_data_1955_, sizeof(void*)*3 + 16, v_collapsed_1915_);
v___y_1930_ = v_a_1949_;
v___y_1931_ = v___y_1948_;
v_data_1932_ = v_data_1955_;
goto v___jp_1929_;
}
}
v___jp_1958_:
{
lean_object* v_ref_1959_; lean_object* v___x_1960_; 
v_ref_1959_ = lean_ctor_get(v___y_1924_, 2);
lean_inc(v___y_1925_);
lean_inc_ref(v___y_1924_);
lean_inc(v___y_1923_);
lean_inc_ref(v___y_1922_);
lean_inc(v_fst_1927_);
v___x_1960_ = lean_apply_6(v_msg_1920_, v_fst_1927_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, lean_box(0));
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1961_);
lean_dec_ref_known(v___x_1960_, 1);
v___y_1948_ = v_ref_1959_;
v_a_1949_ = v_a_1961_;
goto v___jp_1947_;
}
else
{
lean_object* v___x_1962_; 
lean_dec_ref_known(v___x_1960_, 1);
v___x_1962_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1);
v___y_1948_ = v_ref_1959_;
v_a_1949_ = v___x_1962_;
goto v___jp_1947_;
}
}
v___jp_1963_:
{
if (v_clsEnabled_1918_ == 0)
{
if (v___y_1964_ == 0)
{
lean_object* v___x_1965_; lean_object* v_traceState_1966_; lean_object* v_env_1967_; lean_object* v_nextMacroScope_1968_; lean_object* v_ngen_1969_; lean_object* v_auxDeclNGen_1970_; lean_object* v_cache_1971_; lean_object* v_recordedDeps_1972_; lean_object* v_messages_1973_; lean_object* v_infoState_1974_; lean_object* v_snapshotTasks_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1994_; 
lean_dec(v_snd_1944_);
lean_dec(v_fst_1943_);
lean_dec_ref(v_msg_1920_);
lean_dec_ref(v_tag_1916_);
lean_dec(v_cls_1914_);
v___x_1965_ = lean_st_ref_take(v___y_1925_);
v_traceState_1966_ = lean_ctor_get(v___x_1965_, 4);
v_env_1967_ = lean_ctor_get(v___x_1965_, 0);
v_nextMacroScope_1968_ = lean_ctor_get(v___x_1965_, 1);
v_ngen_1969_ = lean_ctor_get(v___x_1965_, 2);
v_auxDeclNGen_1970_ = lean_ctor_get(v___x_1965_, 3);
v_cache_1971_ = lean_ctor_get(v___x_1965_, 5);
v_recordedDeps_1972_ = lean_ctor_get(v___x_1965_, 6);
v_messages_1973_ = lean_ctor_get(v___x_1965_, 7);
v_infoState_1974_ = lean_ctor_get(v___x_1965_, 8);
v_snapshotTasks_1975_ = lean_ctor_get(v___x_1965_, 9);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1977_ = v___x_1965_;
v_isShared_1978_ = v_isSharedCheck_1994_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_snapshotTasks_1975_);
lean_inc(v_infoState_1974_);
lean_inc(v_messages_1973_);
lean_inc(v_recordedDeps_1972_);
lean_inc(v_cache_1971_);
lean_inc(v_traceState_1966_);
lean_inc(v_auxDeclNGen_1970_);
lean_inc(v_ngen_1969_);
lean_inc(v_nextMacroScope_1968_);
lean_inc(v_env_1967_);
lean_dec(v___x_1965_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1994_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
uint64_t v_tid_1979_; lean_object* v_traces_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1993_; 
v_tid_1979_ = lean_ctor_get_uint64(v_traceState_1966_, sizeof(void*)*1);
v_traces_1980_ = lean_ctor_get(v_traceState_1966_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v_traceState_1966_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1982_ = v_traceState_1966_;
v_isShared_1983_ = v_isSharedCheck_1993_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_traces_1980_);
lean_dec(v_traceState_1966_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1993_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1984_; lean_object* v___x_1986_; 
v___x_1984_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1919_, v_traces_1980_);
lean_dec_ref(v_traces_1980_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_1984_);
v___x_1986_ = v___x_1982_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1984_);
lean_ctor_set_uint64(v_reuseFailAlloc_1992_, sizeof(void*)*1, v_tid_1979_);
v___x_1986_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
lean_object* v___x_1988_; 
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 4, v___x_1986_);
v___x_1988_ = v___x_1977_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_env_1967_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_nextMacroScope_1968_);
lean_ctor_set(v_reuseFailAlloc_1991_, 2, v_ngen_1969_);
lean_ctor_set(v_reuseFailAlloc_1991_, 3, v_auxDeclNGen_1970_);
lean_ctor_set(v_reuseFailAlloc_1991_, 4, v___x_1986_);
lean_ctor_set(v_reuseFailAlloc_1991_, 5, v_cache_1971_);
lean_ctor_set(v_reuseFailAlloc_1991_, 6, v_recordedDeps_1972_);
lean_ctor_set(v_reuseFailAlloc_1991_, 7, v_messages_1973_);
lean_ctor_set(v_reuseFailAlloc_1991_, 8, v_infoState_1974_);
lean_ctor_set(v_reuseFailAlloc_1991_, 9, v_snapshotTasks_1975_);
v___x_1988_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = lean_st_ref_put(v___y_1925_, v___x_1988_);
v___x_1990_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(v_fst_1927_);
return v___x_1990_;
}
}
}
}
}
else
{
goto v___jp_1958_;
}
}
else
{
goto v___jp_1958_;
}
}
v___jp_1995_:
{
double v___x_1997_; double v___x_1998_; double v___x_1999_; uint8_t v___x_2000_; 
v___x_1997_ = lean_unbox_float(v_snd_1944_);
v___x_1998_ = lean_unbox_float(v_fst_1943_);
v___x_1999_ = lean_float_sub(v___x_1997_, v___x_1998_);
v___x_2000_ = lean_float_decLt(v___y_1996_, v___x_1999_);
v___y_1964_ = v___x_2000_;
goto v___jp_1963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___boxed(lean_object* v_cls_2011_, lean_object* v_collapsed_2012_, lean_object* v_tag_2013_, lean_object* v_opts_2014_, lean_object* v_clsEnabled_2015_, lean_object* v_oldTraces_2016_, lean_object* v_msg_2017_, lean_object* v_resStartStop_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
uint8_t v_collapsed_boxed_2024_; uint8_t v_clsEnabled_boxed_2025_; lean_object* v_res_2026_; 
v_collapsed_boxed_2024_ = lean_unbox(v_collapsed_2012_);
v_clsEnabled_boxed_2025_ = lean_unbox(v_clsEnabled_2015_);
v_res_2026_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v_cls_2011_, v_collapsed_boxed_2024_, v_tag_2013_, v_opts_2014_, v_clsEnabled_boxed_2025_, v_oldTraces_2016_, v_msg_2017_, v_resStartStop_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec_ref(v_opts_2014_);
return v_res_2026_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__3(void){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__2));
v___x_2032_ = l_Lean_stringToMessageData(v___x_2031_);
return v___x_2032_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__5(void){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__4));
v___x_2035_ = l_Lean_stringToMessageData(v___x_2034_);
return v___x_2035_;
}
}
static double _init_l_Lean_Meta_rwMatcher___closed__6(void){
_start:
{
lean_object* v___x_2036_; double v___x_2037_; 
v___x_2036_ = lean_unsigned_to_nat(1000000000u);
v___x_2037_ = lean_float_of_nat(v___x_2036_);
return v___x_2037_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__8(void){
_start:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2039_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__7));
v___x_2040_ = l_Lean_stringToMessageData(v___x_2039_);
return v___x_2040_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__13(void){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2048_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2049_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
v___x_2050_ = l_Lean_Name_append(v___x_2049_, v___x_2048_);
return v___x_2050_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__15(void){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__14));
v___x_2053_ = l_Lean_stringToMessageData(v___x_2052_);
return v___x_2053_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__17(void){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__16));
v___x_2056_ = l_Lean_stringToMessageData(v___x_2055_);
return v___x_2056_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__19(void){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__18));
v___x_2059_ = l_Lean_stringToMessageData(v___x_2058_);
return v___x_2059_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__21(void){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__20));
v___x_2062_ = l_Lean_stringToMessageData(v___x_2061_);
return v___x_2062_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__22(void){
_start:
{
lean_object* v___x_2063_; lean_object* v_dummy_2064_; 
v___x_2063_ = lean_box(0);
v_dummy_2064_ = l_Lean_Expr_sort___override(v___x_2063_);
return v_dummy_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher(lean_object* v_altIdx_2074_, lean_object* v_e_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_){
_start:
{
lean_object* v___y_2082_; lean_object* v___y_2101_; lean_object* v___y_2105_; lean_object* v___y_2106_; uint8_t v___y_2107_; lean_object* v___y_2108_; lean_object* v___y_2109_; uint8_t v___y_2110_; lean_object* v___y_2139_; uint8_t v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v_a_2143_; lean_object* v___y_2147_; uint8_t v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; uint8_t v___y_2159_; lean_object* v___y_2160_; uint8_t v___y_2161_; uint8_t v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; lean_object* v_a_2165_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; uint8_t v___y_2180_; uint8_t v___y_2181_; uint8_t v___y_2182_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v_a_2186_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; uint8_t v___y_2194_; uint8_t v___y_2195_; uint8_t v___y_2196_; lean_object* v___y_2197_; lean_object* v___y_2198_; lean_object* v___y_2199_; lean_object* v___y_2200_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; uint8_t v___y_2216_; lean_object* v___y_2217_; uint8_t v___y_2218_; uint8_t v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v_a_2222_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; uint8_t v___y_2240_; uint8_t v___y_2241_; uint8_t v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v_a_2246_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; uint8_t v___y_2254_; uint8_t v___y_2255_; uint8_t v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2271_; lean_object* v___y_2272_; uint8_t v___y_2273_; lean_object* v___y_2274_; uint8_t v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; uint8_t v___y_2281_; uint8_t v___y_2282_; uint8_t v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2285_; uint8_t v___y_2351_; uint8_t v___y_2356_; lean_object* v___y_2361_; uint8_t v___y_2362_; lean_object* v_proof_2363_; lean_object* v___y_2368_; lean_object* v___y_2369_; uint8_t v___y_2370_; lean_object* v___y_2371_; uint8_t v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; uint8_t v___y_2381_; uint8_t v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; uint8_t v___y_2391_; lean_object* v___y_2404_; lean_object* v___y_2405_; uint8_t v___y_2406_; lean_object* v___y_2407_; uint8_t v___y_2408_; lean_object* v___y_2409_; uint8_t v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; uint8_t v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2432_; uint8_t v___y_2433_; uint8_t v___y_2434_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v_a_2438_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; uint8_t v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; uint8_t v___y_2462_; lean_object* v___y_2463_; uint8_t v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2471_; lean_object* v___y_2472_; size_t v___y_2473_; lean_object* v___y_2474_; uint8_t v___y_2475_; lean_object* v___y_2476_; uint8_t v___y_2477_; lean_object* v___y_2478_; uint8_t v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2499_; size_t v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; uint8_t v___y_2503_; uint8_t v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; uint8_t v_fst_2507_; lean_object* v_fst_2508_; lean_object* v_snd_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___x_2533_; uint8_t v___y_2535_; lean_object* v___x_2728_; uint8_t v___x_2729_; 
v___x_2533_ = lean_box(0);
v___x_2728_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__25));
v___x_2729_ = l_Lean_Expr_isAppOf(v_e_2075_, v___x_2728_);
if (v___x_2729_ == 0)
{
lean_object* v___x_2730_; uint8_t v___x_2731_; 
v___x_2730_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__27));
v___x_2731_ = l_Lean_Expr_isAppOf(v_e_2075_, v___x_2730_);
v___y_2535_ = v___x_2731_;
goto v___jp_2534_;
}
else
{
v___y_2535_ = v___x_2729_;
goto v___jp_2534_;
}
v___jp_2081_:
{
if (lean_obj_tag(v___y_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2091_; 
v_a_2083_ = lean_ctor_get(v___y_2082_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___y_2082_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2085_ = v___y_2082_;
v_isShared_2086_ = v_isSharedCheck_2091_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___y_2082_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2091_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v_a_2087_; lean_object* v___x_2089_; 
v_a_2087_ = lean_ctor_get(v_a_2083_, 0);
lean_inc(v_a_2087_);
lean_dec(v_a_2083_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 0, v_a_2087_);
v___x_2089_ = v___x_2085_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2087_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
else
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
v_a_2092_ = lean_ctor_get(v___y_2082_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___y_2082_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2094_ = v___y_2082_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___y_2082_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2097_; 
if (v_isShared_2095_ == 0)
{
v___x_2097_ = v___x_2094_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_a_2092_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
v___jp_2100_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = lean_box(0);
lean_inc(v_a_2079_);
lean_inc_ref(v_a_2078_);
lean_inc(v_a_2077_);
lean_inc_ref(v_a_2076_);
v___x_2103_ = lean_apply_6(v___y_2101_, v___x_2102_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, lean_box(0));
v___y_2082_ = v___x_2103_;
goto v___jp_2081_;
}
v___jp_2104_:
{
if (v___y_2110_ == 0)
{
lean_object* v_toCold_2111_; lean_object* v_options_2112_; uint8_t v_hasTrace_2113_; 
v_toCold_2111_ = lean_ctor_get(v_a_2078_, 0);
v_options_2112_ = lean_ctor_get(v_toCold_2111_, 2);
v_hasTrace_2113_ = lean_ctor_get_uint8(v_options_2112_, sizeof(void*)*1);
if (v_hasTrace_2113_ == 0)
{
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
v___y_2101_ = v___y_2108_;
goto v___jp_2100_;
}
else
{
lean_object* v_inheritedTraceOptions_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; uint8_t v___x_2117_; 
v_inheritedTraceOptions_2114_ = lean_ctor_get(v_toCold_2111_, 11);
v___x_2115_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2109_);
v___x_2116_ = l_Lean_Name_append(v___x_2115_, v___y_2109_);
v___x_2117_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2114_, v_options_2112_, v___x_2116_);
lean_dec(v___x_2116_);
if (v___x_2117_ == 0)
{
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
v___y_2101_ = v___y_2108_;
goto v___jp_2100_;
}
else
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2118_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__3, &l_Lean_Meta_rwMatcher___closed__3_once, _init_l_Lean_Meta_rwMatcher___closed__3);
v___x_2119_ = l_Lean_MessageData_ofConstName(v___y_2105_, v___y_2107_);
v___x_2120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2118_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
v___x_2121_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__5, &l_Lean_Meta_rwMatcher___closed__5_once, _init_l_Lean_Meta_rwMatcher___closed__5);
v___x_2122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2120_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = l_Lean_Exception_toMessageData(v___y_2106_);
v___x_2124_ = l_Lean_indentD(v___x_2123_);
v___x_2125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2122_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2109_, v___x_2125_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2128_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2126_, 1);
lean_inc(v_a_2079_);
lean_inc_ref(v_a_2078_);
lean_inc(v_a_2077_);
lean_inc_ref(v_a_2076_);
v___x_2128_ = lean_apply_6(v___y_2108_, v_a_2127_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, lean_box(0));
v___y_2082_ = v___x_2128_;
goto v___jp_2081_;
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
lean_dec_ref(v___y_2108_);
v_a_2129_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2126_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2126_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
}
}
else
{
lean_object* v___x_2137_; 
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2105_);
v___x_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2137_, 0, v___y_2106_);
return v___x_2137_;
}
}
v___jp_2138_:
{
uint8_t v___x_2144_; 
v___x_2144_ = l_Lean_Exception_isInterrupt(v_a_2143_);
if (v___x_2144_ == 0)
{
uint8_t v___x_2145_; 
lean_inc_ref(v_a_2143_);
v___x_2145_ = l_Lean_Exception_isRuntime(v_a_2143_);
v___y_2105_ = v___y_2139_;
v___y_2106_ = v_a_2143_;
v___y_2107_ = v___y_2140_;
v___y_2108_ = v___y_2141_;
v___y_2109_ = v___y_2142_;
v___y_2110_ = v___x_2145_;
goto v___jp_2104_;
}
else
{
v___y_2105_ = v___y_2139_;
v___y_2106_ = v_a_2143_;
v___y_2107_ = v___y_2140_;
v___y_2108_ = v___y_2141_;
v___y_2109_ = v___y_2142_;
v___y_2110_ = v___x_2144_;
goto v___jp_2104_;
}
}
v___jp_2146_:
{
if (lean_obj_tag(v___y_2151_) == 0)
{
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2147_);
return v___y_2151_;
}
else
{
lean_object* v_a_2152_; 
v_a_2152_ = lean_ctor_get(v___y_2151_, 0);
lean_inc(v_a_2152_);
lean_dec_ref_known(v___y_2151_, 1);
v___y_2139_ = v___y_2147_;
v___y_2140_ = v___y_2148_;
v___y_2141_ = v___y_2149_;
v___y_2142_ = v___y_2150_;
v_a_2143_ = v_a_2152_;
goto v___jp_2138_;
}
}
v___jp_2153_:
{
lean_object* v___x_2166_; double v___x_2167_; double v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2166_ = lean_io_get_num_heartbeats();
v___x_2167_ = lean_float_of_nat(v___y_2158_);
v___x_2168_ = lean_float_of_nat(v___x_2166_);
v___x_2169_ = lean_box_float(v___x_2167_);
v___x_2170_ = lean_box_float(v___x_2168_);
v___x_2171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2169_);
lean_ctor_set(v___x_2171_, 1, v___x_2170_);
v___x_2172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2172_, 0, v_a_2165_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
lean_inc_ref(v___y_2157_);
lean_inc(v___y_2164_);
v___x_2173_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v___y_2164_, v___y_2162_, v___y_2157_, v___y_2156_, v___y_2161_, v___y_2163_, v___y_2154_, v___x_2172_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
v___y_2147_ = v___y_2155_;
v___y_2148_ = v___y_2159_;
v___y_2149_ = v___y_2160_;
v___y_2150_ = v___y_2164_;
v___y_2151_ = v___x_2173_;
goto v___jp_2146_;
}
v___jp_2174_:
{
lean_object* v___x_2187_; 
v___x_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2187_, 0, v_a_2186_);
v___y_2154_ = v___y_2175_;
v___y_2155_ = v___y_2176_;
v___y_2156_ = v___y_2177_;
v___y_2157_ = v___y_2178_;
v___y_2158_ = v___y_2179_;
v___y_2159_ = v___y_2180_;
v___y_2160_ = v___y_2183_;
v___y_2161_ = v___y_2182_;
v___y_2162_ = v___y_2181_;
v___y_2163_ = v___y_2184_;
v___y_2164_ = v___y_2185_;
v_a_2165_ = v___x_2187_;
goto v___jp_2153_;
}
v___jp_2188_:
{
if (lean_obj_tag(v___y_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
v_a_2201_ = lean_ctor_get(v___y_2200_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___y_2200_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___y_2200_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___y_2200_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
lean_ctor_set_tag(v___x_2203_, 1);
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
v___y_2154_ = v___y_2189_;
v___y_2155_ = v___y_2190_;
v___y_2156_ = v___y_2191_;
v___y_2157_ = v___y_2192_;
v___y_2158_ = v___y_2193_;
v___y_2159_ = v___y_2194_;
v___y_2160_ = v___y_2197_;
v___y_2161_ = v___y_2196_;
v___y_2162_ = v___y_2195_;
v___y_2163_ = v___y_2198_;
v___y_2164_ = v___y_2199_;
v_a_2165_ = v___x_2206_;
goto v___jp_2153_;
}
}
}
else
{
lean_object* v_a_2209_; 
v_a_2209_ = lean_ctor_get(v___y_2200_, 0);
lean_inc(v_a_2209_);
lean_dec_ref_known(v___y_2200_, 1);
v___y_2175_ = v___y_2189_;
v___y_2176_ = v___y_2190_;
v___y_2177_ = v___y_2191_;
v___y_2178_ = v___y_2192_;
v___y_2179_ = v___y_2193_;
v___y_2180_ = v___y_2194_;
v___y_2181_ = v___y_2195_;
v___y_2182_ = v___y_2196_;
v___y_2183_ = v___y_2197_;
v___y_2184_ = v___y_2198_;
v___y_2185_ = v___y_2199_;
v_a_2186_ = v_a_2209_;
goto v___jp_2174_;
}
}
v___jp_2210_:
{
lean_object* v___x_2223_; double v___x_2224_; double v___x_2225_; double v___x_2226_; double v___x_2227_; double v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2223_ = lean_io_mono_nanos_now();
v___x_2224_ = lean_float_of_nat(v___y_2215_);
v___x_2225_ = lean_float_once(&l_Lean_Meta_rwMatcher___closed__6, &l_Lean_Meta_rwMatcher___closed__6_once, _init_l_Lean_Meta_rwMatcher___closed__6);
v___x_2226_ = lean_float_div(v___x_2224_, v___x_2225_);
v___x_2227_ = lean_float_of_nat(v___x_2223_);
v___x_2228_ = lean_float_div(v___x_2227_, v___x_2225_);
v___x_2229_ = lean_box_float(v___x_2226_);
v___x_2230_ = lean_box_float(v___x_2228_);
v___x_2231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2229_);
lean_ctor_set(v___x_2231_, 1, v___x_2230_);
v___x_2232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2232_, 0, v_a_2222_);
lean_ctor_set(v___x_2232_, 1, v___x_2231_);
lean_inc_ref(v___y_2214_);
lean_inc(v___y_2221_);
v___x_2233_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v___y_2221_, v___y_2219_, v___y_2214_, v___y_2213_, v___y_2218_, v___y_2220_, v___y_2211_, v___x_2232_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
v___y_2147_ = v___y_2212_;
v___y_2148_ = v___y_2216_;
v___y_2149_ = v___y_2217_;
v___y_2150_ = v___y_2221_;
v___y_2151_ = v___x_2233_;
goto v___jp_2146_;
}
v___jp_2234_:
{
lean_object* v___x_2247_; 
v___x_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2247_, 0, v_a_2246_);
v___y_2211_ = v___y_2235_;
v___y_2212_ = v___y_2236_;
v___y_2213_ = v___y_2237_;
v___y_2214_ = v___y_2239_;
v___y_2215_ = v___y_2238_;
v___y_2216_ = v___y_2240_;
v___y_2217_ = v___y_2243_;
v___y_2218_ = v___y_2242_;
v___y_2219_ = v___y_2241_;
v___y_2220_ = v___y_2244_;
v___y_2221_ = v___y_2245_;
v_a_2222_ = v___x_2247_;
goto v___jp_2210_;
}
v___jp_2248_:
{
if (lean_obj_tag(v___y_2260_) == 0)
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2268_; 
v_a_2261_ = lean_ctor_get(v___y_2260_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___y_2260_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___y_2260_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___y_2260_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
lean_ctor_set_tag(v___x_2263_, 1);
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
v___y_2211_ = v___y_2249_;
v___y_2212_ = v___y_2250_;
v___y_2213_ = v___y_2251_;
v___y_2214_ = v___y_2253_;
v___y_2215_ = v___y_2252_;
v___y_2216_ = v___y_2254_;
v___y_2217_ = v___y_2257_;
v___y_2218_ = v___y_2256_;
v___y_2219_ = v___y_2255_;
v___y_2220_ = v___y_2258_;
v___y_2221_ = v___y_2259_;
v_a_2222_ = v___x_2266_;
goto v___jp_2210_;
}
}
}
else
{
lean_object* v_a_2269_; 
v_a_2269_ = lean_ctor_get(v___y_2260_, 0);
lean_inc(v_a_2269_);
lean_dec_ref_known(v___y_2260_, 1);
v___y_2235_ = v___y_2249_;
v___y_2236_ = v___y_2250_;
v___y_2237_ = v___y_2251_;
v___y_2238_ = v___y_2252_;
v___y_2239_ = v___y_2253_;
v___y_2240_ = v___y_2254_;
v___y_2241_ = v___y_2255_;
v___y_2242_ = v___y_2256_;
v___y_2243_ = v___y_2257_;
v___y_2244_ = v___y_2258_;
v___y_2245_ = v___y_2259_;
v_a_2246_ = v_a_2269_;
goto v___jp_2234_;
}
}
v___jp_2270_:
{
lean_object* v___x_2286_; lean_object* v_a_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; 
v___x_2286_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg(v_a_2079_);
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_a_2287_);
lean_dec_ref(v___x_2286_);
v___x_2288_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2289_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v___y_2277_, v___x_2288_);
if (v___x_2289_ == 0)
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2290_ = lean_io_mono_nanos_now();
lean_inc(v_a_2079_);
lean_inc_ref(v_a_2078_);
lean_inc(v_a_2077_);
lean_inc_ref(v_a_2076_);
v___x_2291_ = lean_infer_type(v___y_2280_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v_a_2292_; uint8_t v___x_2293_; lean_object* v___x_2294_; 
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_a_2292_);
lean_dec_ref_known(v___x_2291_, 1);
v___x_2293_ = 0;
v___x_2294_ = l_Lean_Meta_forallMetaTelescope(v_a_2292_, v___x_2293_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v_snd_2296_; lean_object* v_fst_2297_; lean_object* v_snd_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2316_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref_known(v___x_2294_, 1);
v_snd_2296_ = lean_ctor_get(v_a_2295_, 1);
lean_inc(v_snd_2296_);
v_fst_2297_ = lean_ctor_get(v_a_2295_, 0);
lean_inc(v_fst_2297_);
lean_dec(v_a_2295_);
v_snd_2298_ = lean_ctor_get(v_snd_2296_, 1);
v_isSharedCheck_2316_ = !lean_is_exclusive(v_snd_2296_);
if (v_isSharedCheck_2316_ == 0)
{
lean_object* v_unused_2317_; 
v_unused_2317_ = lean_ctor_get(v_snd_2296_, 0);
lean_dec(v_unused_2317_);
v___x_2300_ = v_snd_2296_;
v_isShared_2301_ = v_isSharedCheck_2316_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_snd_2298_);
lean_dec(v_snd_2296_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2316_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; uint8_t v___x_2304_; 
v___x_2302_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2285_);
v___x_2303_ = l_Lean_Name_append(v___x_2302_, v___y_2285_);
v___x_2304_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2278_, v___y_2277_, v___x_2303_);
lean_dec(v___x_2303_);
if (v___x_2304_ == 0)
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
lean_del_object(v___x_2300_);
v___x_2305_ = lean_box(0);
v___x_2306_ = l_Lean_Meta_rwMatcher___lam__2(v___y_2275_, v___y_2274_, v_fst_2297_, v___y_2272_, v_e_2075_, v___y_2273_, v_snd_2298_, v___x_2305_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
lean_dec(v_snd_2298_);
v___y_2249_ = v___y_2271_;
v___y_2250_ = v___y_2276_;
v___y_2251_ = v___y_2277_;
v___y_2252_ = v___x_2290_;
v___y_2253_ = v___y_2279_;
v___y_2254_ = v___y_2281_;
v___y_2255_ = v___y_2282_;
v___y_2256_ = v___y_2283_;
v___y_2257_ = v___y_2284_;
v___y_2258_ = v_a_2287_;
v___y_2259_ = v___y_2285_;
v___y_2260_ = v___x_2306_;
goto v___jp_2248_;
}
else
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2310_; 
v___x_2307_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2298_);
v___x_2308_ = l_Lean_indentExpr(v_snd_2298_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set_tag(v___x_2300_, 7);
lean_ctor_set(v___x_2300_, 1, v___x_2308_);
lean_ctor_set(v___x_2300_, 0, v___x_2307_);
v___x_2310_ = v___x_2300_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v___x_2307_);
lean_ctor_set(v_reuseFailAlloc_2315_, 1, v___x_2308_);
v___x_2310_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
lean_object* v___x_2311_; 
lean_inc(v___y_2285_);
v___x_2311_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2285_, v___x_2310_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2313_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
lean_dec_ref_known(v___x_2311_, 1);
v___x_2313_ = l_Lean_Meta_rwMatcher___lam__2(v___y_2275_, v___y_2274_, v_fst_2297_, v___y_2272_, v_e_2075_, v___y_2273_, v_snd_2298_, v_a_2312_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
lean_dec(v_snd_2298_);
v___y_2249_ = v___y_2271_;
v___y_2250_ = v___y_2276_;
v___y_2251_ = v___y_2277_;
v___y_2252_ = v___x_2290_;
v___y_2253_ = v___y_2279_;
v___y_2254_ = v___y_2281_;
v___y_2255_ = v___y_2282_;
v___y_2256_ = v___y_2283_;
v___y_2257_ = v___y_2284_;
v___y_2258_ = v_a_2287_;
v___y_2259_ = v___y_2285_;
v___y_2260_ = v___x_2313_;
goto v___jp_2248_;
}
else
{
lean_object* v_a_2314_; 
lean_dec(v_snd_2298_);
lean_dec(v_fst_2297_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2272_);
lean_dec_ref(v_e_2075_);
v_a_2314_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2314_);
lean_dec_ref_known(v___x_2311_, 1);
v___y_2235_ = v___y_2271_;
v___y_2236_ = v___y_2276_;
v___y_2237_ = v___y_2277_;
v___y_2238_ = v___x_2290_;
v___y_2239_ = v___y_2279_;
v___y_2240_ = v___y_2281_;
v___y_2241_ = v___y_2282_;
v___y_2242_ = v___y_2283_;
v___y_2243_ = v___y_2284_;
v___y_2244_ = v_a_2287_;
v___y_2245_ = v___y_2285_;
v_a_2246_ = v_a_2314_;
goto v___jp_2234_;
}
}
}
}
}
else
{
lean_object* v_a_2318_; 
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2272_);
lean_dec_ref(v_e_2075_);
v_a_2318_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2318_);
lean_dec_ref_known(v___x_2294_, 1);
v___y_2235_ = v___y_2271_;
v___y_2236_ = v___y_2276_;
v___y_2237_ = v___y_2277_;
v___y_2238_ = v___x_2290_;
v___y_2239_ = v___y_2279_;
v___y_2240_ = v___y_2281_;
v___y_2241_ = v___y_2282_;
v___y_2242_ = v___y_2283_;
v___y_2243_ = v___y_2284_;
v___y_2244_ = v_a_2287_;
v___y_2245_ = v___y_2285_;
v_a_2246_ = v_a_2318_;
goto v___jp_2234_;
}
}
else
{
lean_object* v_a_2319_; 
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2272_);
lean_dec_ref(v_e_2075_);
v_a_2319_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_a_2319_);
lean_dec_ref_known(v___x_2291_, 1);
v___y_2235_ = v___y_2271_;
v___y_2236_ = v___y_2276_;
v___y_2237_ = v___y_2277_;
v___y_2238_ = v___x_2290_;
v___y_2239_ = v___y_2279_;
v___y_2240_ = v___y_2281_;
v___y_2241_ = v___y_2282_;
v___y_2242_ = v___y_2283_;
v___y_2243_ = v___y_2284_;
v___y_2244_ = v_a_2287_;
v___y_2245_ = v___y_2285_;
v_a_2246_ = v_a_2319_;
goto v___jp_2234_;
}
}
else
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2320_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2079_);
lean_inc_ref(v_a_2078_);
lean_inc(v_a_2077_);
lean_inc_ref(v_a_2076_);
v___x_2321_ = lean_infer_type(v___y_2280_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; uint8_t v___x_2323_; lean_object* v___x_2324_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2322_);
lean_dec_ref_known(v___x_2321_, 1);
v___x_2323_ = 0;
v___x_2324_ = l_Lean_Meta_forallMetaTelescope(v_a_2322_, v___x_2323_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; lean_object* v_snd_2326_; lean_object* v_fst_2327_; lean_object* v_snd_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2346_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_a_2325_);
lean_dec_ref_known(v___x_2324_, 1);
v_snd_2326_ = lean_ctor_get(v_a_2325_, 1);
lean_inc(v_snd_2326_);
v_fst_2327_ = lean_ctor_get(v_a_2325_, 0);
lean_inc(v_fst_2327_);
lean_dec(v_a_2325_);
v_snd_2328_ = lean_ctor_get(v_snd_2326_, 1);
v_isSharedCheck_2346_ = !lean_is_exclusive(v_snd_2326_);
if (v_isSharedCheck_2346_ == 0)
{
lean_object* v_unused_2347_; 
v_unused_2347_ = lean_ctor_get(v_snd_2326_, 0);
lean_dec(v_unused_2347_);
v___x_2330_ = v_snd_2326_;
v_isShared_2331_ = v_isSharedCheck_2346_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_snd_2328_);
lean_dec(v_snd_2326_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2346_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; uint8_t v___x_2334_; 
v___x_2332_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2285_);
v___x_2333_ = l_Lean_Name_append(v___x_2332_, v___y_2285_);
v___x_2334_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2278_, v___y_2277_, v___x_2333_);
lean_dec(v___x_2333_);
if (v___x_2334_ == 0)
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
lean_del_object(v___x_2330_);
v___x_2335_ = lean_box(0);
v___x_2336_ = l_Lean_Meta_rwMatcher___lam__3(v___y_2275_, v___y_2274_, v_fst_2327_, v___y_2272_, v_e_2075_, v___y_2273_, v_snd_2328_, v___x_2335_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
lean_dec(v_snd_2328_);
v___y_2189_ = v___y_2271_;
v___y_2190_ = v___y_2276_;
v___y_2191_ = v___y_2277_;
v___y_2192_ = v___y_2279_;
v___y_2193_ = v___x_2320_;
v___y_2194_ = v___y_2281_;
v___y_2195_ = v___y_2282_;
v___y_2196_ = v___y_2283_;
v___y_2197_ = v___y_2284_;
v___y_2198_ = v_a_2287_;
v___y_2199_ = v___y_2285_;
v___y_2200_ = v___x_2336_;
goto v___jp_2188_;
}
else
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2340_; 
v___x_2337_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2328_);
v___x_2338_ = l_Lean_indentExpr(v_snd_2328_);
if (v_isShared_2331_ == 0)
{
lean_ctor_set_tag(v___x_2330_, 7);
lean_ctor_set(v___x_2330_, 1, v___x_2338_);
lean_ctor_set(v___x_2330_, 0, v___x_2337_);
v___x_2340_ = v___x_2330_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v___x_2337_);
lean_ctor_set(v_reuseFailAlloc_2345_, 1, v___x_2338_);
v___x_2340_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
lean_object* v___x_2341_; 
lean_inc(v___y_2285_);
v___x_2341_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2285_, v___x_2340_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v___x_2343_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_a_2342_);
lean_dec_ref_known(v___x_2341_, 1);
v___x_2343_ = l_Lean_Meta_rwMatcher___lam__3(v___y_2275_, v___y_2274_, v_fst_2327_, v___y_2272_, v_e_2075_, v___y_2273_, v_snd_2328_, v_a_2342_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
lean_dec(v_snd_2328_);
v___y_2189_ = v___y_2271_;
v___y_2190_ = v___y_2276_;
v___y_2191_ = v___y_2277_;
v___y_2192_ = v___y_2279_;
v___y_2193_ = v___x_2320_;
v___y_2194_ = v___y_2281_;
v___y_2195_ = v___y_2282_;
v___y_2196_ = v___y_2283_;
v___y_2197_ = v___y_2284_;
v___y_2198_ = v_a_2287_;
v___y_2199_ = v___y_2285_;
v___y_2200_ = v___x_2343_;
goto v___jp_2188_;
}
else
{
lean_object* v_a_2344_; 
lean_dec(v_snd_2328_);
lean_dec(v_fst_2327_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2272_);
lean_dec_ref(v_e_2075_);
v_a_2344_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_a_2344_);
lean_dec_ref_known(v___x_2341_, 1);
v___y_2175_ = v___y_2271_;
v___y_2176_ = v___y_2276_;
v___y_2177_ = v___y_2277_;
v___y_2178_ = v___y_2279_;
v___y_2179_ = v___x_2320_;
v___y_2180_ = v___y_2281_;
v___y_2181_ = v___y_2282_;
v___y_2182_ = v___y_2283_;
v___y_2183_ = v___y_2284_;
v___y_2184_ = v_a_2287_;
v___y_2185_ = v___y_2285_;
v_a_2186_ = v_a_2344_;
goto v___jp_2174_;
}
}
}
}
}
else
{
lean_object* v_a_2348_; 
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2272_);
lean_dec_ref(v_e_2075_);
v_a_2348_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_a_2348_);
lean_dec_ref_known(v___x_2324_, 1);
v___y_2175_ = v___y_2271_;
v___y_2176_ = v___y_2276_;
v___y_2177_ = v___y_2277_;
v___y_2178_ = v___y_2279_;
v___y_2179_ = v___x_2320_;
v___y_2180_ = v___y_2281_;
v___y_2181_ = v___y_2282_;
v___y_2182_ = v___y_2283_;
v___y_2183_ = v___y_2284_;
v___y_2184_ = v_a_2287_;
v___y_2185_ = v___y_2285_;
v_a_2186_ = v_a_2348_;
goto v___jp_2174_;
}
}
else
{
lean_object* v_a_2349_; 
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2272_);
lean_dec_ref(v_e_2075_);
v_a_2349_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2349_);
lean_dec_ref_known(v___x_2321_, 1);
v___y_2175_ = v___y_2271_;
v___y_2176_ = v___y_2276_;
v___y_2177_ = v___y_2277_;
v___y_2178_ = v___y_2279_;
v___y_2179_ = v___x_2320_;
v___y_2180_ = v___y_2281_;
v___y_2181_ = v___y_2282_;
v___y_2182_ = v___y_2283_;
v___y_2183_ = v___y_2284_;
v___y_2184_ = v_a_2287_;
v___y_2185_ = v___y_2285_;
v_a_2186_ = v_a_2349_;
goto v___jp_2174_;
}
}
}
v___jp_2350_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2352_ = lean_box(0);
v___x_2353_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2353_, 0, v_e_2075_);
lean_ctor_set(v___x_2353_, 1, v___x_2352_);
lean_ctor_set_uint8(v___x_2353_, sizeof(void*)*2, v___y_2351_);
v___x_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
return v___x_2354_;
}
v___jp_2355_:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2357_ = lean_box(0);
v___x_2358_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2358_, 0, v_e_2075_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
lean_ctor_set_uint8(v___x_2358_, sizeof(void*)*2, v___y_2356_);
v___x_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
return v___x_2359_;
}
v___jp_2360_:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2364_, 0, v_proof_2363_);
v___x_2365_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2365_, 0, v___y_2361_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
lean_ctor_set_uint8(v___x_2365_, sizeof(void*)*2, v___y_2362_);
v___x_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
return v___x_2366_;
}
v___jp_2367_:
{
if (lean_obj_tag(v___y_2374_) == 0)
{
lean_object* v_a_2375_; 
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2368_);
v_a_2375_ = lean_ctor_get(v___y_2374_, 0);
lean_inc(v_a_2375_);
lean_dec_ref_known(v___y_2374_, 1);
v___y_2361_ = v___y_2369_;
v___y_2362_ = v___y_2372_;
v_proof_2363_ = v_a_2375_;
goto v___jp_2360_;
}
else
{
lean_object* v_a_2376_; 
lean_dec_ref(v___y_2369_);
v_a_2376_ = lean_ctor_get(v___y_2374_, 0);
lean_inc(v_a_2376_);
lean_dec_ref_known(v___y_2374_, 1);
v___y_2139_ = v___y_2368_;
v___y_2140_ = v___y_2370_;
v___y_2141_ = v___y_2371_;
v___y_2142_ = v___y_2373_;
v_a_2143_ = v_a_2376_;
goto v___jp_2138_;
}
}
v___jp_2377_:
{
if (v___y_2391_ == 0)
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
lean_dec_ref(v___y_2387_);
v___x_2392_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_2393_ = l_Lean_MessageData_ofExpr(v___y_2388_);
v___x_2394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2392_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
v___x_2395_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_2396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2394_);
lean_ctor_set(v___x_2396_, 1, v___x_2395_);
v___x_2397_ = l_Lean_Exception_toMessageData(v___y_2378_);
v___x_2398_ = l_Lean_indentD(v___x_2397_);
v___x_2399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2396_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
v___x_2400_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_2401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2399_);
lean_ctor_set(v___x_2401_, 1, v___x_2400_);
v___x_2402_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2401_, v___y_2390_, v___y_2386_, v___y_2384_, v___y_2380_);
v___y_2368_ = v___y_2379_;
v___y_2369_ = v___y_2385_;
v___y_2370_ = v___y_2381_;
v___y_2371_ = v___y_2389_;
v___y_2372_ = v___y_2382_;
v___y_2373_ = v___y_2383_;
v___y_2374_ = v___x_2402_;
goto v___jp_2367_;
}
else
{
lean_dec_ref(v___y_2388_);
lean_dec_ref(v___y_2378_);
v___y_2368_ = v___y_2379_;
v___y_2369_ = v___y_2385_;
v___y_2370_ = v___y_2381_;
v___y_2371_ = v___y_2389_;
v___y_2372_ = v___y_2382_;
v___y_2373_ = v___y_2383_;
v___y_2374_ = v___y_2387_;
goto v___jp_2367_;
}
}
v___jp_2403_:
{
lean_object* v___x_2416_; lean_object* v_a_2417_; lean_object* v___x_2418_; 
v___x_2416_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_2404_, v___y_2413_);
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
lean_inc(v_a_2417_);
lean_dec_ref(v___x_2416_);
v___x_2418_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_2407_, v___y_2413_);
if (v___y_2406_ == 0)
{
lean_object* v_a_2419_; 
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2405_);
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
lean_inc(v_a_2419_);
lean_dec_ref(v___x_2418_);
v___y_2361_ = v_a_2417_;
v___y_2362_ = v___y_2410_;
v_proof_2363_ = v_a_2419_;
goto v___jp_2360_;
}
else
{
lean_object* v_a_2420_; lean_object* v___x_2421_; 
v_a_2420_ = lean_ctor_get(v___x_2418_, 0);
lean_inc_n(v_a_2420_, 2);
lean_dec_ref(v___x_2418_);
v___x_2421_ = l_Lean_Meta_mkEqOfHEq(v_a_2420_, v___y_2410_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_dec(v_a_2420_);
v___y_2368_ = v___y_2405_;
v___y_2369_ = v_a_2417_;
v___y_2370_ = v___y_2408_;
v___y_2371_ = v___y_2409_;
v___y_2372_ = v___y_2410_;
v___y_2373_ = v___y_2411_;
v___y_2374_ = v___x_2421_;
goto v___jp_2367_;
}
else
{
lean_object* v_a_2422_; uint8_t v___x_2423_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
lean_inc(v_a_2422_);
v___x_2423_ = l_Lean_Exception_isInterrupt(v_a_2422_);
if (v___x_2423_ == 0)
{
uint8_t v___x_2424_; 
lean_inc(v_a_2422_);
v___x_2424_ = l_Lean_Exception_isRuntime(v_a_2422_);
v___y_2378_ = v_a_2422_;
v___y_2379_ = v___y_2405_;
v___y_2380_ = v___y_2415_;
v___y_2381_ = v___y_2408_;
v___y_2382_ = v___y_2410_;
v___y_2383_ = v___y_2411_;
v___y_2384_ = v___y_2414_;
v___y_2385_ = v_a_2417_;
v___y_2386_ = v___y_2413_;
v___y_2387_ = v___x_2421_;
v___y_2388_ = v_a_2420_;
v___y_2389_ = v___y_2409_;
v___y_2390_ = v___y_2412_;
v___y_2391_ = v___x_2424_;
goto v___jp_2377_;
}
else
{
v___y_2378_ = v_a_2422_;
v___y_2379_ = v___y_2405_;
v___y_2380_ = v___y_2415_;
v___y_2381_ = v___y_2408_;
v___y_2382_ = v___y_2410_;
v___y_2383_ = v___y_2411_;
v___y_2384_ = v___y_2414_;
v___y_2385_ = v_a_2417_;
v___y_2386_ = v___y_2413_;
v___y_2387_ = v___x_2421_;
v___y_2388_ = v_a_2420_;
v___y_2389_ = v___y_2409_;
v___y_2390_ = v___y_2412_;
v___y_2391_ = v___x_2423_;
goto v___jp_2377_;
}
}
}
}
v___jp_2425_:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; uint8_t v___x_2441_; 
v___x_2439_ = lean_array_get_size(v_a_2438_);
v___x_2440_ = lean_unsigned_to_nat(0u);
v___x_2441_ = lean_nat_dec_eq(v___x_2439_, v___x_2440_);
if (v___x_2441_ == 0)
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v_a_2453_; 
lean_dec_ref(v___y_2430_);
lean_dec_ref(v___y_2426_);
v___x_2442_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
lean_inc(v___y_2428_);
v___x_2443_ = l_Lean_MessageData_ofConstName(v___y_2428_, v___x_2441_);
v___x_2444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2442_);
lean_ctor_set(v___x_2444_, 1, v___x_2443_);
v___x_2445_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_2446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2444_);
lean_ctor_set(v___x_2446_, 1, v___x_2445_);
v___x_2447_ = lean_array_to_list(v_a_2438_);
v___x_2448_ = lean_box(0);
v___x_2449_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_2447_, v___x_2448_);
v___x_2450_ = l_Lean_MessageData_ofList(v___x_2449_);
v___x_2451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2446_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
v___x_2452_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2451_, v___y_2427_, v___y_2432_, v___y_2431_, v___y_2436_);
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_a_2453_);
lean_dec_ref(v___x_2452_);
v___y_2139_ = v___y_2428_;
v___y_2140_ = v___y_2433_;
v___y_2141_ = v___y_2435_;
v___y_2142_ = v___y_2437_;
v_a_2143_ = v_a_2453_;
goto v___jp_2138_;
}
else
{
lean_dec_ref(v_a_2438_);
v___y_2404_ = v___y_2426_;
v___y_2405_ = v___y_2428_;
v___y_2406_ = v___y_2429_;
v___y_2407_ = v___y_2430_;
v___y_2408_ = v___y_2433_;
v___y_2409_ = v___y_2435_;
v___y_2410_ = v___y_2434_;
v___y_2411_ = v___y_2437_;
v___y_2412_ = v___y_2427_;
v___y_2413_ = v___y_2432_;
v___y_2414_ = v___y_2431_;
v___y_2415_ = v___y_2436_;
goto v___jp_2403_;
}
}
v___jp_2454_:
{
if (lean_obj_tag(v___y_2467_) == 0)
{
lean_object* v_a_2468_; 
v_a_2468_ = lean_ctor_get(v___y_2467_, 0);
lean_inc(v_a_2468_);
lean_dec_ref_known(v___y_2467_, 1);
v___y_2426_ = v___y_2455_;
v___y_2427_ = v___y_2457_;
v___y_2428_ = v___y_2456_;
v___y_2429_ = v___y_2458_;
v___y_2430_ = v___y_2459_;
v___y_2431_ = v___y_2461_;
v___y_2432_ = v___y_2460_;
v___y_2433_ = v___y_2462_;
v___y_2434_ = v___y_2464_;
v___y_2435_ = v___y_2463_;
v___y_2436_ = v___y_2465_;
v___y_2437_ = v___y_2466_;
v_a_2438_ = v_a_2468_;
goto v___jp_2425_;
}
else
{
lean_object* v_a_2469_; 
lean_dec_ref(v___y_2459_);
lean_dec_ref(v___y_2455_);
v_a_2469_ = lean_ctor_get(v___y_2467_, 0);
lean_inc(v_a_2469_);
lean_dec_ref_known(v___y_2467_, 1);
v___y_2139_ = v___y_2456_;
v___y_2140_ = v___y_2462_;
v___y_2141_ = v___y_2463_;
v___y_2142_ = v___y_2466_;
v_a_2143_ = v_a_2469_;
goto v___jp_2138_;
}
}
v___jp_2470_:
{
lean_object* v___x_2485_; size_t v_sz_2486_; lean_object* v___x_2487_; 
v___x_2485_ = lean_box(0);
v_sz_2486_ = lean_array_size(v___y_2474_);
v___x_2487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___y_2474_, v_sz_2486_, v___y_2473_, v___x_2485_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; uint8_t v___x_2491_; 
lean_dec_ref_known(v___x_2487_, 1);
v___x_2488_ = lean_unsigned_to_nat(0u);
v___x_2489_ = lean_array_get_size(v___y_2474_);
v___x_2490_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_2491_ = lean_nat_dec_lt(v___x_2488_, v___x_2489_);
if (v___x_2491_ == 0)
{
lean_dec_ref(v___y_2474_);
v___y_2426_ = v___y_2471_;
v___y_2427_ = v___y_2481_;
v___y_2428_ = v___y_2472_;
v___y_2429_ = v___y_2475_;
v___y_2430_ = v___y_2476_;
v___y_2431_ = v___y_2483_;
v___y_2432_ = v___y_2482_;
v___y_2433_ = v___y_2477_;
v___y_2434_ = v___y_2479_;
v___y_2435_ = v___y_2478_;
v___y_2436_ = v___y_2484_;
v___y_2437_ = v___y_2480_;
v_a_2438_ = v___x_2490_;
goto v___jp_2425_;
}
else
{
uint8_t v___x_2492_; 
v___x_2492_ = lean_nat_dec_le(v___x_2489_, v___x_2489_);
if (v___x_2492_ == 0)
{
if (v___x_2491_ == 0)
{
lean_dec_ref(v___y_2474_);
v___y_2426_ = v___y_2471_;
v___y_2427_ = v___y_2481_;
v___y_2428_ = v___y_2472_;
v___y_2429_ = v___y_2475_;
v___y_2430_ = v___y_2476_;
v___y_2431_ = v___y_2483_;
v___y_2432_ = v___y_2482_;
v___y_2433_ = v___y_2477_;
v___y_2434_ = v___y_2479_;
v___y_2435_ = v___y_2478_;
v___y_2436_ = v___y_2484_;
v___y_2437_ = v___y_2480_;
v_a_2438_ = v___x_2490_;
goto v___jp_2425_;
}
else
{
size_t v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = lean_usize_of_nat(v___x_2489_);
v___x_2494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___y_2474_, v___y_2473_, v___x_2493_, v___x_2490_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
lean_dec_ref(v___y_2474_);
v___y_2455_ = v___y_2471_;
v___y_2456_ = v___y_2472_;
v___y_2457_ = v___y_2481_;
v___y_2458_ = v___y_2475_;
v___y_2459_ = v___y_2476_;
v___y_2460_ = v___y_2482_;
v___y_2461_ = v___y_2483_;
v___y_2462_ = v___y_2477_;
v___y_2463_ = v___y_2478_;
v___y_2464_ = v___y_2479_;
v___y_2465_ = v___y_2484_;
v___y_2466_ = v___y_2480_;
v___y_2467_ = v___x_2494_;
goto v___jp_2454_;
}
}
else
{
size_t v___x_2495_; lean_object* v___x_2496_; 
v___x_2495_ = lean_usize_of_nat(v___x_2489_);
v___x_2496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___y_2474_, v___y_2473_, v___x_2495_, v___x_2490_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
lean_dec_ref(v___y_2474_);
v___y_2455_ = v___y_2471_;
v___y_2456_ = v___y_2472_;
v___y_2457_ = v___y_2481_;
v___y_2458_ = v___y_2475_;
v___y_2459_ = v___y_2476_;
v___y_2460_ = v___y_2482_;
v___y_2461_ = v___y_2483_;
v___y_2462_ = v___y_2477_;
v___y_2463_ = v___y_2478_;
v___y_2464_ = v___y_2479_;
v___y_2465_ = v___y_2484_;
v___y_2466_ = v___y_2480_;
v___y_2467_ = v___x_2496_;
goto v___jp_2454_;
}
}
}
else
{
lean_object* v_a_2497_; 
lean_dec_ref(v___y_2476_);
lean_dec_ref(v___y_2474_);
lean_dec_ref(v___y_2471_);
v_a_2497_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_a_2497_);
lean_dec_ref_known(v___x_2487_, 1);
v___y_2139_ = v___y_2472_;
v___y_2140_ = v___y_2477_;
v___y_2141_ = v___y_2478_;
v___y_2142_ = v___y_2480_;
v_a_2143_ = v_a_2497_;
goto v___jp_2138_;
}
}
v___jp_2498_:
{
lean_object* v___x_2514_; 
lean_inc_ref(v_fst_2508_);
lean_inc_ref(v_e_2075_);
v___x_2514_ = l_Lean_Meta_isExprDefEq(v_e_2075_, v_fst_2508_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; uint8_t v___x_2516_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2515_);
lean_dec_ref_known(v___x_2514_, 1);
v___x_2516_ = lean_unbox(v_a_2515_);
lean_dec(v_a_2515_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v_a_2531_; 
lean_dec_ref(v_snd_2509_);
lean_dec_ref(v___y_2502_);
lean_dec_ref(v___y_2501_);
v___x_2517_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_2518_ = l_Lean_MessageData_ofExpr(v_fst_2508_);
v___x_2519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2517_);
lean_ctor_set(v___x_2519_, 1, v___x_2518_);
v___x_2520_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_2521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2519_);
lean_ctor_set(v___x_2521_, 1, v___x_2520_);
lean_inc(v___y_2499_);
v___x_2522_ = l_Lean_MessageData_ofConstName(v___y_2499_, v___y_2503_);
v___x_2523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2521_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
v___x_2524_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_2525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2523_);
lean_ctor_set(v___x_2525_, 1, v___x_2524_);
v___x_2526_ = l_Lean_MessageData_ofExpr(v_e_2075_);
v___x_2527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2525_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
v___x_2528_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_2529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2527_);
lean_ctor_set(v___x_2529_, 1, v___x_2528_);
v___x_2530_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2529_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
lean_inc(v_a_2531_);
lean_dec_ref(v___x_2530_);
v___y_2139_ = v___y_2499_;
v___y_2140_ = v___y_2503_;
v___y_2141_ = v___y_2505_;
v___y_2142_ = v___y_2506_;
v_a_2143_ = v_a_2531_;
goto v___jp_2138_;
}
else
{
lean_dec_ref(v_fst_2508_);
lean_dec_ref(v_e_2075_);
v___y_2471_ = v_snd_2509_;
v___y_2472_ = v___y_2499_;
v___y_2473_ = v___y_2500_;
v___y_2474_ = v___y_2501_;
v___y_2475_ = v_fst_2507_;
v___y_2476_ = v___y_2502_;
v___y_2477_ = v___y_2503_;
v___y_2478_ = v___y_2505_;
v___y_2479_ = v___y_2504_;
v___y_2480_ = v___y_2506_;
v___y_2481_ = v___y_2510_;
v___y_2482_ = v___y_2511_;
v___y_2483_ = v___y_2512_;
v___y_2484_ = v___y_2513_;
goto v___jp_2470_;
}
}
else
{
lean_object* v_a_2532_; 
lean_dec_ref(v_snd_2509_);
lean_dec_ref(v_fst_2508_);
lean_dec_ref(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec_ref(v_e_2075_);
v_a_2532_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2532_);
lean_dec_ref_known(v___x_2514_, 1);
v___y_2139_ = v___y_2499_;
v___y_2140_ = v___y_2503_;
v___y_2141_ = v___y_2505_;
v___y_2142_ = v___y_2506_;
v_a_2143_ = v_a_2532_;
goto v___jp_2138_;
}
}
v___jp_2534_:
{
uint8_t v___x_2536_; 
v___x_2536_ = 1;
if (v___y_2535_ == 0)
{
lean_object* v___x_2537_; lean_object* v___f_2538_; lean_object* v___x_2539_; lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2708_; 
v___x_2537_ = lean_box(v___x_2536_);
lean_inc_ref(v_e_2075_);
v___f_2538_ = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2538_, 0, v_e_2075_);
lean_closure_set(v___f_2538_, 1, v___x_2537_);
v___x_2539_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(v_e_2075_, v_a_2079_);
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2542_ = v___x_2539_;
v_isShared_2543_ = v_isSharedCheck_2708_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2539_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2708_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
uint8_t v___x_2544_; 
v___x_2544_ = lean_unbox(v_a_2540_);
lean_dec(v_a_2540_);
if (v___x_2544_ == 0)
{
lean_object* v_toCold_2545_; lean_object* v_options_2546_; uint8_t v_hasTrace_2547_; 
lean_del_object(v___x_2542_);
lean_dec_ref(v___f_2538_);
lean_dec(v_altIdx_2074_);
v_toCold_2545_ = lean_ctor_get(v_a_2078_, 0);
v_options_2546_ = lean_ctor_get(v_toCold_2545_, 2);
v_hasTrace_2547_ = lean_ctor_get_uint8(v_options_2546_, sizeof(void*)*1);
if (v_hasTrace_2547_ == 0)
{
v___y_2356_ = v___x_2536_;
goto v___jp_2355_;
}
else
{
lean_object* v_inheritedTraceOptions_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; uint8_t v___x_2551_; 
v_inheritedTraceOptions_2548_ = lean_ctor_get(v_toCold_2545_, 11);
v___x_2549_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2550_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2551_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2548_, v_options_2546_, v___x_2550_);
if (v___x_2551_ == 0)
{
v___y_2356_ = v___x_2536_;
goto v___jp_2355_;
}
else
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2552_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__15, &l_Lean_Meta_rwMatcher___closed__15_once, _init_l_Lean_Meta_rwMatcher___closed__15);
lean_inc_ref(v_e_2075_);
v___x_2553_ = l_Lean_indentExpr(v_e_2075_);
v___x_2554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2552_);
lean_ctor_set(v___x_2554_, 1, v___x_2553_);
v___x_2555_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2549_, v___x_2554_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_dec_ref_known(v___x_2555_, 1);
v___y_2356_ = v___x_2536_;
goto v___jp_2355_;
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
lean_dec_ref(v_e_2075_);
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2555_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2555_);
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
}
else
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2564_ = l_Lean_Expr_getAppFn(v_e_2075_);
v___x_2565_ = l_Lean_Expr_constName_x21(v___x_2564_);
lean_inc(v_a_2079_);
lean_inc_ref(v_a_2078_);
lean_inc(v_a_2077_);
lean_inc_ref(v_a_2076_);
lean_inc(v___x_2565_);
v___x_2566_ = lean_get_congr_match_equations_for(v___x_2565_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_a_2567_);
lean_dec_ref_known(v___x_2566_, 1);
v___x_2568_ = lean_array_get_size(v_a_2567_);
v___x_2569_ = lean_nat_dec_lt(v_altIdx_2074_, v___x_2568_);
if (v___x_2569_ == 0)
{
lean_object* v_toCold_2570_; lean_object* v_options_2571_; uint8_t v_hasTrace_2572_; 
lean_dec(v_a_2567_);
lean_dec_ref(v___x_2564_);
lean_dec_ref(v___f_2538_);
v_toCold_2570_ = lean_ctor_get(v_a_2078_, 0);
v_options_2571_ = lean_ctor_get(v_toCold_2570_, 2);
v_hasTrace_2572_ = lean_ctor_get_uint8(v_options_2571_, sizeof(void*)*1);
if (v_hasTrace_2572_ == 0)
{
lean_dec(v___x_2565_);
lean_del_object(v___x_2542_);
lean_dec(v_altIdx_2074_);
v___y_2351_ = v___x_2536_;
goto v___jp_2350_;
}
else
{
lean_object* v_inheritedTraceOptions_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; uint8_t v___x_2576_; 
v_inheritedTraceOptions_2573_ = lean_ctor_get(v_toCold_2570_, 11);
v___x_2574_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2575_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2576_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2573_, v_options_2571_, v___x_2575_);
if (v___x_2576_ == 0)
{
lean_dec(v___x_2565_);
lean_del_object(v___x_2542_);
lean_dec(v_altIdx_2074_);
v___y_2351_ = v___x_2536_;
goto v___jp_2350_;
}
else
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2580_; 
v___x_2577_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__17, &l_Lean_Meta_rwMatcher___closed__17_once, _init_l_Lean_Meta_rwMatcher___closed__17);
v___x_2578_ = l_Nat_reprFast(v_altIdx_2074_);
if (v_isShared_2543_ == 0)
{
lean_ctor_set_tag(v___x_2542_, 3);
lean_ctor_set(v___x_2542_, 0, v___x_2578_);
v___x_2580_ = v___x_2542_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2578_);
v___x_2580_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2581_ = l_Lean_MessageData_ofFormat(v___x_2580_);
v___x_2582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2577_);
lean_ctor_set(v___x_2582_, 1, v___x_2581_);
v___x_2583_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__19, &l_Lean_Meta_rwMatcher___closed__19_once, _init_l_Lean_Meta_rwMatcher___closed__19);
v___x_2584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2582_);
lean_ctor_set(v___x_2584_, 1, v___x_2583_);
v___x_2585_ = l_Nat_reprFast(v___x_2568_);
v___x_2586_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2585_);
v___x_2587_ = l_Lean_MessageData_ofFormat(v___x_2586_);
v___x_2588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2584_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
v___x_2589_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__21, &l_Lean_Meta_rwMatcher___closed__21_once, _init_l_Lean_Meta_rwMatcher___closed__21);
v___x_2590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2588_);
lean_ctor_set(v___x_2590_, 1, v___x_2589_);
v___x_2591_ = l_Lean_MessageData_ofConstName(v___x_2565_, v___x_2569_);
v___x_2592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2590_);
lean_ctor_set(v___x_2592_, 1, v___x_2591_);
v___x_2593_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2574_, v___x_2592_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_dec_ref_known(v___x_2593_, 1);
v___y_2351_ = v___x_2536_;
goto v___jp_2350_;
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_dec_ref(v_e_2075_);
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2593_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2593_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
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
}
}
}
else
{
lean_object* v_toCold_2603_; lean_object* v_options_2604_; lean_object* v_inheritedTraceOptions_2605_; uint8_t v_hasTrace_2606_; lean_object* v_nargs_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v_dummy_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
lean_dec(v___x_2565_);
lean_del_object(v___x_2542_);
v_toCold_2603_ = lean_ctor_get(v_a_2078_, 0);
v_options_2604_ = lean_ctor_get(v_toCold_2603_, 2);
v_inheritedTraceOptions_2605_ = lean_ctor_get(v_toCold_2603_, 11);
v_hasTrace_2606_ = lean_ctor_get_uint8(v_options_2604_, sizeof(void*)*1);
v_nargs_2607_ = l_Lean_Expr_getAppNumArgs(v_e_2075_);
v___x_2608_ = lean_array_get(v___x_2533_, v_a_2567_, v_altIdx_2074_);
lean_dec(v_altIdx_2074_);
lean_dec(v_a_2567_);
v___x_2609_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2610_ = l_Lean_Expr_constLevels_x21(v___x_2564_);
lean_dec_ref(v___x_2564_);
lean_inc(v___x_2608_);
v___x_2611_ = l_Lean_mkConst(v___x_2608_, v___x_2610_);
v_dummy_2612_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__22, &l_Lean_Meta_rwMatcher___closed__22_once, _init_l_Lean_Meta_rwMatcher___closed__22);
lean_inc(v_nargs_2607_);
v___x_2613_ = lean_mk_array(v_nargs_2607_, v_dummy_2612_);
v___x_2614_ = lean_unsigned_to_nat(1u);
v___x_2615_ = lean_nat_sub(v_nargs_2607_, v___x_2614_);
lean_dec(v_nargs_2607_);
lean_inc_ref(v_e_2075_);
v___x_2616_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2075_, v___x_2613_, v___x_2615_);
v___x_2617_ = l_Lean_mkAppN(v___x_2611_, v___x_2616_);
lean_dec_ref(v___x_2616_);
if (v_hasTrace_2606_ == 0)
{
lean_object* v___x_2618_; 
lean_inc(v_a_2079_);
lean_inc_ref(v_a_2078_);
lean_inc(v_a_2077_);
lean_inc_ref(v_a_2076_);
lean_inc_ref(v___x_2617_);
v___x_2618_ = lean_infer_type(v___x_2617_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; uint8_t v___x_2620_; lean_object* v___x_2621_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v___x_2618_, 1);
v___x_2620_ = 0;
v___x_2621_ = l_Lean_Meta_forallMetaTelescope(v_a_2619_, v___x_2620_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2622_; lean_object* v_snd_2623_; lean_object* v_fst_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2662_; 
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_a_2622_);
lean_dec_ref_known(v___x_2621_, 1);
v_snd_2623_ = lean_ctor_get(v_a_2622_, 1);
v_fst_2624_ = lean_ctor_get(v_a_2622_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v_a_2622_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2626_ = v_a_2622_;
v_isShared_2627_ = v_isSharedCheck_2662_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_snd_2623_);
lean_inc(v_fst_2624_);
lean_dec(v_a_2622_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2662_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v_snd_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2660_; 
v_snd_2628_ = lean_ctor_get(v_snd_2623_, 1);
v_isSharedCheck_2660_ = !lean_is_exclusive(v_snd_2623_);
if (v_isSharedCheck_2660_ == 0)
{
lean_object* v_unused_2661_; 
v_unused_2661_ = lean_ctor_get(v_snd_2623_, 0);
lean_dec(v_unused_2661_);
v___x_2630_ = v_snd_2623_;
v_isShared_2631_ = v_isSharedCheck_2660_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_snd_2628_);
lean_dec(v_snd_2623_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2660_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2632_; size_t v_sz_2633_; size_t v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; uint8_t v___x_2638_; 
v___x_2632_ = l_Lean_mkAppN(v___x_2617_, v_fst_2624_);
v_sz_2633_ = lean_array_size(v_fst_2624_);
v___x_2634_ = ((size_t)0ULL);
v___x_2635_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_2633_, v___x_2634_, v_fst_2624_);
v___x_2636_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_2637_ = lean_unsigned_to_nat(4u);
v___x_2638_ = l_Lean_Expr_isAppOfArity(v_snd_2628_, v___x_2636_, v___x_2637_);
if (v___x_2638_ == 0)
{
lean_object* v___x_2639_; lean_object* v___x_2640_; uint8_t v___x_2641_; 
v___x_2639_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_2640_ = lean_unsigned_to_nat(3u);
v___x_2641_ = l_Lean_Expr_isAppOfArity(v_snd_2628_, v___x_2639_, v___x_2640_);
if (v___x_2641_ == 0)
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2645_; 
lean_dec_ref(v___x_2635_);
lean_dec_ref(v___x_2632_);
lean_dec(v_snd_2628_);
lean_dec_ref(v_e_2075_);
v___x_2642_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
lean_inc(v___x_2608_);
v___x_2643_ = l_Lean_MessageData_ofConstName(v___x_2608_, v___y_2535_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set_tag(v___x_2630_, 7);
lean_ctor_set(v___x_2630_, 1, v___x_2643_);
lean_ctor_set(v___x_2630_, 0, v___x_2642_);
v___x_2645_ = v___x_2630_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2642_);
lean_ctor_set(v_reuseFailAlloc_2652_, 1, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
lean_object* v___x_2646_; lean_object* v___x_2648_; 
v___x_2646_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
if (v_isShared_2627_ == 0)
{
lean_ctor_set_tag(v___x_2626_, 7);
lean_ctor_set(v___x_2626_, 1, v___x_2646_);
lean_ctor_set(v___x_2626_, 0, v___x_2645_);
v___x_2648_ = v___x_2626_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2645_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v___x_2646_);
v___x_2648_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
lean_object* v___x_2649_; lean_object* v_a_2650_; 
v___x_2649_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2648_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2650_);
lean_dec_ref(v___x_2649_);
v___y_2139_ = v___x_2608_;
v___y_2140_ = v___y_2535_;
v___y_2141_ = v___f_2538_;
v___y_2142_ = v___x_2609_;
v_a_2143_ = v_a_2650_;
goto v___jp_2138_;
}
}
}
else
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
lean_del_object(v___x_2630_);
lean_del_object(v___x_2626_);
v___x_2653_ = l_Lean_Expr_appFn_x21(v_snd_2628_);
v___x_2654_ = l_Lean_Expr_appArg_x21(v___x_2653_);
lean_dec_ref(v___x_2653_);
v___x_2655_ = l_Lean_Expr_appArg_x21(v_snd_2628_);
lean_dec(v_snd_2628_);
v___y_2499_ = v___x_2608_;
v___y_2500_ = v___x_2634_;
v___y_2501_ = v___x_2635_;
v___y_2502_ = v___x_2632_;
v___y_2503_ = v___y_2535_;
v___y_2504_ = v___x_2536_;
v___y_2505_ = v___f_2538_;
v___y_2506_ = v___x_2609_;
v_fst_2507_ = v___y_2535_;
v_fst_2508_ = v___x_2654_;
v_snd_2509_ = v___x_2655_;
v___y_2510_ = v_a_2076_;
v___y_2511_ = v_a_2077_;
v___y_2512_ = v_a_2078_;
v___y_2513_ = v_a_2079_;
goto v___jp_2498_;
}
}
else
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
lean_del_object(v___x_2630_);
lean_del_object(v___x_2626_);
v___x_2656_ = l_Lean_Expr_appFn_x21(v_snd_2628_);
v___x_2657_ = l_Lean_Expr_appFn_x21(v___x_2656_);
lean_dec_ref(v___x_2656_);
v___x_2658_ = l_Lean_Expr_appArg_x21(v___x_2657_);
lean_dec_ref(v___x_2657_);
v___x_2659_ = l_Lean_Expr_appArg_x21(v_snd_2628_);
lean_dec(v_snd_2628_);
v___y_2499_ = v___x_2608_;
v___y_2500_ = v___x_2634_;
v___y_2501_ = v___x_2635_;
v___y_2502_ = v___x_2632_;
v___y_2503_ = v___y_2535_;
v___y_2504_ = v___x_2536_;
v___y_2505_ = v___f_2538_;
v___y_2506_ = v___x_2609_;
v_fst_2507_ = v___x_2536_;
v_fst_2508_ = v___x_2658_;
v_snd_2509_ = v___x_2659_;
v___y_2510_ = v_a_2076_;
v___y_2511_ = v_a_2077_;
v___y_2512_ = v_a_2078_;
v___y_2513_ = v_a_2079_;
goto v___jp_2498_;
}
}
}
}
else
{
lean_object* v_a_2663_; 
lean_dec_ref(v___x_2617_);
lean_dec_ref(v_e_2075_);
v_a_2663_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_a_2663_);
lean_dec_ref_known(v___x_2621_, 1);
v___y_2139_ = v___x_2608_;
v___y_2140_ = v___y_2535_;
v___y_2141_ = v___f_2538_;
v___y_2142_ = v___x_2609_;
v_a_2143_ = v_a_2663_;
goto v___jp_2138_;
}
}
else
{
lean_object* v_a_2664_; 
lean_dec_ref(v___x_2617_);
lean_dec_ref(v_e_2075_);
v_a_2664_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2664_);
lean_dec_ref_known(v___x_2618_, 1);
v___y_2139_ = v___x_2608_;
v___y_2140_ = v___y_2535_;
v___y_2141_ = v___f_2538_;
v___y_2142_ = v___x_2609_;
v_a_2143_ = v_a_2664_;
goto v___jp_2138_;
}
}
else
{
lean_object* v___x_2665_; lean_object* v___f_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; uint8_t v___x_2669_; 
v___x_2665_ = lean_box(v___y_2535_);
lean_inc_ref(v_e_2075_);
lean_inc(v___x_2608_);
v___f_2666_ = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__1___boxed), 9, 3);
lean_closure_set(v___f_2666_, 0, v___x_2608_);
lean_closure_set(v___f_2666_, 1, v___x_2665_);
lean_closure_set(v___f_2666_, 2, v_e_2075_);
v___x_2667_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1));
v___x_2668_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2669_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2605_, v_options_2604_, v___x_2668_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2670_; uint8_t v___x_2671_; 
v___x_2670_ = l_Lean_trace_profiler;
v___x_2671_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_options_2604_, v___x_2670_);
if (v___x_2671_ == 0)
{
lean_object* v___x_2672_; 
lean_dec_ref(v___f_2666_);
lean_inc(v_a_2079_);
lean_inc_ref(v_a_2078_);
lean_inc(v_a_2077_);
lean_inc_ref(v_a_2076_);
lean_inc_ref(v___x_2617_);
v___x_2672_ = lean_infer_type(v___x_2617_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; uint8_t v___x_2674_; lean_object* v___x_2675_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2673_);
lean_dec_ref_known(v___x_2672_, 1);
v___x_2674_ = 0;
v___x_2675_ = l_Lean_Meta_forallMetaTelescope(v_a_2673_, v___x_2674_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v_snd_2677_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref_known(v___x_2675_, 1);
v_snd_2677_ = lean_ctor_get(v_a_2676_, 1);
lean_inc(v_snd_2677_);
if (v___x_2669_ == 0)
{
lean_object* v_fst_2678_; lean_object* v_snd_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v_fst_2678_ = lean_ctor_get(v_a_2676_, 0);
lean_inc(v_fst_2678_);
lean_dec(v_a_2676_);
v_snd_2679_ = lean_ctor_get(v_snd_2677_, 1);
lean_inc(v_snd_2679_);
lean_dec(v_snd_2677_);
v___x_2680_ = lean_box(0);
lean_inc(v___x_2608_);
v___x_2681_ = l_Lean_Meta_rwMatcher___lam__4(v___x_2536_, v___x_2617_, v_fst_2678_, v___x_2608_, v_e_2075_, v___y_2535_, v_snd_2679_, v___x_2680_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
lean_dec(v_snd_2679_);
v___y_2147_ = v___x_2608_;
v___y_2148_ = v___y_2535_;
v___y_2149_ = v___f_2538_;
v___y_2150_ = v___x_2609_;
v___y_2151_ = v___x_2681_;
goto v___jp_2146_;
}
else
{
lean_object* v_fst_2682_; lean_object* v_snd_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2696_; 
v_fst_2682_ = lean_ctor_get(v_a_2676_, 0);
lean_inc(v_fst_2682_);
lean_dec(v_a_2676_);
v_snd_2683_ = lean_ctor_get(v_snd_2677_, 1);
v_isSharedCheck_2696_ = !lean_is_exclusive(v_snd_2677_);
if (v_isSharedCheck_2696_ == 0)
{
lean_object* v_unused_2697_; 
v_unused_2697_ = lean_ctor_get(v_snd_2677_, 0);
lean_dec(v_unused_2697_);
v___x_2685_ = v_snd_2677_;
v_isShared_2686_ = v_isSharedCheck_2696_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_snd_2683_);
lean_dec(v_snd_2677_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2696_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2690_; 
v___x_2687_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2683_);
v___x_2688_ = l_Lean_indentExpr(v_snd_2683_);
if (v_isShared_2686_ == 0)
{
lean_ctor_set_tag(v___x_2685_, 7);
lean_ctor_set(v___x_2685_, 1, v___x_2688_);
lean_ctor_set(v___x_2685_, 0, v___x_2687_);
v___x_2690_ = v___x_2685_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2687_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v___x_2688_);
v___x_2690_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
lean_object* v___x_2691_; 
v___x_2691_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2609_, v___x_2690_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_a_2692_; lean_object* v___x_2693_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2692_);
lean_dec_ref_known(v___x_2691_, 1);
lean_inc(v___x_2608_);
v___x_2693_ = l_Lean_Meta_rwMatcher___lam__4(v___x_2536_, v___x_2617_, v_fst_2682_, v___x_2608_, v_e_2075_, v___y_2535_, v_snd_2683_, v_a_2692_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
lean_dec(v_snd_2683_);
v___y_2147_ = v___x_2608_;
v___y_2148_ = v___y_2535_;
v___y_2149_ = v___f_2538_;
v___y_2150_ = v___x_2609_;
v___y_2151_ = v___x_2693_;
goto v___jp_2146_;
}
else
{
lean_object* v_a_2694_; 
lean_dec(v_snd_2683_);
lean_dec(v_fst_2682_);
lean_dec_ref(v___x_2617_);
lean_dec_ref(v_e_2075_);
v_a_2694_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2694_);
lean_dec_ref_known(v___x_2691_, 1);
v___y_2139_ = v___x_2608_;
v___y_2140_ = v___y_2535_;
v___y_2141_ = v___f_2538_;
v___y_2142_ = v___x_2609_;
v_a_2143_ = v_a_2694_;
goto v___jp_2138_;
}
}
}
}
}
else
{
lean_object* v_a_2698_; 
lean_dec_ref(v___x_2617_);
lean_dec_ref(v_e_2075_);
v_a_2698_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2698_);
lean_dec_ref_known(v___x_2675_, 1);
v___y_2139_ = v___x_2608_;
v___y_2140_ = v___y_2535_;
v___y_2141_ = v___f_2538_;
v___y_2142_ = v___x_2609_;
v_a_2143_ = v_a_2698_;
goto v___jp_2138_;
}
}
else
{
lean_object* v_a_2699_; 
lean_dec_ref(v___x_2617_);
lean_dec_ref(v_e_2075_);
v_a_2699_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2699_);
lean_dec_ref_known(v___x_2672_, 1);
v___y_2139_ = v___x_2608_;
v___y_2140_ = v___y_2535_;
v___y_2141_ = v___f_2538_;
v___y_2142_ = v___x_2609_;
v_a_2143_ = v_a_2699_;
goto v___jp_2138_;
}
}
else
{
lean_inc_ref(v___x_2617_);
lean_inc(v___x_2608_);
v___y_2271_ = v___f_2666_;
v___y_2272_ = v___x_2608_;
v___y_2273_ = v___y_2535_;
v___y_2274_ = v___x_2617_;
v___y_2275_ = v___x_2536_;
v___y_2276_ = v___x_2608_;
v___y_2277_ = v_options_2604_;
v___y_2278_ = v_inheritedTraceOptions_2605_;
v___y_2279_ = v___x_2667_;
v___y_2280_ = v___x_2617_;
v___y_2281_ = v___y_2535_;
v___y_2282_ = v___x_2536_;
v___y_2283_ = v___x_2669_;
v___y_2284_ = v___f_2538_;
v___y_2285_ = v___x_2609_;
goto v___jp_2270_;
}
}
else
{
lean_inc_ref(v___x_2617_);
lean_inc(v___x_2608_);
v___y_2271_ = v___f_2666_;
v___y_2272_ = v___x_2608_;
v___y_2273_ = v___y_2535_;
v___y_2274_ = v___x_2617_;
v___y_2275_ = v___x_2536_;
v___y_2276_ = v___x_2608_;
v___y_2277_ = v_options_2604_;
v___y_2278_ = v_inheritedTraceOptions_2605_;
v___y_2279_ = v___x_2667_;
v___y_2280_ = v___x_2617_;
v___y_2281_ = v___y_2535_;
v___y_2282_ = v___x_2536_;
v___y_2283_ = v___x_2669_;
v___y_2284_ = v___f_2538_;
v___y_2285_ = v___x_2609_;
goto v___jp_2270_;
}
}
}
}
else
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
lean_dec(v___x_2565_);
lean_dec_ref(v___x_2564_);
lean_del_object(v___x_2542_);
lean_dec_ref(v___f_2538_);
lean_dec_ref(v_e_2075_);
lean_dec(v_altIdx_2074_);
v_a_2700_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2566_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2566_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
}
}
else
{
lean_object* v___x_2709_; 
lean_dec(v_altIdx_2074_);
v___x_2709_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(v_e_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2719_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2712_ = v___x_2709_;
v_isShared_2713_ = v_isSharedCheck_2719_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2709_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2719_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2717_; 
v___x_2714_ = lean_box(0);
v___x_2715_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2715_, 0, v_a_2710_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
lean_ctor_set_uint8(v___x_2715_, sizeof(void*)*2, v___x_2536_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 0, v___x_2715_);
v___x_2717_ = v___x_2712_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v___x_2715_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
v_a_2720_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2709_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2709_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___boxed(lean_object* v_altIdx_2732_, lean_object* v_e_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Lean_Meta_rwMatcher(v_altIdx_2732_, v_e_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
lean_dec(v_a_2737_);
lean_dec_ref(v_a_2736_);
lean_dec(v_a_2735_);
lean_dec_ref(v_a_2734_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(lean_object* v_mvarId_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v___x_2746_; 
v___x_2746_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_mvarId_2740_, v___y_2742_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___boxed(lean_object* v_mvarId_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(v_mvarId_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v_mvarId_2747_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5(lean_object* v_00_u03b1_2754_, lean_object* v_msg_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v_msg_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___boxed(lean_object* v_00_u03b1_2762_, lean_object* v_msg_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5(v_00_u03b1_2762_, v_msg_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14(lean_object* v_00_u03b1_2770_, lean_object* v_x_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v___x_2777_; 
v___x_2777_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(v_x_2771_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___boxed(lean_object* v_00_u03b1_2778_, lean_object* v_x_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14(v_00_u03b1_2778_, v_x_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12(lean_object* v_inst_2786_, lean_object* v_a_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v___x_2793_; 
v___x_2793_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(v_a_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___boxed(lean_object* v_inst_2794_, lean_object* v_a_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12(v_inst_2794_, v_a_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
return v_res_2801_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(lean_object* v_00_u03b2_2802_, lean_object* v_x_2803_, lean_object* v_x_2804_){
_start:
{
uint8_t v___x_2805_; 
v___x_2805_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_x_2803_, v_x_2804_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2806_, lean_object* v_x_2807_, lean_object* v_x_2808_){
_start:
{
uint8_t v_res_2809_; lean_object* v_r_2810_; 
v_res_2809_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(v_00_u03b2_2806_, v_x_2807_, v_x_2808_);
lean_dec(v_x_2808_);
lean_dec_ref(v_x_2807_);
v_r_2810_ = lean_box(v_res_2809_);
return v_r_2810_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5(lean_object* v_00_u03b2_2811_, lean_object* v_x_2812_, size_t v_x_2813_, lean_object* v_x_2814_){
_start:
{
uint8_t v___x_2815_; 
v___x_2815_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_2812_, v_x_2813_, v_x_2814_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b2_2816_, lean_object* v_x_2817_, lean_object* v_x_2818_, lean_object* v_x_2819_){
_start:
{
size_t v_x_88394__boxed_2820_; uint8_t v_res_2821_; lean_object* v_r_2822_; 
v_x_88394__boxed_2820_ = lean_unbox_usize(v_x_2818_);
lean_dec(v_x_2818_);
v_res_2821_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5(v_00_u03b2_2816_, v_x_2817_, v_x_88394__boxed_2820_, v_x_2819_);
lean_dec(v_x_2819_);
lean_dec_ref(v_x_2817_);
v_r_2822_ = lean_box(v_res_2821_);
return v_r_2822_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18(lean_object* v_00_u03b2_2823_, lean_object* v_keys_2824_, lean_object* v_vals_2825_, lean_object* v_heq_2826_, lean_object* v_i_2827_, lean_object* v_k_2828_){
_start:
{
uint8_t v___x_2829_; 
v___x_2829_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(v_keys_2824_, v_i_2827_, v_k_2828_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___boxed(lean_object* v_00_u03b2_2830_, lean_object* v_keys_2831_, lean_object* v_vals_2832_, lean_object* v_heq_2833_, lean_object* v_i_2834_, lean_object* v_k_2835_){
_start:
{
uint8_t v_res_2836_; lean_object* v_r_2837_; 
v_res_2836_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18(v_00_u03b2_2830_, v_keys_2831_, v_vals_2832_, v_heq_2833_, v_i_2834_, v_k_2835_);
lean_dec(v_k_2835_);
lean_dec_ref(v_vals_2832_);
lean_dec_ref(v_keys_2831_);
v_r_2837_ = lean_box(v_res_2836_);
return v_r_2837_;
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
