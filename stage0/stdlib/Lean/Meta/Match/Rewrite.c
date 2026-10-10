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
lean_object* l_Lean_Meta_rwIfWith(lean_object* v_hc_45_, lean_object* v_e_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
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
LEAN_EXPORT void l_Lean_Meta_rwIfWith_0interp(lean_interpreter_value* stack)
{
lean_object* v_hc_45_ = stack[0].m_obj;
lean_object* v_e_46_ = stack[1].m_obj;
lean_object* v_a_47_ = stack[2].m_obj;
lean_object* v_a_48_ = stack[3].m_obj;
lean_object* v_a_49_ = stack[4].m_obj;
lean_object* v_a_50_ = stack[5].m_obj;
lean_object* v_res_368_;
v_res_368_ = l_Lean_Meta_rwIfWith(v_hc_45_, v_e_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
stack->m_obj
 = v_res_368_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwIfWith___boxed(lean_object* v_hc_369_, lean_object* v_e_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_Meta_rwIfWith(v_hc_369_, v_e_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
return v_res_376_;
}
}
lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(lean_object* v_e_377_, lean_object* v___y_378_){
_start:
{
lean_object* v___x_380_; lean_object* v_env_381_; uint8_t v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_380_ = lean_st_ref_get(v___y_378_);
v_env_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc_ref(v_env_381_);
lean_dec(v___x_380_);
v___x_382_ = l_Lean_Meta_isMatcherAppCore(v_env_381_, v_e_377_);
v___x_383_ = lean_box(v___x_382_);
v___x_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT void l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_377_ = stack[0].m_obj;
lean_object* v___y_378_ = stack[1].m_obj;
lean_object* v_res_385_;
v_res_385_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(v_e_377_, v___y_378_);
stack->m_obj
 = v_res_385_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg___boxed(lean_object* v_e_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(v_e_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v_e_386_);
return v_res_389_;
}
}
lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1(lean_object* v_e_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(v_e_390_, v___y_394_);
return v___x_396_;
}
}
LEAN_EXPORT void l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_390_ = stack[0].m_obj;
lean_object* v___y_391_ = stack[1].m_obj;
lean_object* v___y_392_ = stack[2].m_obj;
lean_object* v___y_393_ = stack[3].m_obj;
lean_object* v___y_394_ = stack[4].m_obj;
lean_object* v_res_397_;
v_res_397_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1(v_e_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
stack->m_obj
 = v_res_397_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___boxed(lean_object* v_e_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1(v_e_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec_ref(v_e_398_);
return v_res_404_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(lean_object* v_e_405_, lean_object* v___y_406_){
_start:
{
uint8_t v___x_408_; 
v___x_408_ = l_Lean_Expr_hasMVar(v_e_405_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; 
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v_e_405_);
return v___x_409_;
}
else
{
lean_object* v___x_410_; lean_object* v_mctx_411_; lean_object* v___x_412_; lean_object* v_fst_413_; lean_object* v_snd_414_; lean_object* v___x_415_; lean_object* v_cache_416_; lean_object* v_zetaDeltaFVarIds_417_; lean_object* v_postponed_418_; lean_object* v_diag_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_428_; 
v___x_410_ = lean_st_ref_get(v___y_406_);
v_mctx_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc_ref(v_mctx_411_);
lean_dec(v___x_410_);
v___x_412_ = l_Lean_instantiateMVarsCore(v_mctx_411_, v_e_405_);
v_fst_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_fst_413_);
v_snd_414_ = lean_ctor_get(v___x_412_, 1);
lean_inc(v_snd_414_);
lean_dec_ref(v___x_412_);
v___x_415_ = lean_st_ref_take(v___y_406_);
v_cache_416_ = lean_ctor_get(v___x_415_, 1);
v_zetaDeltaFVarIds_417_ = lean_ctor_get(v___x_415_, 2);
v_postponed_418_ = lean_ctor_get(v___x_415_, 3);
v_diag_419_ = lean_ctor_get(v___x_415_, 4);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_428_ == 0)
{
lean_object* v_unused_429_; 
v_unused_429_ = lean_ctor_get(v___x_415_, 0);
lean_dec(v_unused_429_);
v___x_421_ = v___x_415_;
v_isShared_422_ = v_isSharedCheck_428_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_diag_419_);
lean_inc(v_postponed_418_);
lean_inc(v_zetaDeltaFVarIds_417_);
lean_inc(v_cache_416_);
lean_dec(v___x_415_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_428_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v_snd_414_);
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_snd_414_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_cache_416_);
lean_ctor_set(v_reuseFailAlloc_427_, 2, v_zetaDeltaFVarIds_417_);
lean_ctor_set(v_reuseFailAlloc_427_, 3, v_postponed_418_);
lean_ctor_set(v_reuseFailAlloc_427_, 4, v_diag_419_);
v___x_424_ = v_reuseFailAlloc_427_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_st_ref_put(v___y_406_, v___x_424_);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v_fst_413_);
return v___x_426_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_405_ = stack[0].m_obj;
lean_object* v___y_406_ = stack[1].m_obj;
lean_object* v_res_430_;
v_res_430_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v_e_405_, v___y_406_);
stack->m_obj
 = v_res_430_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg___boxed(lean_object* v_e_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v_e_431_, v___y_432_);
lean_dec(v___y_432_);
return v_res_434_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4(lean_object* v_e_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v_e_435_, v___y_437_);
return v___x_441_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_435_ = stack[0].m_obj;
lean_object* v___y_436_ = stack[1].m_obj;
lean_object* v___y_437_ = stack[2].m_obj;
lean_object* v___y_438_ = stack[3].m_obj;
lean_object* v___y_439_ = stack[4].m_obj;
lean_object* v_res_442_;
v_res_442_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4(v_e_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
stack->m_obj
 = v_res_442_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___boxed(lean_object* v_e_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4(v_e_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
return v_res_449_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_450_ = lean_unsigned_to_nat(32u);
v___x_451_ = lean_mk_empty_array_with_capacity(v___x_450_);
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
return v___x_452_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__1(void){
_start:
{
size_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_453_ = ((size_t)5ULL);
v___x_454_ = lean_unsigned_to_nat(0u);
v___x_455_ = lean_unsigned_to_nat(32u);
v___x_456_ = lean_mk_empty_array_with_capacity(v___x_455_);
v___x_457_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__0);
v___x_458_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v___x_456_);
lean_ctor_set(v___x_458_, 2, v___x_454_);
lean_ctor_set(v___x_458_, 3, v___x_454_);
lean_ctor_set_usize(v___x_458_, 4, v___x_453_);
return v___x_458_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg(lean_object* v___y_459_){
_start:
{
lean_object* v___x_461_; lean_object* v_traceState_462_; lean_object* v_traces_463_; lean_object* v___x_464_; lean_object* v_traceState_465_; lean_object* v_env_466_; lean_object* v_nextMacroScope_467_; lean_object* v_ngen_468_; lean_object* v_auxDeclNGen_469_; lean_object* v_cache_470_; lean_object* v_recordedDeps_471_; lean_object* v_messages_472_; lean_object* v_infoState_473_; lean_object* v_snapshotTasks_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_493_; 
v___x_461_ = lean_st_ref_get(v___y_459_);
v_traceState_462_ = lean_ctor_get(v___x_461_, 4);
lean_inc_ref(v_traceState_462_);
lean_dec(v___x_461_);
v_traces_463_ = lean_ctor_get(v_traceState_462_, 0);
lean_inc_ref(v_traces_463_);
lean_dec_ref(v_traceState_462_);
v___x_464_ = lean_st_ref_take(v___y_459_);
v_traceState_465_ = lean_ctor_get(v___x_464_, 4);
v_env_466_ = lean_ctor_get(v___x_464_, 0);
v_nextMacroScope_467_ = lean_ctor_get(v___x_464_, 1);
v_ngen_468_ = lean_ctor_get(v___x_464_, 2);
v_auxDeclNGen_469_ = lean_ctor_get(v___x_464_, 3);
v_cache_470_ = lean_ctor_get(v___x_464_, 5);
v_recordedDeps_471_ = lean_ctor_get(v___x_464_, 6);
v_messages_472_ = lean_ctor_get(v___x_464_, 7);
v_infoState_473_ = lean_ctor_get(v___x_464_, 8);
v_snapshotTasks_474_ = lean_ctor_get(v___x_464_, 9);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_493_ == 0)
{
v___x_476_ = v___x_464_;
v_isShared_477_ = v_isSharedCheck_493_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_snapshotTasks_474_);
lean_inc(v_infoState_473_);
lean_inc(v_messages_472_);
lean_inc(v_recordedDeps_471_);
lean_inc(v_cache_470_);
lean_inc(v_traceState_465_);
lean_inc(v_auxDeclNGen_469_);
lean_inc(v_ngen_468_);
lean_inc(v_nextMacroScope_467_);
lean_inc(v_env_466_);
lean_dec(v___x_464_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_493_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
uint64_t v_tid_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_491_; 
v_tid_478_ = lean_ctor_get_uint64(v_traceState_465_, sizeof(void*)*1);
v_isSharedCheck_491_ = !lean_is_exclusive(v_traceState_465_);
if (v_isSharedCheck_491_ == 0)
{
lean_object* v_unused_492_; 
v_unused_492_ = lean_ctor_get(v_traceState_465_, 0);
lean_dec(v_unused_492_);
v___x_480_ = v_traceState_465_;
v_isShared_481_ = v_isSharedCheck_491_;
goto v_resetjp_479_;
}
else
{
lean_dec(v_traceState_465_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_491_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; lean_object* v___x_484_; 
v___x_482_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___closed__1);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_482_);
v___x_484_ = v___x_480_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_482_);
lean_ctor_set_uint64(v_reuseFailAlloc_490_, sizeof(void*)*1, v_tid_478_);
v___x_484_ = v_reuseFailAlloc_490_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
lean_object* v___x_486_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 4, v___x_484_);
v___x_486_ = v___x_476_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_env_466_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_nextMacroScope_467_);
lean_ctor_set(v_reuseFailAlloc_489_, 2, v_ngen_468_);
lean_ctor_set(v_reuseFailAlloc_489_, 3, v_auxDeclNGen_469_);
lean_ctor_set(v_reuseFailAlloc_489_, 4, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_489_, 5, v_cache_470_);
lean_ctor_set(v_reuseFailAlloc_489_, 6, v_recordedDeps_471_);
lean_ctor_set(v_reuseFailAlloc_489_, 7, v_messages_472_);
lean_ctor_set(v_reuseFailAlloc_489_, 8, v_infoState_473_);
lean_ctor_set(v_reuseFailAlloc_489_, 9, v_snapshotTasks_474_);
v___x_486_ = v_reuseFailAlloc_489_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = lean_st_ref_put(v___y_459_, v___x_486_);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v_traces_463_);
return v___x_488_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_459_ = stack[0].m_obj;
lean_object* v_res_494_;
v_res_494_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg(v___y_459_);
stack->m_obj
 = v_res_494_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg___boxed(lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg(v___y_495_);
lean_dec(v___y_495_);
return v_res_497_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9(lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg(v___y_501_);
return v___x_503_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_498_ = stack[0].m_obj;
lean_object* v___y_499_ = stack[1].m_obj;
lean_object* v___y_500_ = stack[2].m_obj;
lean_object* v___y_501_ = stack[3].m_obj;
lean_object* v_res_504_;
v_res_504_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9(v___y_498_, v___y_499_, v___y_500_, v___y_501_);
stack->m_obj
 = v_res_504_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___boxed(lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9(v___y_505_, v___y_506_, v___y_507_, v___y_508_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
return v_res_510_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(lean_object* v_opts_511_, lean_object* v_opt_512_){
_start:
{
lean_object* v_name_513_; lean_object* v_defValue_514_; lean_object* v_map_515_; lean_object* v___x_516_; 
v_name_513_ = lean_ctor_get(v_opt_512_, 0);
v_defValue_514_ = lean_ctor_get(v_opt_512_, 1);
v_map_515_ = lean_ctor_get(v_opts_511_, 0);
v___x_516_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_515_, v_name_513_);
if (lean_obj_tag(v___x_516_) == 0)
{
uint8_t v___x_517_; 
v___x_517_ = lean_unbox(v_defValue_514_);
return v___x_517_;
}
else
{
lean_object* v_val_518_; 
v_val_518_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_val_518_);
lean_dec_ref_known(v___x_516_, 1);
if (lean_obj_tag(v_val_518_) == 1)
{
uint8_t v_v_519_; 
v_v_519_ = lean_ctor_get_uint8(v_val_518_, 0);
lean_dec_ref_known(v_val_518_, 0);
return v_v_519_;
}
else
{
uint8_t v___x_520_; 
lean_dec(v_val_518_);
v___x_520_ = lean_unbox(v_defValue_514_);
return v___x_520_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_511_ = stack[0].m_obj;
lean_object* v_opt_512_ = stack[1].m_obj;
uint8_t v_res_521_;
v_res_521_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_opts_511_, v_opt_512_);
stack->m_num = v_res_521_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10___boxed(lean_object* v_opts_522_, lean_object* v_opt_523_){
_start:
{
uint8_t v_res_524_; lean_object* v_r_525_; 
v_res_524_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_opts_522_, v_opt_523_);
lean_dec_ref(v_opt_523_);
lean_dec_ref(v_opts_522_);
v_r_525_ = lean_box(v_res_524_);
return v_r_525_;
}
}
lean_object* l_Lean_Meta_rwMatcher___lam__0(lean_object* v_e_526_, uint8_t v___x_527_, lean_object* v_____r_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_534_ = lean_box(0);
v___x_535_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_535_, 0, v_e_526_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
lean_ctor_set_uint8(v___x_535_, sizeof(void*)*2, v___x_527_);
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
return v___x_537_;
}
}
LEAN_EXPORT void l_Lean_Meta_rwMatcher___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_526_ = stack[0].m_obj;
uint8_t v___x_527_ = stack[1].m_num;
lean_object* v_____r_528_ = stack[2].m_obj;
lean_object* v___y_529_ = stack[3].m_obj;
lean_object* v___y_530_ = stack[4].m_obj;
lean_object* v___y_531_ = stack[5].m_obj;
lean_object* v___y_532_ = stack[6].m_obj;
lean_object* v_res_538_;
v_res_538_ = l_Lean_Meta_rwMatcher___lam__0(v_e_526_, v___x_527_, v_____r_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
stack->m_obj
 = v_res_538_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__0___boxed(lean_object* v_e_539_, lean_object* v___x_540_, lean_object* v_____r_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
uint8_t v___x_84175__boxed_547_; lean_object* v_res_548_; 
v___x_84175__boxed_547_ = lean_unbox(v___x_540_);
v_res_548_ = l_Lean_Meta_rwMatcher___lam__0(v_e_539_, v___x_84175__boxed_547_, v_____r_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
return v_res_548_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__1(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__0));
v___x_551_ = l_Lean_stringToMessageData(v___x_550_);
return v___x_551_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__1___closed__3(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__1___closed__2));
v___x_554_ = l_Lean_stringToMessageData(v___x_553_);
return v___x_554_;
}
}
lean_object* l_Lean_Meta_rwMatcher___lam__1(lean_object* v___x_555_, uint8_t v___y_556_, lean_object* v_e_557_, lean_object* v_x_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_564_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__1, &l_Lean_Meta_rwMatcher___lam__1___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__1);
v___x_565_ = l_Lean_MessageData_ofConstName(v___x_555_, v___y_556_);
v___x_566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_564_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
v___x_567_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__1___closed__3, &l_Lean_Meta_rwMatcher___lam__1___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__1___closed__3);
v___x_568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_566_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
v___x_569_ = l_Lean_indentExpr(v_e_557_);
v___x_570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_568_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
return v___x_571_;
}
}
LEAN_EXPORT void l_Lean_Meta_rwMatcher___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_555_ = stack[0].m_obj;
uint8_t v___y_556_ = stack[1].m_num;
lean_object* v_e_557_ = stack[2].m_obj;
lean_object* v_x_558_ = stack[3].m_obj;
lean_object* v___y_559_ = stack[4].m_obj;
lean_object* v___y_560_ = stack[5].m_obj;
lean_object* v___y_561_ = stack[6].m_obj;
lean_object* v___y_562_ = stack[7].m_obj;
lean_object* v_res_572_;
v_res_572_ = l_Lean_Meta_rwMatcher___lam__1(v___x_555_, v___y_556_, v_e_557_, v_x_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
stack->m_obj
 = v_res_572_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__1___boxed(lean_object* v___x_573_, lean_object* v___y_574_, lean_object* v_e_575_, lean_object* v_x_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
uint8_t v___y_84235__boxed_582_; lean_object* v_res_583_; 
v___y_84235__boxed_582_ = lean_unbox(v___y_574_);
v_res_583_ = l_Lean_Meta_rwMatcher___lam__1(v___x_573_, v___y_84235__boxed_582_, v_e_575_, v_x_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec_ref(v_x_576_);
return v_res_583_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(size_t v_sz_584_, size_t v_i_585_, lean_object* v_bs_586_){
_start:
{
uint8_t v___x_587_; 
v___x_587_ = lean_usize_dec_lt(v_i_585_, v_sz_584_);
if (v___x_587_ == 0)
{
return v_bs_586_;
}
else
{
lean_object* v_v_588_; lean_object* v___x_589_; lean_object* v_bs_x27_590_; lean_object* v___x_591_; size_t v___x_592_; size_t v___x_593_; lean_object* v___x_594_; 
v_v_588_ = lean_array_uget(v_bs_586_, v_i_585_);
v___x_589_ = lean_unsigned_to_nat(0u);
v_bs_x27_590_ = lean_array_uset(v_bs_586_, v_i_585_, v___x_589_);
v___x_591_ = l_Lean_Expr_mvarId_x21(v_v_588_);
lean_dec(v_v_588_);
v___x_592_ = ((size_t)1ULL);
v___x_593_ = lean_usize_add(v_i_585_, v___x_592_);
v___x_594_ = lean_array_uset(v_bs_x27_590_, v_i_585_, v___x_591_);
v_i_585_ = v___x_593_;
v_bs_586_ = v___x_594_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_584_ = stack[0].m_num;
size_t v_i_585_ = stack[1].m_num;
lean_object* v_bs_586_ = stack[2].m_obj;
lean_object* v_res_596_;
v_res_596_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_584_, v_i_585_, v_bs_586_);
stack->m_obj
 = v_res_596_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3___boxed(lean_object* v_sz_597_, lean_object* v_i_598_, lean_object* v_bs_599_){
_start:
{
size_t v_sz_boxed_600_; size_t v_i_boxed_601_; lean_object* v_res_602_; 
v_sz_boxed_600_ = lean_unbox_usize(v_sz_597_);
lean_dec(v_sz_597_);
v_i_boxed_601_ = lean_unbox_usize(v_i_598_);
lean_dec(v_i_598_);
v_res_602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_boxed_600_, v_i_boxed_601_, v_bs_599_);
return v_res_602_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(lean_object* v_msgData_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v___x_609_; lean_object* v_env_610_; uint8_t v___x_611_; lean_object* v_env_612_; lean_object* v___x_613_; lean_object* v_toCold_614_; lean_object* v_mctx_615_; lean_object* v_lctx_616_; lean_object* v_options_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_609_ = lean_st_ref_get(v___y_607_);
v_env_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc_ref(v_env_610_);
lean_dec(v___x_609_);
v___x_611_ = 0;
v_env_612_ = l_Lean_Environment_setRecordingDeps(v_env_610_, v___x_611_);
v___x_613_ = lean_st_ref_get(v___y_605_);
v_toCold_614_ = lean_ctor_get(v___y_606_, 0);
v_mctx_615_ = lean_ctor_get(v___x_613_, 0);
lean_inc_ref(v_mctx_615_);
lean_dec(v___x_613_);
v_lctx_616_ = lean_ctor_get(v___y_604_, 2);
v_options_617_ = lean_ctor_get(v_toCold_614_, 2);
lean_inc_ref(v_options_617_);
lean_inc_ref(v_lctx_616_);
v___x_618_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_618_, 0, v_env_612_);
lean_ctor_set(v___x_618_, 1, v_mctx_615_);
lean_ctor_set(v___x_618_, 2, v_lctx_616_);
lean_ctor_set(v___x_618_, 3, v_options_617_);
v___x_619_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
lean_ctor_set(v___x_619_, 1, v_msgData_603_);
v___x_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_603_ = stack[0].m_obj;
lean_object* v___y_604_ = stack[1].m_obj;
lean_object* v___y_605_ = stack[2].m_obj;
lean_object* v___y_606_ = stack[3].m_obj;
lean_object* v___y_607_ = stack[4].m_obj;
lean_object* v_res_621_;
v_res_621_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msgData_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
stack->m_obj
 = v_res_621_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3___boxed(lean_object* v_msgData_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msgData_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
return v_res_628_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(lean_object* v_msg_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_ref_635_; lean_object* v___x_636_; lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_645_; 
v_ref_635_ = lean_ctor_get(v___y_632_, 2);
v___x_636_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
v_a_637_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_645_ == 0)
{
v___x_639_ = v___x_636_;
v_isShared_640_ = v_isSharedCheck_645_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_636_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_645_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v___x_643_; 
lean_inc(v_ref_635_);
v___x_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_641_, 0, v_ref_635_);
lean_ctor_set(v___x_641_, 1, v_a_637_);
if (v_isShared_640_ == 0)
{
lean_ctor_set_tag(v___x_639_, 1);
lean_ctor_set(v___x_639_, 0, v___x_641_);
v___x_643_ = v___x_639_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_629_ = stack[0].m_obj;
lean_object* v___y_630_ = stack[1].m_obj;
lean_object* v___y_631_ = stack[2].m_obj;
lean_object* v___y_632_ = stack[3].m_obj;
lean_object* v___y_633_ = stack[4].m_obj;
lean_object* v_res_646_;
v_res_646_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v_msg_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
stack->m_obj
 = v_res_646_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg___boxed(lean_object* v_msg_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v_msg_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
return v_res_653_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(lean_object* v_keys_654_, lean_object* v_i_655_, lean_object* v_k_656_){
_start:
{
lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_657_ = lean_array_get_size(v_keys_654_);
v___x_658_ = lean_nat_dec_lt(v_i_655_, v___x_657_);
if (v___x_658_ == 0)
{
lean_dec(v_i_655_);
return v___x_658_;
}
else
{
lean_object* v_k_x27_659_; uint8_t v___x_660_; 
v_k_x27_659_ = lean_array_fget_borrowed(v_keys_654_, v_i_655_);
v___x_660_ = l_Lean_instBEqMVarId_beq(v_k_656_, v_k_x27_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_unsigned_to_nat(1u);
v___x_662_ = lean_nat_add(v_i_655_, v___x_661_);
lean_dec(v_i_655_);
v_i_655_ = v___x_662_;
goto _start;
}
else
{
lean_dec(v_i_655_);
return v___x_658_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_654_ = stack[0].m_obj;
lean_object* v_i_655_ = stack[1].m_obj;
lean_object* v_k_656_ = stack[2].m_obj;
uint8_t v_res_664_;
v_res_664_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(v_keys_654_, v_i_655_, v_k_656_);
stack->m_num = v_res_664_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg___boxed(lean_object* v_keys_665_, lean_object* v_i_666_, lean_object* v_k_667_){
_start:
{
uint8_t v_res_668_; lean_object* v_r_669_; 
v_res_668_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(v_keys_665_, v_i_666_, v_k_667_);
lean_dec(v_k_667_);
lean_dec_ref(v_keys_665_);
v_r_669_ = lean_box(v_res_668_);
return v_r_669_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(lean_object* v_x_670_, size_t v_x_671_, lean_object* v_x_672_){
_start:
{
if (lean_obj_tag(v_x_670_) == 0)
{
lean_object* v_es_673_; lean_object* v___x_674_; size_t v___x_675_; size_t v___x_676_; lean_object* v_j_677_; lean_object* v___x_678_; 
v_es_673_ = lean_ctor_get(v_x_670_, 0);
v___x_674_ = lean_box(2);
v___x_675_ = ((size_t)31ULL);
v___x_676_ = lean_usize_land(v_x_671_, v___x_675_);
v_j_677_ = lean_usize_to_nat(v___x_676_);
v___x_678_ = lean_array_get_borrowed(v___x_674_, v_es_673_, v_j_677_);
lean_dec(v_j_677_);
switch(lean_obj_tag(v___x_678_))
{
case 0:
{
lean_object* v_key_679_; uint8_t v___x_680_; 
v_key_679_ = lean_ctor_get(v___x_678_, 0);
v___x_680_ = l_Lean_instBEqMVarId_beq(v_x_672_, v_key_679_);
return v___x_680_;
}
case 1:
{
lean_object* v_node_681_; size_t v___x_682_; size_t v___x_683_; 
v_node_681_ = lean_ctor_get(v___x_678_, 0);
v___x_682_ = ((size_t)5ULL);
v___x_683_ = lean_usize_shift_right(v_x_671_, v___x_682_);
v_x_670_ = v_node_681_;
v_x_671_ = v___x_683_;
goto _start;
}
default: 
{
uint8_t v___x_685_; 
v___x_685_ = 0;
return v___x_685_;
}
}
}
else
{
lean_object* v_ks_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v_ks_686_ = lean_ctor_get(v_x_670_, 0);
v___x_687_ = lean_unsigned_to_nat(0u);
v___x_688_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(v_ks_686_, v___x_687_, v_x_672_);
return v___x_688_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_670_ = stack[0].m_obj;
size_t v_x_671_ = stack[1].m_num;
lean_object* v_x_672_ = stack[2].m_obj;
uint8_t v_res_689_;
v_res_689_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_670_, v_x_671_, v_x_672_);
stack->m_num = v_res_689_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_690_, lean_object* v_x_691_, lean_object* v_x_692_){
_start:
{
size_t v_x_84449__boxed_693_; uint8_t v_res_694_; lean_object* v_r_695_; 
v_x_84449__boxed_693_ = lean_unbox_usize(v_x_691_);
lean_dec(v_x_691_);
v_res_694_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_690_, v_x_84449__boxed_693_, v_x_692_);
lean_dec(v_x_692_);
lean_dec_ref(v_x_690_);
v_r_695_ = lean_box(v_res_694_);
return v_r_695_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(lean_object* v_x_696_, lean_object* v_x_697_){
_start:
{
uint64_t v___x_698_; size_t v___x_699_; uint8_t v___x_700_; 
v___x_698_ = l_Lean_instHashableMVarId_hash(v_x_697_);
v___x_699_ = lean_uint64_to_usize(v___x_698_);
v___x_700_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_696_, v___x_699_, v_x_697_);
return v___x_700_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_696_ = stack[0].m_obj;
lean_object* v_x_697_ = stack[1].m_obj;
uint8_t v_res_701_;
v_res_701_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_x_696_, v_x_697_);
stack->m_num = v_res_701_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg___boxed(lean_object* v_x_702_, lean_object* v_x_703_){
_start:
{
uint8_t v_res_704_; lean_object* v_r_705_; 
v_res_704_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_x_702_, v_x_703_);
lean_dec(v_x_703_);
lean_dec_ref(v_x_702_);
v_r_705_ = lean_box(v_res_704_);
return v_r_705_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(lean_object* v_mvarId_706_, lean_object* v___y_707_){
_start:
{
lean_object* v___x_709_; lean_object* v_mctx_710_; lean_object* v_eAssignment_711_; uint8_t v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_709_ = lean_st_ref_get(v___y_707_);
v_mctx_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc_ref(v_mctx_710_);
lean_dec(v___x_709_);
v_eAssignment_711_ = lean_ctor_get(v_mctx_710_, 8);
lean_inc_ref(v_eAssignment_711_);
lean_dec_ref(v_mctx_710_);
v___x_712_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_eAssignment_711_, v_mvarId_706_);
lean_dec_ref(v_eAssignment_711_);
v___x_713_ = lean_box(v___x_712_);
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
return v___x_714_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_706_ = stack[0].m_obj;
lean_object* v___y_707_ = stack[1].m_obj;
lean_object* v_res_715_;
v_res_715_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_mvarId_706_, v___y_707_);
stack->m_obj
 = v_res_715_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg___boxed(lean_object* v_mvarId_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_mvarId_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec(v_mvarId_716_);
return v_res_719_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(lean_object* v_as_720_, size_t v_i_721_, size_t v_stop_722_, lean_object* v_b_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_a_730_; uint8_t v___x_734_; 
v___x_734_ = lean_usize_dec_eq(v_i_721_, v_stop_722_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; lean_object* v___x_738_; 
v___x_735_ = lean_array_uget_borrowed(v_as_720_, v_i_721_);
v___x_738_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v___x_735_, v___y_725_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; uint8_t v___x_740_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_738_, 1);
v___x_740_ = lean_unbox(v_a_739_);
lean_dec(v_a_739_);
if (v___x_740_ == 0)
{
goto v___jp_736_;
}
else
{
v_a_730_ = v_b_723_;
goto v___jp_729_;
}
}
else
{
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_741_; uint8_t v___x_742_; 
v_a_741_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_741_);
lean_dec_ref_known(v___x_738_, 1);
v___x_742_ = lean_unbox(v_a_741_);
lean_dec(v_a_741_);
if (v___x_742_ == 0)
{
v_a_730_ = v_b_723_;
goto v___jp_729_;
}
else
{
goto v___jp_736_;
}
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec_ref(v_b_723_);
v_a_743_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_738_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_738_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
v___jp_736_:
{
lean_object* v___x_737_; 
lean_inc(v___x_735_);
v___x_737_ = lean_array_push(v_b_723_, v___x_735_);
v_a_730_ = v___x_737_;
goto v___jp_729_;
}
}
else
{
lean_object* v___x_751_; 
v___x_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_751_, 0, v_b_723_);
return v___x_751_;
}
v___jp_729_:
{
size_t v___x_731_; size_t v___x_732_; 
v___x_731_ = ((size_t)1ULL);
v___x_732_ = lean_usize_add(v_i_721_, v___x_731_);
v_i_721_ = v___x_732_;
v_b_723_ = v_a_730_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_720_ = stack[0].m_obj;
size_t v_i_721_ = stack[1].m_num;
size_t v_stop_722_ = stack[2].m_num;
lean_object* v_b_723_ = stack[3].m_obj;
lean_object* v___y_724_ = stack[4].m_obj;
lean_object* v___y_725_ = stack[5].m_obj;
lean_object* v___y_726_ = stack[6].m_obj;
lean_object* v___y_727_ = stack[7].m_obj;
lean_object* v_res_752_;
v_res_752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v_as_720_, v_i_721_, v_stop_722_, v_b_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
stack->m_obj
 = v_res_752_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8___boxed(lean_object* v_as_753_, lean_object* v_i_754_, lean_object* v_stop_755_, lean_object* v_b_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
size_t v_i_boxed_762_; size_t v_stop_boxed_763_; lean_object* v_res_764_; 
v_i_boxed_762_ = lean_unbox_usize(v_i_754_);
lean_dec(v_i_754_);
v_stop_boxed_763_ = lean_unbox_usize(v_stop_755_);
lean_dec(v_stop_755_);
v_res_764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v_as_753_, v_i_boxed_762_, v_stop_boxed_763_, v_b_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec_ref(v_as_753_);
return v_res_764_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__0));
v___x_767_ = l_Lean_stringToMessageData(v___x_766_);
return v___x_767_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__2));
v___x_770_ = l_Lean_stringToMessageData(v___x_769_);
return v___x_770_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__4));
v___x_773_ = l_Lean_stringToMessageData(v___x_772_);
return v___x_773_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(lean_object* v_as_774_, size_t v_sz_775_, size_t v_i_776_, lean_object* v_b_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_a_784_; uint8_t v___x_788_; 
v___x_788_ = lean_usize_dec_lt(v_i_776_, v_sz_775_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; 
v___x_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_789_, 0, v_b_777_);
return v___x_789_;
}
else
{
lean_object* v___x_790_; lean_object* v___y_792_; lean_object* v___y_794_; lean_object* v___y_796_; lean_object* v_a_797_; lean_object* v___y_799_; lean_object* v___y_800_; uint8_t v___y_801_; lean_object* v___y_817_; lean_object* v___y_818_; uint8_t v___y_819_; lean_object* v___x_834_; 
v___x_790_ = lean_box(0);
v_a_797_ = lean_array_uget_borrowed(v_as_774_, v_i_776_);
v___x_834_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_a_797_, v___y_779_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; uint8_t v___x_836_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_a_835_);
lean_dec_ref_known(v___x_834_, 1);
v___x_836_ = lean_unbox(v_a_835_);
lean_dec(v_a_835_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; 
lean_inc(v_a_797_);
v___x_837_ = l_Lean_MVarId_getType(v_a_797_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; uint8_t v___x_839_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc_n(v_a_838_, 2);
lean_dec_ref_known(v___x_837_, 1);
v___x_839_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_a_838_);
if (v___x_839_ == 0)
{
uint8_t v___x_840_; 
v___x_840_ = l_Lean_Expr_isEq(v_a_838_);
if (v___x_840_ == 0)
{
uint8_t v___x_841_; 
v___x_841_ = l_Lean_Expr_isHEq(v_a_838_);
lean_dec(v_a_838_);
if (v___x_841_ == 0)
{
v_a_784_ = v___x_790_;
goto v___jp_783_;
}
else
{
lean_object* v___x_842_; 
v___x_842_ = l_Lean_Meta_saveState___redArg(v___y_779_, v___y_781_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_844_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_a_843_);
lean_dec_ref_known(v___x_842_, 1);
lean_inc(v_a_797_);
v___x_844_ = l_Lean_MVarId_assumption(v_a_797_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_dec(v_a_843_);
v___y_794_ = v___x_844_;
goto v___jp_793_;
}
else
{
lean_object* v_a_845_; uint8_t v___y_847_; uint8_t v___x_863_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
v___x_863_ = l_Lean_Exception_isInterrupt(v_a_845_);
if (v___x_863_ == 0)
{
uint8_t v___x_864_; 
lean_inc(v_a_845_);
v___x_864_ = l_Lean_Exception_isRuntime(v_a_845_);
v___y_847_ = v___x_864_;
goto v___jp_846_;
}
else
{
v___y_847_ = v___x_863_;
goto v___jp_846_;
}
v___jp_846_:
{
if (v___y_847_ == 0)
{
lean_object* v___x_848_; 
lean_dec_ref_known(v___x_844_, 1);
v___x_848_ = l_Lean_Meta_SavedState_restore___redArg(v_a_843_, v___y_779_, v___y_781_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v___x_849_; 
lean_dec_ref_known(v___x_848_, 1);
v___x_849_ = l_Lean_Meta_saveState___redArg(v___y_779_, v___y_781_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_851_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_a_850_);
lean_dec_ref_known(v___x_849_, 1);
lean_inc(v_a_797_);
v___x_851_ = l_Lean_MVarId_hrefl(v_a_797_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_dec(v_a_850_);
v___y_794_ = v___x_851_;
goto v___jp_793_;
}
else
{
lean_object* v_a_852_; uint8_t v___x_853_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
v___x_853_ = l_Lean_Exception_isInterrupt(v_a_852_);
if (v___x_853_ == 0)
{
uint8_t v___x_854_; 
lean_inc(v_a_852_);
v___x_854_ = l_Lean_Exception_isRuntime(v_a_852_);
v___y_817_ = v___x_851_;
v___y_818_ = v_a_850_;
v___y_819_ = v___x_854_;
goto v___jp_816_;
}
else
{
v___y_817_ = v___x_851_;
v___y_818_ = v_a_850_;
v___y_819_ = v___x_853_;
goto v___jp_816_;
}
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
v_a_855_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_849_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_849_);
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
v___y_794_ = v___x_848_;
goto v___jp_793_;
}
}
else
{
lean_dec(v_a_843_);
v___y_794_ = v___x_844_;
goto v___jp_793_;
}
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
v_a_865_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_842_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_842_);
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
}
else
{
lean_object* v___x_873_; 
lean_dec(v_a_838_);
v___x_873_ = l_Lean_Meta_saveState___redArg(v___y_779_, v___y_781_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_875_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_874_);
lean_dec_ref_known(v___x_873_, 1);
lean_inc(v_a_797_);
v___x_875_ = l_Lean_MVarId_assumption(v_a_797_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_dec(v_a_874_);
v___y_796_ = v___x_875_;
goto v___jp_795_;
}
else
{
lean_object* v_a_876_; uint8_t v___y_878_; uint8_t v___x_894_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
v___x_894_ = l_Lean_Exception_isInterrupt(v_a_876_);
if (v___x_894_ == 0)
{
uint8_t v___x_895_; 
lean_inc(v_a_876_);
v___x_895_ = l_Lean_Exception_isRuntime(v_a_876_);
v___y_878_ = v___x_895_;
goto v___jp_877_;
}
else
{
v___y_878_ = v___x_894_;
goto v___jp_877_;
}
v___jp_877_:
{
if (v___y_878_ == 0)
{
lean_object* v___x_879_; 
lean_dec_ref_known(v___x_875_, 1);
v___x_879_ = l_Lean_Meta_SavedState_restore___redArg(v_a_874_, v___y_779_, v___y_781_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v___x_880_; 
lean_dec_ref_known(v___x_879_, 1);
v___x_880_ = l_Lean_Meta_saveState___redArg(v___y_779_, v___y_781_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_882_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_881_);
lean_dec_ref_known(v___x_880_, 1);
lean_inc(v_a_797_);
v___x_882_ = l_Lean_MVarId_refl(v_a_797_, v___x_788_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_dec(v_a_881_);
v___y_796_ = v___x_882_;
goto v___jp_795_;
}
else
{
lean_object* v_a_883_; uint8_t v___x_884_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
v___x_884_ = l_Lean_Exception_isInterrupt(v_a_883_);
if (v___x_884_ == 0)
{
uint8_t v___x_885_; 
lean_inc(v_a_883_);
v___x_885_ = l_Lean_Exception_isRuntime(v_a_883_);
v___y_799_ = v_a_881_;
v___y_800_ = v___x_882_;
v___y_801_ = v___x_885_;
goto v___jp_798_;
}
else
{
v___y_799_ = v_a_881_;
v___y_800_ = v___x_882_;
v___y_801_ = v___x_884_;
goto v___jp_798_;
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
v_a_886_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_880_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_880_);
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
else
{
v___y_796_ = v___x_879_;
goto v___jp_795_;
}
}
else
{
lean_dec(v_a_874_);
v___y_796_ = v___x_875_;
goto v___jp_795_;
}
}
}
}
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
v_a_896_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_873_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_873_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
else
{
lean_object* v___x_904_; 
lean_dec(v_a_838_);
v___x_904_ = l_Lean_Meta_saveState___redArg(v___y_779_, v___y_781_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v___x_906_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_905_);
lean_dec_ref_known(v___x_904_, 1);
lean_inc(v_a_797_);
v___x_906_ = l_Lean_MVarId_assumption(v_a_797_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_dec(v_a_905_);
v___y_792_ = v___x_906_;
goto v___jp_791_;
}
else
{
lean_object* v_a_907_; uint8_t v___y_909_; uint8_t v___x_924_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
v___x_924_ = l_Lean_Exception_isInterrupt(v_a_907_);
if (v___x_924_ == 0)
{
uint8_t v___x_925_; 
lean_inc(v_a_907_);
v___x_925_ = l_Lean_Exception_isRuntime(v_a_907_);
v___y_909_ = v___x_925_;
goto v___jp_908_;
}
else
{
v___y_909_ = v___x_924_;
goto v___jp_908_;
}
v___jp_908_:
{
if (v___y_909_ == 0)
{
lean_object* v___x_910_; 
lean_dec_ref_known(v___x_906_, 1);
v___x_910_ = l_Lean_Meta_SavedState_restore___redArg(v_a_905_, v___y_779_, v___y_781_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_922_; 
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_922_ == 0)
{
lean_object* v_unused_923_; 
v_unused_923_ = lean_ctor_get(v___x_910_, 0);
lean_dec(v_unused_923_);
v___x_912_ = v___x_910_;
v_isShared_913_ = v_isSharedCheck_922_;
goto v_resetjp_911_;
}
else
{
lean_dec(v___x_910_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_922_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; lean_object* v___x_916_; 
v___x_914_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5);
lean_inc(v_a_797_);
if (v_isShared_913_ == 0)
{
lean_ctor_set_tag(v___x_912_, 1);
lean_ctor_set(v___x_912_, 0, v_a_797_);
v___x_916_ = v___x_912_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_797_);
v___x_916_ = v_reuseFailAlloc_921_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_914_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_917_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_919_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
v___y_792_ = v___x_920_;
goto v___jp_791_;
}
}
}
else
{
v___y_792_ = v___x_910_;
goto v___jp_791_;
}
}
else
{
lean_dec(v_a_905_);
v___y_792_ = v___x_906_;
goto v___jp_791_;
}
}
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
v_a_926_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_904_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_904_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
v_a_934_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_837_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_837_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
else
{
v_a_784_ = v___x_790_;
goto v___jp_783_;
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
v_a_942_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_834_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_834_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
v___jp_791_:
{
if (lean_obj_tag(v___y_792_) == 0)
{
lean_dec_ref_known(v___y_792_, 1);
v_a_784_ = v___x_790_;
goto v___jp_783_;
}
else
{
return v___y_792_;
}
}
v___jp_793_:
{
if (lean_obj_tag(v___y_794_) == 0)
{
lean_dec_ref_known(v___y_794_, 1);
v_a_784_ = v___x_790_;
goto v___jp_783_;
}
else
{
return v___y_794_;
}
}
v___jp_795_:
{
if (lean_obj_tag(v___y_796_) == 0)
{
lean_dec_ref_known(v___y_796_, 1);
v_a_784_ = v___x_790_;
goto v___jp_783_;
}
else
{
return v___y_796_;
}
}
v___jp_798_:
{
if (v___y_801_ == 0)
{
lean_object* v___x_802_; 
lean_dec_ref(v___y_800_);
v___x_802_ = l_Lean_Meta_SavedState_restore___redArg(v___y_799_, v___y_779_, v___y_781_);
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
lean_inc(v_a_797_);
if (v_isShared_805_ == 0)
{
lean_ctor_set_tag(v___x_804_, 1);
lean_ctor_set(v___x_804_, 0, v_a_797_);
v___x_808_ = v___x_804_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_797_);
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
v___x_812_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_811_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
v___y_796_ = v___x_812_;
goto v___jp_795_;
}
}
}
else
{
v___y_796_ = v___x_802_;
goto v___jp_795_;
}
}
else
{
lean_dec_ref(v___y_799_);
v___y_796_ = v___y_800_;
goto v___jp_795_;
}
}
v___jp_816_:
{
if (v___y_819_ == 0)
{
lean_object* v___x_820_; 
lean_dec_ref(v___y_817_);
v___x_820_ = l_Lean_Meta_SavedState_restore___redArg(v___y_818_, v___y_779_, v___y_781_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_832_; 
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_832_ == 0)
{
lean_object* v_unused_833_; 
v_unused_833_ = lean_ctor_get(v___x_820_, 0);
lean_dec(v_unused_833_);
v___x_822_ = v___x_820_;
v_isShared_823_ = v_isSharedCheck_832_;
goto v_resetjp_821_;
}
else
{
lean_dec(v___x_820_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_832_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; lean_object* v___x_826_; 
v___x_824_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1);
lean_inc(v_a_797_);
if (v_isShared_823_ == 0)
{
lean_ctor_set_tag(v___x_822_, 1);
lean_ctor_set(v___x_822_, 0, v_a_797_);
v___x_826_ = v___x_822_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_797_);
v___x_826_ = v_reuseFailAlloc_831_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_824_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_829_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
v___y_794_ = v___x_830_;
goto v___jp_793_;
}
}
}
else
{
v___y_794_ = v___x_820_;
goto v___jp_793_;
}
}
else
{
lean_dec_ref(v___y_818_);
v___y_794_ = v___y_817_;
goto v___jp_793_;
}
}
}
v___jp_783_:
{
size_t v___x_785_; size_t v___x_786_; 
v___x_785_ = ((size_t)1ULL);
v___x_786_ = lean_usize_add(v_i_776_, v___x_785_);
v_i_776_ = v___x_786_;
v_b_777_ = v_a_784_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_774_ = stack[0].m_obj;
size_t v_sz_775_ = stack[1].m_num;
size_t v_i_776_ = stack[2].m_num;
lean_object* v_b_777_ = stack[3].m_obj;
lean_object* v___y_778_ = stack[4].m_obj;
lean_object* v___y_779_ = stack[5].m_obj;
lean_object* v___y_780_ = stack[6].m_obj;
lean_object* v___y_781_ = stack[7].m_obj;
lean_object* v_res_950_;
v_res_950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v_as_774_, v_sz_775_, v_i_776_, v_b_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
stack->m_obj
 = v_res_950_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___boxed(lean_object* v_as_951_, lean_object* v_sz_952_, lean_object* v_i_953_, lean_object* v_b_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
size_t v_sz_boxed_960_; size_t v_i_boxed_961_; lean_object* v_res_962_; 
v_sz_boxed_960_ = lean_unbox_usize(v_sz_952_);
lean_dec(v_sz_952_);
v_i_boxed_961_ = lean_unbox_usize(v_i_953_);
lean_dec(v_i_953_);
v_res_962_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v_as_951_, v_sz_boxed_960_, v_i_boxed_961_, v_b_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec_ref(v_as_951_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
if (lean_obj_tag(v_a_963_) == 0)
{
lean_object* v___x_965_; 
v___x_965_ = l_List_reverse___redArg(v_a_964_);
return v___x_965_;
}
else
{
lean_object* v_head_966_; lean_object* v_tail_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_976_; 
v_head_966_ = lean_ctor_get(v_a_963_, 0);
v_tail_967_ = lean_ctor_get(v_a_963_, 1);
v_isSharedCheck_976_ = !lean_is_exclusive(v_a_963_);
if (v_isSharedCheck_976_ == 0)
{
v___x_969_ = v_a_963_;
v_isShared_970_ = v_isSharedCheck_976_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_tail_967_);
lean_inc(v_head_966_);
lean_dec(v_a_963_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_976_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_971_, 0, v_head_966_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 1, v_a_964_);
lean_ctor_set(v___x_969_, 0, v___x_971_);
v___x_973_ = v___x_969_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_a_964_);
v___x_973_ = v_reuseFailAlloc_975_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
v_a_963_ = v_tail_967_;
v_a_964_ = v___x_973_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__1(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__0));
v___x_979_ = l_Lean_stringToMessageData(v___x_978_);
return v___x_979_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__3(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__2));
v___x_982_ = l_Lean_stringToMessageData(v___x_981_);
return v___x_982_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__5(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__4));
v___x_985_ = l_Lean_stringToMessageData(v___x_984_);
return v___x_985_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__7(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__6));
v___x_988_ = l_Lean_stringToMessageData(v___x_987_);
return v___x_988_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__9(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__8));
v___x_991_ = l_Lean_stringToMessageData(v___x_990_);
return v___x_991_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__12(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__11));
v___x_996_ = l_Lean_stringToMessageData(v___x_995_);
return v___x_996_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__14(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__13));
v___x_999_ = l_Lean_stringToMessageData(v___x_998_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__16(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__15));
v___x_1002_ = l_Lean_stringToMessageData(v___x_1001_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__22(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__21));
v___x_1011_ = l_Lean_stringToMessageData(v___x_1010_);
return v___x_1011_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__24(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__23));
v___x_1014_ = l_Lean_stringToMessageData(v___x_1013_);
return v___x_1014_;
}
}
lean_object* l_Lean_Meta_rwMatcher___lam__2(uint8_t v___x_1015_, lean_object* v___x_1016_, lean_object* v_fst_1017_, lean_object* v___x_1018_, lean_object* v_e_1019_, uint8_t v___y_1020_, lean_object* v_snd_1021_, lean_object* v_____r_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___y_1029_; lean_object* v_proof_1030_; lean_object* v___y_1035_; lean_object* v___y_1036_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; uint8_t v___y_1055_; lean_object* v___x_1067_; uint8_t v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; uint8_t v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v_a_1091_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; uint8_t v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; size_t v_sz_1131_; size_t v___x_1132_; lean_object* v___x_1133_; uint8_t v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; uint8_t v_fst_1162_; lean_object* v_fst_1163_; lean_object* v_snd_1164_; lean_object* v___x_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; 
v___x_1067_ = l_Lean_mkAppN(v___x_1016_, v_fst_1017_);
v_sz_1131_ = lean_array_size(v_fst_1017_);
v___x_1132_ = ((size_t)0ULL);
v___x_1133_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_1131_, v___x_1132_, v_fst_1017_);
v___x_1198_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1199_ = lean_unsigned_to_nat(4u);
v___x_1200_ = l_Lean_Expr_isAppOfArity(v_snd_1021_, v___x_1198_, v___x_1199_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
v___x_1201_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1202_ = lean_unsigned_to_nat(3u);
v___x_1203_ = l_Lean_Expr_isAppOfArity(v_snd_1021_, v___x_1201_, v___x_1202_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec_ref(v___x_1133_);
lean_dec_ref(v___x_1067_);
lean_dec_ref(v_e_1019_);
v___x_1204_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1205_ = l_Lean_MessageData_ofConstName(v___x_1018_, v___y_1020_);
v___x_1206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1204_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
v___x_1207_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1206_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
v___x_1209_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1208_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1209_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1209_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
else
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1218_ = l_Lean_Expr_appFn_x21(v_snd_1021_);
v___x_1219_ = l_Lean_Expr_appArg_x21(v___x_1218_);
lean_dec_ref(v___x_1218_);
v___x_1220_ = l_Lean_Expr_appArg_x21(v_snd_1021_);
v_fst_1162_ = v___y_1020_;
v_fst_1163_ = v___x_1219_;
v_snd_1164_ = v___x_1220_;
goto v___jp_1161_;
}
}
else
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1221_ = l_Lean_Expr_appFn_x21(v_snd_1021_);
v___x_1222_ = l_Lean_Expr_appFn_x21(v___x_1221_);
lean_dec_ref(v___x_1221_);
v___x_1223_ = l_Lean_Expr_appArg_x21(v___x_1222_);
lean_dec_ref(v___x_1222_);
v___x_1224_ = l_Lean_Expr_appArg_x21(v_snd_1021_);
v_fst_1162_ = v___x_1015_;
v_fst_1163_ = v___x_1223_;
v_snd_1164_ = v___x_1224_;
goto v___jp_1161_;
}
v___jp_1028_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1031_, 0, v_proof_1030_);
v___x_1032_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1032_, 0, v___y_1029_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
lean_ctor_set_uint8(v___x_1032_, sizeof(void*)*2, v___x_1015_);
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
return v___x_1033_;
}
v___jp_1034_:
{
if (lean_obj_tag(v___y_1036_) == 0)
{
lean_object* v_a_1037_; 
v_a_1037_ = lean_ctor_get(v___y_1036_, 0);
lean_inc(v_a_1037_);
lean_dec_ref_known(v___y_1036_, 1);
v___y_1029_ = v___y_1035_;
v_proof_1030_ = v_a_1037_;
goto v___jp_1028_;
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec_ref(v___y_1035_);
v_a_1038_ = lean_ctor_get(v___y_1036_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___y_1036_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___y_1036_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___y_1036_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
v___jp_1046_:
{
if (v___y_1055_ == 0)
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
lean_dec_ref(v___y_1048_);
v___x_1056_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1057_ = l_Lean_MessageData_ofExpr(v___y_1047_);
v___x_1058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1056_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1058_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = l_Lean_Exception_toMessageData(v___y_1054_);
v___x_1062_ = l_Lean_indentD(v___x_1061_);
v___x_1063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1060_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1063_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1065_, v___y_1053_, v___y_1051_, v___y_1050_, v___y_1052_);
v___y_1035_ = v___y_1049_;
v___y_1036_ = v___x_1066_;
goto v___jp_1034_;
}
else
{
lean_dec_ref(v___y_1054_);
lean_dec_ref(v___y_1047_);
v___y_1035_ = v___y_1049_;
v___y_1036_ = v___y_1048_;
goto v___jp_1034_;
}
}
v___jp_1068_:
{
lean_object* v___x_1075_; lean_object* v_a_1076_; lean_object* v___x_1077_; 
v___x_1075_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_1070_, v___y_1072_);
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
lean_dec_ref(v___x_1075_);
v___x_1077_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___x_1067_, v___y_1072_);
if (v___y_1069_ == 0)
{
lean_object* v_a_1078_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1078_);
lean_dec_ref(v___x_1077_);
v___y_1029_ = v_a_1076_;
v_proof_1030_ = v_a_1078_;
goto v___jp_1028_;
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1080_; 
v_a_1079_ = lean_ctor_get(v___x_1077_, 0);
lean_inc_n(v_a_1079_, 2);
lean_dec_ref(v___x_1077_);
v___x_1080_ = l_Lean_Meta_mkEqOfHEq(v_a_1079_, v___x_1015_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_dec(v_a_1079_);
v___y_1035_ = v_a_1076_;
v___y_1036_ = v___x_1080_;
goto v___jp_1034_;
}
else
{
lean_object* v_a_1081_; uint8_t v___x_1082_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
v___x_1082_ = l_Lean_Exception_isInterrupt(v_a_1081_);
if (v___x_1082_ == 0)
{
uint8_t v___x_1083_; 
lean_inc(v_a_1081_);
v___x_1083_ = l_Lean_Exception_isRuntime(v_a_1081_);
v___y_1047_ = v_a_1079_;
v___y_1048_ = v___x_1080_;
v___y_1049_ = v_a_1076_;
v___y_1050_ = v___y_1073_;
v___y_1051_ = v___y_1072_;
v___y_1052_ = v___y_1074_;
v___y_1053_ = v___y_1071_;
v___y_1054_ = v_a_1081_;
v___y_1055_ = v___x_1083_;
goto v___jp_1046_;
}
else
{
v___y_1047_ = v_a_1079_;
v___y_1048_ = v___x_1080_;
v___y_1049_ = v_a_1076_;
v___y_1050_ = v___y_1073_;
v___y_1051_ = v___y_1072_;
v___y_1052_ = v___y_1074_;
v___y_1053_ = v___y_1071_;
v___y_1054_ = v_a_1081_;
v___y_1055_ = v___x_1082_;
goto v___jp_1046_;
}
}
}
}
v___jp_1084_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; 
v___x_1092_ = lean_array_get_size(v_a_1091_);
v___x_1093_ = lean_unsigned_to_nat(0u);
v___x_1094_ = lean_nat_dec_eq(v___x_1092_, v___x_1093_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec_ref(v___y_1089_);
lean_dec_ref(v___x_1067_);
v___x_1095_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1096_ = l_Lean_MessageData_ofConstName(v___x_1018_, v___x_1094_);
v___x_1097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1095_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1097_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = lean_array_to_list(v_a_1091_);
v___x_1101_ = lean_box(0);
v___x_1102_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_1100_, v___x_1101_);
v___x_1103_ = l_Lean_MessageData_ofList(v___x_1102_);
v___x_1104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1099_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
v___x_1105_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1104_, v___y_1087_, v___y_1086_, v___y_1085_, v___y_1090_);
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1105_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1105_);
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
else
{
lean_dec_ref(v_a_1091_);
lean_dec(v___x_1018_);
v___y_1069_ = v___y_1088_;
v___y_1070_ = v___y_1089_;
v___y_1071_ = v___y_1087_;
v___y_1072_ = v___y_1086_;
v___y_1073_ = v___y_1085_;
v___y_1074_ = v___y_1090_;
goto v___jp_1068_;
}
}
v___jp_1114_:
{
if (lean_obj_tag(v___y_1121_) == 0)
{
lean_object* v_a_1122_; 
v_a_1122_ = lean_ctor_get(v___y_1121_, 0);
lean_inc(v_a_1122_);
lean_dec_ref_known(v___y_1121_, 1);
v___y_1085_ = v___y_1115_;
v___y_1086_ = v___y_1117_;
v___y_1087_ = v___y_1116_;
v___y_1088_ = v___y_1118_;
v___y_1089_ = v___y_1120_;
v___y_1090_ = v___y_1119_;
v_a_1091_ = v_a_1122_;
goto v___jp_1084_;
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_dec_ref(v___y_1120_);
lean_dec_ref(v___x_1067_);
lean_dec(v___x_1018_);
v_a_1123_ = lean_ctor_get(v___y_1121_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___y_1121_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___y_1121_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___y_1121_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
v___jp_1134_:
{
lean_object* v___x_1141_; size_t v_sz_1142_; lean_object* v___x_1143_; 
v___x_1141_ = lean_box(0);
v_sz_1142_ = lean_array_size(v___x_1133_);
v___x_1143_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1133_, v_sz_1142_, v___x_1132_, v___x_1141_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
lean_dec_ref_known(v___x_1143_, 1);
v___x_1144_ = lean_unsigned_to_nat(0u);
v___x_1145_ = lean_array_get_size(v___x_1133_);
v___x_1146_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1147_ = lean_nat_dec_lt(v___x_1144_, v___x_1145_);
if (v___x_1147_ == 0)
{
lean_dec_ref(v___x_1133_);
v___y_1085_ = v___y_1139_;
v___y_1086_ = v___y_1138_;
v___y_1087_ = v___y_1137_;
v___y_1088_ = v___y_1135_;
v___y_1089_ = v___y_1136_;
v___y_1090_ = v___y_1140_;
v_a_1091_ = v___x_1146_;
goto v___jp_1084_;
}
else
{
uint8_t v___x_1148_; 
v___x_1148_ = lean_nat_dec_le(v___x_1145_, v___x_1145_);
if (v___x_1148_ == 0)
{
if (v___x_1147_ == 0)
{
lean_dec_ref(v___x_1133_);
v___y_1085_ = v___y_1139_;
v___y_1086_ = v___y_1138_;
v___y_1087_ = v___y_1137_;
v___y_1088_ = v___y_1135_;
v___y_1089_ = v___y_1136_;
v___y_1090_ = v___y_1140_;
v_a_1091_ = v___x_1146_;
goto v___jp_1084_;
}
else
{
size_t v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = lean_usize_of_nat(v___x_1145_);
v___x_1150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1133_, v___x_1132_, v___x_1149_, v___x_1146_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
lean_dec_ref(v___x_1133_);
v___y_1115_ = v___y_1139_;
v___y_1116_ = v___y_1137_;
v___y_1117_ = v___y_1138_;
v___y_1118_ = v___y_1135_;
v___y_1119_ = v___y_1140_;
v___y_1120_ = v___y_1136_;
v___y_1121_ = v___x_1150_;
goto v___jp_1114_;
}
}
else
{
size_t v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = lean_usize_of_nat(v___x_1145_);
v___x_1152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1133_, v___x_1132_, v___x_1151_, v___x_1146_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
lean_dec_ref(v___x_1133_);
v___y_1115_ = v___y_1139_;
v___y_1116_ = v___y_1137_;
v___y_1117_ = v___y_1138_;
v___y_1118_ = v___y_1135_;
v___y_1119_ = v___y_1140_;
v___y_1120_ = v___y_1136_;
v___y_1121_ = v___x_1152_;
goto v___jp_1114_;
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec_ref(v___y_1136_);
lean_dec_ref(v___x_1133_);
lean_dec_ref(v___x_1067_);
lean_dec(v___x_1018_);
v_a_1153_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1143_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1143_);
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
v___jp_1161_:
{
lean_object* v___x_1165_; 
lean_inc_ref(v_fst_1163_);
lean_inc_ref(v_e_1019_);
v___x_1165_ = l_Lean_Meta_isExprDefEq(v_e_1019_, v_fst_1163_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; uint8_t v___x_1167_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v___x_1165_, 1);
v___x_1167_ = lean_unbox(v_a_1166_);
lean_dec(v_a_1166_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
lean_dec_ref(v_snd_1164_);
lean_dec_ref(v___x_1133_);
lean_dec_ref(v___x_1067_);
v___x_1168_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1169_ = l_Lean_MessageData_ofExpr(v_fst_1163_);
v___x_1170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1170_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_1173_ = l_Lean_MessageData_ofConstName(v___x_1018_, v___y_1020_);
v___x_1174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1172_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
v___x_1175_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1174_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = l_Lean_MessageData_ofExpr(v_e_1019_);
v___x_1178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1176_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_1180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1178_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1180_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1181_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1181_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
else
{
lean_dec_ref(v_fst_1163_);
lean_dec_ref(v_e_1019_);
v___y_1135_ = v_fst_1162_;
v___y_1136_ = v_snd_1164_;
v___y_1137_ = v___y_1023_;
v___y_1138_ = v___y_1024_;
v___y_1139_ = v___y_1025_;
v___y_1140_ = v___y_1026_;
goto v___jp_1134_;
}
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
lean_dec_ref(v_snd_1164_);
lean_dec_ref(v_fst_1163_);
lean_dec_ref(v___x_1133_);
lean_dec_ref(v___x_1067_);
lean_dec_ref(v_e_1019_);
lean_dec(v___x_1018_);
v_a_1190_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_1165_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1165_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1190_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_rwMatcher___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1015_ = stack[0].m_num;
lean_object* v___x_1016_ = stack[1].m_obj;
lean_object* v_fst_1017_ = stack[2].m_obj;
lean_object* v___x_1018_ = stack[3].m_obj;
lean_object* v_e_1019_ = stack[4].m_obj;
uint8_t v___y_1020_ = stack[5].m_num;
lean_object* v_snd_1021_ = stack[6].m_obj;
lean_object* v_____r_1022_ = stack[7].m_obj;
lean_object* v___y_1023_ = stack[8].m_obj;
lean_object* v___y_1024_ = stack[9].m_obj;
lean_object* v___y_1025_ = stack[10].m_obj;
lean_object* v___y_1026_ = stack[11].m_obj;
lean_object* v_res_1225_;
v_res_1225_ = l_Lean_Meta_rwMatcher___lam__2(v___x_1015_, v___x_1016_, v_fst_1017_, v___x_1018_, v_e_1019_, v___y_1020_, v_snd_1021_, v_____r_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
stack->m_obj
 = v_res_1225_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2___boxed(lean_object* v___x_1226_, lean_object* v___x_1227_, lean_object* v_fst_1228_, lean_object* v___x_1229_, lean_object* v_e_1230_, lean_object* v___y_1231_, lean_object* v_snd_1232_, lean_object* v_____r_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
uint8_t v___x_85355__boxed_1239_; uint8_t v___y_85359__boxed_1240_; lean_object* v_res_1241_; 
v___x_85355__boxed_1239_ = lean_unbox(v___x_1226_);
v___y_85359__boxed_1240_ = lean_unbox(v___y_1231_);
v_res_1241_ = l_Lean_Meta_rwMatcher___lam__2(v___x_85355__boxed_1239_, v___x_1227_, v_fst_1228_, v___x_1229_, v_e_1230_, v___y_85359__boxed_1240_, v_snd_1232_, v_____r_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec_ref(v_snd_1232_);
return v_res_1241_;
}
}
lean_object* l_Lean_Meta_rwMatcher___lam__3(uint8_t v___x_1242_, lean_object* v___x_1243_, lean_object* v_fst_1244_, lean_object* v___x_1245_, lean_object* v_e_1246_, uint8_t v___y_1247_, lean_object* v_snd_1248_, lean_object* v_____r_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v___y_1256_; lean_object* v_proof_1257_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; uint8_t v___y_1282_; lean_object* v___x_1294_; lean_object* v___y_1296_; uint8_t v___y_1297_; lean_object* v___y_1298_; lean_object* v___y_1299_; lean_object* v___y_1300_; lean_object* v___y_1301_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; uint8_t v___y_1317_; lean_object* v_a_1318_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; uint8_t v___y_1347_; lean_object* v___y_1348_; size_t v_sz_1358_; size_t v___x_1359_; lean_object* v___x_1360_; lean_object* v___y_1362_; uint8_t v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; uint8_t v_fst_1389_; lean_object* v_fst_1390_; lean_object* v_snd_1391_; lean_object* v___x_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; 
v___x_1294_ = l_Lean_mkAppN(v___x_1243_, v_fst_1244_);
v_sz_1358_ = lean_array_size(v_fst_1244_);
v___x_1359_ = ((size_t)0ULL);
v___x_1360_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_1358_, v___x_1359_, v_fst_1244_);
v___x_1425_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1426_ = lean_unsigned_to_nat(4u);
v___x_1427_ = l_Lean_Expr_isAppOfArity(v_snd_1248_, v___x_1425_, v___x_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1428_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1429_ = lean_unsigned_to_nat(3u);
v___x_1430_ = l_Lean_Expr_isAppOfArity(v_snd_1248_, v___x_1428_, v___x_1429_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec_ref(v___x_1360_);
lean_dec_ref(v___x_1294_);
lean_dec_ref(v_e_1246_);
v___x_1431_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1432_ = l_Lean_MessageData_ofConstName(v___x_1245_, v___y_1247_);
v___x_1433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1431_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
v___x_1434_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1433_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
v___x_1436_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1435_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
else
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1445_ = l_Lean_Expr_appFn_x21(v_snd_1248_);
v___x_1446_ = l_Lean_Expr_appArg_x21(v___x_1445_);
lean_dec_ref(v___x_1445_);
v___x_1447_ = l_Lean_Expr_appArg_x21(v_snd_1248_);
v_fst_1389_ = v___y_1247_;
v_fst_1390_ = v___x_1446_;
v_snd_1391_ = v___x_1447_;
goto v___jp_1388_;
}
}
else
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1448_ = l_Lean_Expr_appFn_x21(v_snd_1248_);
v___x_1449_ = l_Lean_Expr_appFn_x21(v___x_1448_);
lean_dec_ref(v___x_1448_);
v___x_1450_ = l_Lean_Expr_appArg_x21(v___x_1449_);
lean_dec_ref(v___x_1449_);
v___x_1451_ = l_Lean_Expr_appArg_x21(v_snd_1248_);
v_fst_1389_ = v___x_1242_;
v_fst_1390_ = v___x_1450_;
v_snd_1391_ = v___x_1451_;
goto v___jp_1388_;
}
v___jp_1255_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1258_, 0, v_proof_1257_);
v___x_1259_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1259_, 0, v___y_1256_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*2, v___x_1242_);
v___x_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
return v___x_1260_;
}
v___jp_1261_:
{
if (lean_obj_tag(v___y_1263_) == 0)
{
lean_object* v_a_1264_; 
v_a_1264_ = lean_ctor_get(v___y_1263_, 0);
lean_inc(v_a_1264_);
lean_dec_ref_known(v___y_1263_, 1);
v___y_1256_ = v___y_1262_;
v_proof_1257_ = v_a_1264_;
goto v___jp_1255_;
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec_ref(v___y_1262_);
v_a_1265_ = lean_ctor_get(v___y_1263_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___y_1263_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___y_1263_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___y_1263_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
v___jp_1273_:
{
if (v___y_1282_ == 0)
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
lean_dec_ref(v___y_1278_);
v___x_1283_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1284_ = l_Lean_MessageData_ofExpr(v___y_1275_);
v___x_1285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1283_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
v___x_1286_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1285_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = l_Lean_Exception_toMessageData(v___y_1280_);
v___x_1289_ = l_Lean_indentD(v___x_1288_);
v___x_1290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1287_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___x_1291_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1290_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
v___x_1293_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1292_, v___y_1279_, v___y_1281_, v___y_1277_, v___y_1274_);
v___y_1262_ = v___y_1276_;
v___y_1263_ = v___x_1293_;
goto v___jp_1261_;
}
else
{
lean_dec_ref(v___y_1280_);
lean_dec_ref(v___y_1275_);
v___y_1262_ = v___y_1276_;
v___y_1263_ = v___y_1278_;
goto v___jp_1261_;
}
}
v___jp_1295_:
{
lean_object* v___x_1302_; lean_object* v_a_1303_; lean_object* v___x_1304_; 
v___x_1302_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_1296_, v___y_1299_);
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_a_1303_);
lean_dec_ref(v___x_1302_);
v___x_1304_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___x_1294_, v___y_1299_);
if (v___y_1297_ == 0)
{
lean_object* v_a_1305_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1305_);
lean_dec_ref(v___x_1304_);
v___y_1256_ = v_a_1303_;
v_proof_1257_ = v_a_1305_;
goto v___jp_1255_;
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1307_; 
v_a_1306_ = lean_ctor_get(v___x_1304_, 0);
lean_inc_n(v_a_1306_, 2);
lean_dec_ref(v___x_1304_);
v___x_1307_ = l_Lean_Meta_mkEqOfHEq(v_a_1306_, v___x_1242_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_dec(v_a_1306_);
v___y_1262_ = v_a_1303_;
v___y_1263_ = v___x_1307_;
goto v___jp_1261_;
}
else
{
lean_object* v_a_1308_; uint8_t v___x_1309_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_a_1308_);
v___x_1309_ = l_Lean_Exception_isInterrupt(v_a_1308_);
if (v___x_1309_ == 0)
{
uint8_t v___x_1310_; 
lean_inc(v_a_1308_);
v___x_1310_ = l_Lean_Exception_isRuntime(v_a_1308_);
v___y_1274_ = v___y_1301_;
v___y_1275_ = v_a_1306_;
v___y_1276_ = v_a_1303_;
v___y_1277_ = v___y_1300_;
v___y_1278_ = v___x_1307_;
v___y_1279_ = v___y_1298_;
v___y_1280_ = v_a_1308_;
v___y_1281_ = v___y_1299_;
v___y_1282_ = v___x_1310_;
goto v___jp_1273_;
}
else
{
v___y_1274_ = v___y_1301_;
v___y_1275_ = v_a_1306_;
v___y_1276_ = v_a_1303_;
v___y_1277_ = v___y_1300_;
v___y_1278_ = v___x_1307_;
v___y_1279_ = v___y_1298_;
v___y_1280_ = v_a_1308_;
v___y_1281_ = v___y_1299_;
v___y_1282_ = v___x_1309_;
goto v___jp_1273_;
}
}
}
}
v___jp_1311_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1319_ = lean_array_get_size(v_a_1318_);
v___x_1320_ = lean_unsigned_to_nat(0u);
v___x_1321_ = lean_nat_dec_eq(v___x_1319_, v___x_1320_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec_ref(v___y_1313_);
lean_dec_ref(v___x_1294_);
v___x_1322_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1323_ = l_Lean_MessageData_ofConstName(v___x_1245_, v___x_1321_);
v___x_1324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1322_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
v___x_1325_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1324_);
lean_ctor_set(v___x_1326_, 1, v___x_1325_);
v___x_1327_ = lean_array_to_list(v_a_1318_);
v___x_1328_ = lean_box(0);
v___x_1329_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_1327_, v___x_1328_);
v___x_1330_ = l_Lean_MessageData_ofList(v___x_1329_);
v___x_1331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1326_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
v___x_1332_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1331_, v___y_1316_, v___y_1315_, v___y_1314_, v___y_1312_);
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1332_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
else
{
lean_dec_ref(v_a_1318_);
lean_dec(v___x_1245_);
v___y_1296_ = v___y_1313_;
v___y_1297_ = v___y_1317_;
v___y_1298_ = v___y_1316_;
v___y_1299_ = v___y_1315_;
v___y_1300_ = v___y_1314_;
v___y_1301_ = v___y_1312_;
goto v___jp_1295_;
}
}
v___jp_1341_:
{
if (lean_obj_tag(v___y_1348_) == 0)
{
lean_object* v_a_1349_; 
v_a_1349_ = lean_ctor_get(v___y_1348_, 0);
lean_inc(v_a_1349_);
lean_dec_ref_known(v___y_1348_, 1);
v___y_1312_ = v___y_1342_;
v___y_1313_ = v___y_1345_;
v___y_1314_ = v___y_1344_;
v___y_1315_ = v___y_1343_;
v___y_1316_ = v___y_1346_;
v___y_1317_ = v___y_1347_;
v_a_1318_ = v_a_1349_;
goto v___jp_1311_;
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_dec_ref(v___y_1345_);
lean_dec_ref(v___x_1294_);
lean_dec(v___x_1245_);
v_a_1350_ = lean_ctor_get(v___y_1348_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___y_1348_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___y_1348_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___y_1348_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
v___jp_1361_:
{
lean_object* v___x_1368_; size_t v_sz_1369_; lean_object* v___x_1370_; 
v___x_1368_ = lean_box(0);
v_sz_1369_ = lean_array_size(v___x_1360_);
v___x_1370_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1360_, v_sz_1369_, v___x_1359_, v___x_1368_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
lean_dec_ref_known(v___x_1370_, 1);
v___x_1371_ = lean_unsigned_to_nat(0u);
v___x_1372_ = lean_array_get_size(v___x_1360_);
v___x_1373_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1374_ = lean_nat_dec_lt(v___x_1371_, v___x_1372_);
if (v___x_1374_ == 0)
{
lean_dec_ref(v___x_1360_);
v___y_1312_ = v___y_1367_;
v___y_1313_ = v___y_1362_;
v___y_1314_ = v___y_1366_;
v___y_1315_ = v___y_1365_;
v___y_1316_ = v___y_1364_;
v___y_1317_ = v___y_1363_;
v_a_1318_ = v___x_1373_;
goto v___jp_1311_;
}
else
{
uint8_t v___x_1375_; 
v___x_1375_ = lean_nat_dec_le(v___x_1372_, v___x_1372_);
if (v___x_1375_ == 0)
{
if (v___x_1374_ == 0)
{
lean_dec_ref(v___x_1360_);
v___y_1312_ = v___y_1367_;
v___y_1313_ = v___y_1362_;
v___y_1314_ = v___y_1366_;
v___y_1315_ = v___y_1365_;
v___y_1316_ = v___y_1364_;
v___y_1317_ = v___y_1363_;
v_a_1318_ = v___x_1373_;
goto v___jp_1311_;
}
else
{
size_t v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = lean_usize_of_nat(v___x_1372_);
v___x_1377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1360_, v___x_1359_, v___x_1376_, v___x_1373_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
lean_dec_ref(v___x_1360_);
v___y_1342_ = v___y_1367_;
v___y_1343_ = v___y_1365_;
v___y_1344_ = v___y_1366_;
v___y_1345_ = v___y_1362_;
v___y_1346_ = v___y_1364_;
v___y_1347_ = v___y_1363_;
v___y_1348_ = v___x_1377_;
goto v___jp_1341_;
}
}
else
{
size_t v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = lean_usize_of_nat(v___x_1372_);
v___x_1379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1360_, v___x_1359_, v___x_1378_, v___x_1373_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
lean_dec_ref(v___x_1360_);
v___y_1342_ = v___y_1367_;
v___y_1343_ = v___y_1365_;
v___y_1344_ = v___y_1366_;
v___y_1345_ = v___y_1362_;
v___y_1346_ = v___y_1364_;
v___y_1347_ = v___y_1363_;
v___y_1348_ = v___x_1379_;
goto v___jp_1341_;
}
}
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_dec_ref(v___y_1362_);
lean_dec_ref(v___x_1360_);
lean_dec_ref(v___x_1294_);
lean_dec(v___x_1245_);
v_a_1380_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1370_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1370_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
v___jp_1388_:
{
lean_object* v___x_1392_; 
lean_inc_ref(v_fst_1390_);
lean_inc_ref(v_e_1246_);
v___x_1392_ = l_Lean_Meta_isExprDefEq(v_e_1246_, v_fst_1390_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; uint8_t v___x_1394_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_a_1393_);
lean_dec_ref_known(v___x_1392_, 1);
v___x_1394_ = lean_unbox(v_a_1393_);
lean_dec(v_a_1393_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
lean_dec_ref(v_snd_1391_);
lean_dec_ref(v___x_1360_);
lean_dec_ref(v___x_1294_);
v___x_1395_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1396_ = l_Lean_MessageData_ofExpr(v_fst_1390_);
v___x_1397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1395_);
lean_ctor_set(v___x_1397_, 1, v___x_1396_);
v___x_1398_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1397_);
lean_ctor_set(v___x_1399_, 1, v___x_1398_);
v___x_1400_ = l_Lean_MessageData_ofConstName(v___x_1245_, v___y_1247_);
v___x_1401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1399_);
lean_ctor_set(v___x_1401_, 1, v___x_1400_);
v___x_1402_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1401_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
v___x_1404_ = l_Lean_MessageData_ofExpr(v_e_1246_);
v___x_1405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1403_);
lean_ctor_set(v___x_1405_, 1, v___x_1404_);
v___x_1406_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_1407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1405_);
lean_ctor_set(v___x_1407_, 1, v___x_1406_);
v___x_1408_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1407_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1408_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1408_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
else
{
lean_dec_ref(v_fst_1390_);
lean_dec_ref(v_e_1246_);
v___y_1362_ = v_snd_1391_;
v___y_1363_ = v_fst_1389_;
v___y_1364_ = v___y_1250_;
v___y_1365_ = v___y_1251_;
v___y_1366_ = v___y_1252_;
v___y_1367_ = v___y_1253_;
goto v___jp_1361_;
}
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_dec_ref(v_snd_1391_);
lean_dec_ref(v_fst_1390_);
lean_dec_ref(v___x_1360_);
lean_dec_ref(v___x_1294_);
lean_dec_ref(v_e_1246_);
lean_dec(v___x_1245_);
v_a_1417_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1392_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1392_);
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
}
}
}
LEAN_EXPORT void l_Lean_Meta_rwMatcher___lam__3_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1242_ = stack[0].m_num;
lean_object* v___x_1243_ = stack[1].m_obj;
lean_object* v_fst_1244_ = stack[2].m_obj;
lean_object* v___x_1245_ = stack[3].m_obj;
lean_object* v_e_1246_ = stack[4].m_obj;
uint8_t v___y_1247_ = stack[5].m_num;
lean_object* v_snd_1248_ = stack[6].m_obj;
lean_object* v_____r_1249_ = stack[7].m_obj;
lean_object* v___y_1250_ = stack[8].m_obj;
lean_object* v___y_1251_ = stack[9].m_obj;
lean_object* v___y_1252_ = stack[10].m_obj;
lean_object* v___y_1253_ = stack[11].m_obj;
lean_object* v_res_1452_;
v_res_1452_ = l_Lean_Meta_rwMatcher___lam__3(v___x_1242_, v___x_1243_, v_fst_1244_, v___x_1245_, v_e_1246_, v___y_1247_, v_snd_1248_, v_____r_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
stack->m_obj
 = v_res_1452_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3___boxed(lean_object* v___x_1453_, lean_object* v___x_1454_, lean_object* v_fst_1455_, lean_object* v___x_1456_, lean_object* v_e_1457_, lean_object* v___y_1458_, lean_object* v_snd_1459_, lean_object* v_____r_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
uint8_t v___x_86121__boxed_1466_; uint8_t v___y_86125__boxed_1467_; lean_object* v_res_1468_; 
v___x_86121__boxed_1466_ = lean_unbox(v___x_1453_);
v___y_86125__boxed_1467_ = lean_unbox(v___y_1458_);
v_res_1468_ = l_Lean_Meta_rwMatcher___lam__3(v___x_86121__boxed_1466_, v___x_1454_, v_fst_1455_, v___x_1456_, v_e_1457_, v___y_86125__boxed_1467_, v_snd_1459_, v_____r_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec_ref(v_snd_1459_);
return v_res_1468_;
}
}
lean_object* l_Lean_Meta_rwMatcher___lam__4(uint8_t v___x_1469_, lean_object* v___x_1470_, lean_object* v_fst_1471_, lean_object* v___x_1472_, lean_object* v_e_1473_, uint8_t v___y_1474_, lean_object* v_snd_1475_, lean_object* v_____r_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v___y_1483_; lean_object* v_proof_1484_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; uint8_t v___y_1509_; lean_object* v___x_1521_; lean_object* v___y_1523_; uint8_t v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; uint8_t v___y_1544_; lean_object* v_a_1545_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; uint8_t v___y_1574_; lean_object* v___y_1575_; size_t v_sz_1585_; size_t v___x_1586_; lean_object* v___x_1587_; lean_object* v___y_1589_; uint8_t v___y_1590_; lean_object* v___y_1591_; lean_object* v___y_1592_; lean_object* v___y_1593_; lean_object* v___y_1594_; uint8_t v_fst_1616_; lean_object* v_fst_1617_; lean_object* v_snd_1618_; lean_object* v___x_1652_; lean_object* v___x_1653_; uint8_t v___x_1654_; 
v___x_1521_ = l_Lean_mkAppN(v___x_1470_, v_fst_1471_);
v_sz_1585_ = lean_array_size(v_fst_1471_);
v___x_1586_ = ((size_t)0ULL);
v___x_1587_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_1585_, v___x_1586_, v_fst_1471_);
v___x_1652_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1653_ = lean_unsigned_to_nat(4u);
v___x_1654_ = l_Lean_Expr_isAppOfArity(v_snd_1475_, v___x_1652_, v___x_1653_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1655_; lean_object* v___x_1656_; uint8_t v___x_1657_; 
v___x_1655_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1656_ = lean_unsigned_to_nat(3u);
v___x_1657_ = l_Lean_Expr_isAppOfArity(v_snd_1475_, v___x_1655_, v___x_1656_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
lean_dec_ref(v___x_1587_);
lean_dec_ref(v___x_1521_);
lean_dec_ref(v_e_1473_);
v___x_1658_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1659_ = l_Lean_MessageData_ofConstName(v___x_1472_, v___y_1474_);
v___x_1660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1658_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
v___x_1661_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1660_);
lean_ctor_set(v___x_1662_, 1, v___x_1661_);
v___x_1663_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1662_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1663_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1663_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
else
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1672_ = l_Lean_Expr_appFn_x21(v_snd_1475_);
v___x_1673_ = l_Lean_Expr_appArg_x21(v___x_1672_);
lean_dec_ref(v___x_1672_);
v___x_1674_ = l_Lean_Expr_appArg_x21(v_snd_1475_);
v_fst_1616_ = v___y_1474_;
v_fst_1617_ = v___x_1673_;
v_snd_1618_ = v___x_1674_;
goto v___jp_1615_;
}
}
else
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1675_ = l_Lean_Expr_appFn_x21(v_snd_1475_);
v___x_1676_ = l_Lean_Expr_appFn_x21(v___x_1675_);
lean_dec_ref(v___x_1675_);
v___x_1677_ = l_Lean_Expr_appArg_x21(v___x_1676_);
lean_dec_ref(v___x_1676_);
v___x_1678_ = l_Lean_Expr_appArg_x21(v_snd_1475_);
v_fst_1616_ = v___x_1469_;
v_fst_1617_ = v___x_1677_;
v_snd_1618_ = v___x_1678_;
goto v___jp_1615_;
}
v___jp_1482_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1485_, 0, v_proof_1484_);
v___x_1486_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1486_, 0, v___y_1483_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
lean_ctor_set_uint8(v___x_1486_, sizeof(void*)*2, v___x_1469_);
v___x_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
return v___x_1487_;
}
v___jp_1488_:
{
if (lean_obj_tag(v___y_1490_) == 0)
{
lean_object* v_a_1491_; 
v_a_1491_ = lean_ctor_get(v___y_1490_, 0);
lean_inc(v_a_1491_);
lean_dec_ref_known(v___y_1490_, 1);
v___y_1483_ = v___y_1489_;
v_proof_1484_ = v_a_1491_;
goto v___jp_1482_;
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec_ref(v___y_1489_);
v_a_1492_ = lean_ctor_get(v___y_1490_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___y_1490_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___y_1490_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___y_1490_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
v___jp_1500_:
{
if (v___y_1509_ == 0)
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
lean_dec_ref(v___y_1504_);
v___x_1510_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1511_ = l_Lean_MessageData_ofExpr(v___y_1506_);
v___x_1512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1510_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
v___x_1513_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1512_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
v___x_1515_ = l_Lean_Exception_toMessageData(v___y_1505_);
v___x_1516_ = l_Lean_indentD(v___x_1515_);
v___x_1517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1514_);
lean_ctor_set(v___x_1517_, 1, v___x_1516_);
v___x_1518_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1517_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
v___x_1520_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1519_, v___y_1502_, v___y_1507_, v___y_1503_, v___y_1501_);
v___y_1489_ = v___y_1508_;
v___y_1490_ = v___x_1520_;
goto v___jp_1488_;
}
else
{
lean_dec_ref(v___y_1506_);
lean_dec_ref(v___y_1505_);
v___y_1489_ = v___y_1508_;
v___y_1490_ = v___y_1504_;
goto v___jp_1488_;
}
}
v___jp_1522_:
{
lean_object* v___x_1529_; lean_object* v_a_1530_; lean_object* v___x_1531_; 
v___x_1529_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_1523_, v___y_1526_);
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref(v___x_1529_);
v___x_1531_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___x_1521_, v___y_1526_);
if (v___y_1524_ == 0)
{
lean_object* v_a_1532_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref(v___x_1531_);
v___y_1483_ = v_a_1530_;
v_proof_1484_ = v_a_1532_;
goto v___jp_1482_;
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1534_; 
v_a_1533_ = lean_ctor_get(v___x_1531_, 0);
lean_inc_n(v_a_1533_, 2);
lean_dec_ref(v___x_1531_);
v___x_1534_ = l_Lean_Meta_mkEqOfHEq(v_a_1533_, v___x_1469_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_dec(v_a_1533_);
v___y_1489_ = v_a_1530_;
v___y_1490_ = v___x_1534_;
goto v___jp_1488_;
}
else
{
lean_object* v_a_1535_; uint8_t v___x_1536_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
v___x_1536_ = l_Lean_Exception_isInterrupt(v_a_1535_);
if (v___x_1536_ == 0)
{
uint8_t v___x_1537_; 
lean_inc(v_a_1535_);
v___x_1537_ = l_Lean_Exception_isRuntime(v_a_1535_);
v___y_1501_ = v___y_1528_;
v___y_1502_ = v___y_1525_;
v___y_1503_ = v___y_1527_;
v___y_1504_ = v___x_1534_;
v___y_1505_ = v_a_1535_;
v___y_1506_ = v_a_1533_;
v___y_1507_ = v___y_1526_;
v___y_1508_ = v_a_1530_;
v___y_1509_ = v___x_1537_;
goto v___jp_1500_;
}
else
{
v___y_1501_ = v___y_1528_;
v___y_1502_ = v___y_1525_;
v___y_1503_ = v___y_1527_;
v___y_1504_ = v___x_1534_;
v___y_1505_ = v_a_1535_;
v___y_1506_ = v_a_1533_;
v___y_1507_ = v___y_1526_;
v___y_1508_ = v_a_1530_;
v___y_1509_ = v___x_1536_;
goto v___jp_1500_;
}
}
}
}
v___jp_1538_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v___x_1546_ = lean_array_get_size(v_a_1545_);
v___x_1547_ = lean_unsigned_to_nat(0u);
v___x_1548_ = lean_nat_dec_eq(v___x_1546_, v___x_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_dec_ref(v___y_1539_);
lean_dec_ref(v___x_1521_);
v___x_1549_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1550_ = l_Lean_MessageData_ofConstName(v___x_1472_, v___x_1548_);
v___x_1551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1549_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = lean_array_to_list(v_a_1545_);
v___x_1555_ = lean_box(0);
v___x_1556_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_1554_, v___x_1555_);
v___x_1557_ = l_Lean_MessageData_ofList(v___x_1556_);
v___x_1558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1553_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1558_, v___y_1542_, v___y_1541_, v___y_1543_, v___y_1540_);
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1559_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1559_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
else
{
lean_dec_ref(v_a_1545_);
lean_dec(v___x_1472_);
v___y_1523_ = v___y_1539_;
v___y_1524_ = v___y_1544_;
v___y_1525_ = v___y_1542_;
v___y_1526_ = v___y_1541_;
v___y_1527_ = v___y_1543_;
v___y_1528_ = v___y_1540_;
goto v___jp_1522_;
}
}
v___jp_1568_:
{
if (lean_obj_tag(v___y_1575_) == 0)
{
lean_object* v_a_1576_; 
v_a_1576_ = lean_ctor_get(v___y_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v___y_1575_, 1);
v___y_1539_ = v___y_1569_;
v___y_1540_ = v___y_1571_;
v___y_1541_ = v___y_1570_;
v___y_1542_ = v___y_1572_;
v___y_1543_ = v___y_1573_;
v___y_1544_ = v___y_1574_;
v_a_1545_ = v_a_1576_;
goto v___jp_1538_;
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec_ref(v___y_1569_);
lean_dec_ref(v___x_1521_);
lean_dec(v___x_1472_);
v_a_1577_ = lean_ctor_get(v___y_1575_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___y_1575_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___y_1575_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___y_1575_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
v___jp_1588_:
{
lean_object* v___x_1595_; size_t v_sz_1596_; lean_object* v___x_1597_; 
v___x_1595_ = lean_box(0);
v_sz_1596_ = lean_array_size(v___x_1587_);
v___x_1597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1587_, v_sz_1596_, v___x_1586_, v___x_1595_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; uint8_t v___x_1601_; 
lean_dec_ref_known(v___x_1597_, 1);
v___x_1598_ = lean_unsigned_to_nat(0u);
v___x_1599_ = lean_array_get_size(v___x_1587_);
v___x_1600_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1601_ = lean_nat_dec_lt(v___x_1598_, v___x_1599_);
if (v___x_1601_ == 0)
{
lean_dec_ref(v___x_1587_);
v___y_1539_ = v___y_1589_;
v___y_1540_ = v___y_1594_;
v___y_1541_ = v___y_1592_;
v___y_1542_ = v___y_1591_;
v___y_1543_ = v___y_1593_;
v___y_1544_ = v___y_1590_;
v_a_1545_ = v___x_1600_;
goto v___jp_1538_;
}
else
{
uint8_t v___x_1602_; 
v___x_1602_ = lean_nat_dec_le(v___x_1599_, v___x_1599_);
if (v___x_1602_ == 0)
{
if (v___x_1601_ == 0)
{
lean_dec_ref(v___x_1587_);
v___y_1539_ = v___y_1589_;
v___y_1540_ = v___y_1594_;
v___y_1541_ = v___y_1592_;
v___y_1542_ = v___y_1591_;
v___y_1543_ = v___y_1593_;
v___y_1544_ = v___y_1590_;
v_a_1545_ = v___x_1600_;
goto v___jp_1538_;
}
else
{
size_t v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = lean_usize_of_nat(v___x_1599_);
v___x_1604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1587_, v___x_1586_, v___x_1603_, v___x_1600_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
lean_dec_ref(v___x_1587_);
v___y_1569_ = v___y_1589_;
v___y_1570_ = v___y_1592_;
v___y_1571_ = v___y_1594_;
v___y_1572_ = v___y_1591_;
v___y_1573_ = v___y_1593_;
v___y_1574_ = v___y_1590_;
v___y_1575_ = v___x_1604_;
goto v___jp_1568_;
}
}
else
{
size_t v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = lean_usize_of_nat(v___x_1599_);
v___x_1606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1587_, v___x_1586_, v___x_1605_, v___x_1600_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
lean_dec_ref(v___x_1587_);
v___y_1569_ = v___y_1589_;
v___y_1570_ = v___y_1592_;
v___y_1571_ = v___y_1594_;
v___y_1572_ = v___y_1591_;
v___y_1573_ = v___y_1593_;
v___y_1574_ = v___y_1590_;
v___y_1575_ = v___x_1606_;
goto v___jp_1568_;
}
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec_ref(v___y_1589_);
lean_dec_ref(v___x_1587_);
lean_dec_ref(v___x_1521_);
lean_dec(v___x_1472_);
v_a_1607_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1597_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1597_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
v___jp_1615_:
{
lean_object* v___x_1619_; 
lean_inc_ref(v_fst_1617_);
lean_inc_ref(v_e_1473_);
v___x_1619_ = l_Lean_Meta_isExprDefEq(v_e_1473_, v_fst_1617_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; uint8_t v___x_1621_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1619_, 1);
v___x_1621_ = lean_unbox(v_a_1620_);
lean_dec(v_a_1620_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec_ref(v_snd_1618_);
lean_dec_ref(v___x_1587_);
lean_dec_ref(v___x_1521_);
v___x_1622_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1623_ = l_Lean_MessageData_ofExpr(v_fst_1617_);
v___x_1624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1622_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1624_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
v___x_1627_ = l_Lean_MessageData_ofConstName(v___x_1472_, v___y_1474_);
v___x_1628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1626_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
v___x_1629_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1628_);
lean_ctor_set(v___x_1630_, 1, v___x_1629_);
v___x_1631_ = l_Lean_MessageData_ofExpr(v_e_1473_);
v___x_1632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1630_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_1634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1632_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1634_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1635_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1635_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
else
{
lean_dec_ref(v_fst_1617_);
lean_dec_ref(v_e_1473_);
v___y_1589_ = v_snd_1618_;
v___y_1590_ = v_fst_1616_;
v___y_1591_ = v___y_1477_;
v___y_1592_ = v___y_1478_;
v___y_1593_ = v___y_1479_;
v___y_1594_ = v___y_1480_;
goto v___jp_1588_;
}
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
lean_dec_ref(v_snd_1618_);
lean_dec_ref(v_fst_1617_);
lean_dec_ref(v___x_1587_);
lean_dec_ref(v___x_1521_);
lean_dec_ref(v_e_1473_);
lean_dec(v___x_1472_);
v_a_1644_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1619_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1619_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_rwMatcher___lam__4_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1469_ = stack[0].m_num;
lean_object* v___x_1470_ = stack[1].m_obj;
lean_object* v_fst_1471_ = stack[2].m_obj;
lean_object* v___x_1472_ = stack[3].m_obj;
lean_object* v_e_1473_ = stack[4].m_obj;
uint8_t v___y_1474_ = stack[5].m_num;
lean_object* v_snd_1475_ = stack[6].m_obj;
lean_object* v_____r_1476_ = stack[7].m_obj;
lean_object* v___y_1477_ = stack[8].m_obj;
lean_object* v___y_1478_ = stack[9].m_obj;
lean_object* v___y_1479_ = stack[10].m_obj;
lean_object* v___y_1480_ = stack[11].m_obj;
lean_object* v_res_1679_;
v_res_1679_ = l_Lean_Meta_rwMatcher___lam__4(v___x_1469_, v___x_1470_, v_fst_1471_, v___x_1472_, v_e_1473_, v___y_1474_, v_snd_1475_, v_____r_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
stack->m_obj
 = v_res_1679_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4___boxed(lean_object* v___x_1680_, lean_object* v___x_1681_, lean_object* v_fst_1682_, lean_object* v___x_1683_, lean_object* v_e_1684_, lean_object* v___y_1685_, lean_object* v_snd_1686_, lean_object* v_____r_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
uint8_t v___x_86824__boxed_1693_; uint8_t v___y_86828__boxed_1694_; lean_object* v_res_1695_; 
v___x_86824__boxed_1693_ = lean_unbox(v___x_1680_);
v___y_86828__boxed_1694_ = lean_unbox(v___y_1685_);
v_res_1695_ = l_Lean_Meta_rwMatcher___lam__4(v___x_86824__boxed_1693_, v___x_1681_, v_fst_1682_, v___x_1683_, v_e_1684_, v___y_86828__boxed_1694_, v_snd_1686_, v_____r_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec_ref(v_snd_1686_);
return v_res_1695_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1696_; double v___x_1697_; 
v___x_1696_ = lean_unsigned_to_nat(0u);
v___x_1697_ = lean_float_of_nat(v___x_1696_);
return v___x_1697_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(lean_object* v_cls_1701_, lean_object* v_msg_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_ref_1708_; lean_object* v___x_1709_; lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1755_; 
v_ref_1708_ = lean_ctor_get(v___y_1705_, 2);
v___x_1709_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1712_ = v___x_1709_;
v_isShared_1713_ = v_isSharedCheck_1755_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1709_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1755_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1714_; lean_object* v_traceState_1715_; lean_object* v_env_1716_; lean_object* v_nextMacroScope_1717_; lean_object* v_ngen_1718_; lean_object* v_auxDeclNGen_1719_; lean_object* v_cache_1720_; lean_object* v_recordedDeps_1721_; lean_object* v_messages_1722_; lean_object* v_infoState_1723_; lean_object* v_snapshotTasks_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1754_; 
v___x_1714_ = lean_st_ref_take(v___y_1706_);
v_traceState_1715_ = lean_ctor_get(v___x_1714_, 4);
v_env_1716_ = lean_ctor_get(v___x_1714_, 0);
v_nextMacroScope_1717_ = lean_ctor_get(v___x_1714_, 1);
v_ngen_1718_ = lean_ctor_get(v___x_1714_, 2);
v_auxDeclNGen_1719_ = lean_ctor_get(v___x_1714_, 3);
v_cache_1720_ = lean_ctor_get(v___x_1714_, 5);
v_recordedDeps_1721_ = lean_ctor_get(v___x_1714_, 6);
v_messages_1722_ = lean_ctor_get(v___x_1714_, 7);
v_infoState_1723_ = lean_ctor_get(v___x_1714_, 8);
v_snapshotTasks_1724_ = lean_ctor_get(v___x_1714_, 9);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1726_ = v___x_1714_;
v_isShared_1727_ = v_isSharedCheck_1754_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_snapshotTasks_1724_);
lean_inc(v_infoState_1723_);
lean_inc(v_messages_1722_);
lean_inc(v_recordedDeps_1721_);
lean_inc(v_cache_1720_);
lean_inc(v_traceState_1715_);
lean_inc(v_auxDeclNGen_1719_);
lean_inc(v_ngen_1718_);
lean_inc(v_nextMacroScope_1717_);
lean_inc(v_env_1716_);
lean_dec(v___x_1714_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1754_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
uint64_t v_tid_1728_; lean_object* v_traces_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1753_; 
v_tid_1728_ = lean_ctor_get_uint64(v_traceState_1715_, sizeof(void*)*1);
v_traces_1729_ = lean_ctor_get(v_traceState_1715_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v_traceState_1715_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1731_ = v_traceState_1715_;
v_isShared_1732_ = v_isSharedCheck_1753_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_traces_1729_);
lean_dec(v_traceState_1715_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1753_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; double v___x_1735_; uint8_t v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1744_; 
v___x_1733_ = lean_box(0);
v___x_1734_ = lean_box(0);
v___x_1735_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0);
v___x_1736_ = 0;
v___x_1737_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1));
v___x_1738_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1738_, 0, v_cls_1701_);
lean_ctor_set(v___x_1738_, 1, v___x_1734_);
lean_ctor_set(v___x_1738_, 2, v___x_1737_);
lean_ctor_set_float(v___x_1738_, sizeof(void*)*3, v___x_1735_);
lean_ctor_set_float(v___x_1738_, sizeof(void*)*3 + 8, v___x_1735_);
lean_ctor_set_uint8(v___x_1738_, sizeof(void*)*3 + 16, v___x_1736_);
v___x_1739_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__2));
v___x_1740_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1738_);
lean_ctor_set(v___x_1740_, 1, v_a_1710_);
lean_ctor_set(v___x_1740_, 2, v___x_1739_);
lean_inc(v_ref_1708_);
v___x_1741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1741_, 0, v_ref_1708_);
lean_ctor_set(v___x_1741_, 1, v___x_1740_);
v___x_1742_ = l_Lean_PersistentArray_push___redArg(v_traces_1729_, v___x_1741_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v___x_1742_);
v___x_1744_ = v___x_1731_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1742_);
lean_ctor_set_uint64(v_reuseFailAlloc_1752_, sizeof(void*)*1, v_tid_1728_);
v___x_1744_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
lean_object* v___x_1746_; 
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 4, v___x_1744_);
v___x_1746_ = v___x_1726_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_env_1716_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v_nextMacroScope_1717_);
lean_ctor_set(v_reuseFailAlloc_1751_, 2, v_ngen_1718_);
lean_ctor_set(v_reuseFailAlloc_1751_, 3, v_auxDeclNGen_1719_);
lean_ctor_set(v_reuseFailAlloc_1751_, 4, v___x_1744_);
lean_ctor_set(v_reuseFailAlloc_1751_, 5, v_cache_1720_);
lean_ctor_set(v_reuseFailAlloc_1751_, 6, v_recordedDeps_1721_);
lean_ctor_set(v_reuseFailAlloc_1751_, 7, v_messages_1722_);
lean_ctor_set(v_reuseFailAlloc_1751_, 8, v_infoState_1723_);
lean_ctor_set(v_reuseFailAlloc_1751_, 9, v_snapshotTasks_1724_);
v___x_1746_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
lean_object* v___x_1747_; lean_object* v___x_1749_; 
v___x_1747_ = lean_st_ref_put(v___y_1706_, v___x_1746_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 0, v___x_1733_);
v___x_1749_ = v___x_1712_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1733_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1701_ = stack[0].m_obj;
lean_object* v_msg_1702_ = stack[1].m_obj;
lean_object* v___y_1703_ = stack[2].m_obj;
lean_object* v___y_1704_ = stack[3].m_obj;
lean_object* v___y_1705_ = stack[4].m_obj;
lean_object* v___y_1706_ = stack[5].m_obj;
lean_object* v_res_1756_;
v_res_1756_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v_cls_1701_, v_msg_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
stack->m_obj
 = v_res_1756_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___boxed(lean_object* v_cls_1757_, lean_object* v_msg_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v_cls_1757_, v_msg_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
return v_res_1764_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(lean_object* v_a_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Lean_Meta_reduceRecMatcher_x3f(v_a_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1785_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1774_ = v___x_1771_;
v_isShared_1775_ = v_isSharedCheck_1785_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1771_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1785_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
if (lean_obj_tag(v_a_1772_) == 1)
{
lean_object* v_val_1776_; lean_object* v___x_1777_; 
lean_del_object(v___x_1774_);
lean_dec_ref(v_a_1765_);
v_val_1776_ = lean_ctor_get(v_a_1772_, 0);
lean_inc(v_val_1776_);
lean_dec_ref_known(v_a_1772_, 1);
v___x_1777_ = l_Lean_Expr_headBeta(v_val_1776_);
v_a_1765_ = v___x_1777_;
goto _start;
}
else
{
lean_object* v___x_1779_; uint8_t v___x_1780_; 
lean_dec(v_a_1772_);
lean_inc_ref(v_a_1765_);
v___x_1779_ = l_Lean_Expr_headBeta(v_a_1765_);
v___x_1780_ = lean_expr_eqv(v_a_1765_, v___x_1779_);
if (v___x_1780_ == 0)
{
lean_del_object(v___x_1774_);
lean_dec_ref(v_a_1765_);
v_a_1765_ = v___x_1779_;
goto _start;
}
else
{
lean_object* v___x_1783_; 
lean_dec_ref(v___x_1779_);
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 0, v_a_1765_);
v___x_1783_ = v___x_1774_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1765_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_dec_ref(v_a_1765_);
v_a_1786_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1771_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1771_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1765_ = stack[0].m_obj;
lean_object* v___y_1766_ = stack[1].m_obj;
lean_object* v___y_1767_ = stack[2].m_obj;
lean_object* v___y_1768_ = stack[3].m_obj;
lean_object* v___y_1769_ = stack[4].m_obj;
lean_object* v_res_1794_;
v_res_1794_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(v_a_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
stack->m_obj
 = v_res_1794_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg___boxed(lean_object* v_a_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(v_a_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(lean_object* v_opts_1802_, lean_object* v_opt_1803_){
_start:
{
lean_object* v_name_1804_; lean_object* v_defValue_1805_; lean_object* v_map_1806_; lean_object* v___x_1807_; 
v_name_1804_ = lean_ctor_get(v_opt_1803_, 0);
v_defValue_1805_ = lean_ctor_get(v_opt_1803_, 1);
v_map_1806_ = lean_ctor_get(v_opts_1802_, 0);
v___x_1807_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1806_, v_name_1804_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_inc(v_defValue_1805_);
return v_defValue_1805_;
}
else
{
lean_object* v_val_1808_; 
v_val_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_val_1808_);
lean_dec_ref_known(v___x_1807_, 1);
if (lean_obj_tag(v_val_1808_) == 3)
{
lean_object* v_v_1809_; 
v_v_1809_ = lean_ctor_get(v_val_1808_, 0);
lean_inc(v_v_1809_);
lean_dec_ref_known(v_val_1808_, 1);
return v_v_1809_;
}
else
{
lean_dec(v_val_1808_);
lean_inc(v_defValue_1805_);
return v_defValue_1805_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16___boxed(lean_object* v_opts_1810_, lean_object* v_opt_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_1810_, v_opt_1811_);
lean_dec_ref(v_opt_1811_);
lean_dec_ref(v_opts_1810_);
return v_res_1812_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(lean_object* v_e_1813_){
_start:
{
if (lean_obj_tag(v_e_1813_) == 0)
{
uint8_t v___x_1814_; 
v___x_1814_ = 2;
return v___x_1814_;
}
else
{
uint8_t v___x_1815_; 
v___x_1815_ = 0;
return v___x_1815_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1813_ = stack[0].m_obj;
uint8_t v_res_1816_;
v_res_1816_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(v_e_1813_);
stack->m_num = v_res_1816_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___boxed(lean_object* v_e_1817_){
_start:
{
uint8_t v_res_1818_; lean_object* v_r_1819_; 
v_res_1818_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(v_e_1817_);
lean_dec_ref(v_e_1817_);
v_r_1819_ = lean_box(v_res_1818_);
return v_r_1819_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(lean_object* v_x_1820_){
_start:
{
if (lean_obj_tag(v_x_1820_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
v_a_1822_ = lean_ctor_get(v_x_1820_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v_x_1820_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v_x_1820_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v_x_1820_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set_tag(v___x_1824_, 1);
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
v_a_1830_ = lean_ctor_get(v_x_1820_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v_x_1820_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v_x_1820_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v_x_1820_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
lean_ctor_set_tag(v___x_1832_, 0);
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1820_ = stack[0].m_obj;
lean_object* v_res_1838_;
v_res_1838_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(v_x_1820_);
stack->m_obj
 = v_res_1838_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg___boxed(lean_object* v_x_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(v_x_1839_);
return v_res_1841_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15(size_t v_sz_1842_, size_t v_i_1843_, lean_object* v_bs_1844_){
_start:
{
uint8_t v___x_1845_; 
v___x_1845_ = lean_usize_dec_lt(v_i_1843_, v_sz_1842_);
if (v___x_1845_ == 0)
{
return v_bs_1844_;
}
else
{
lean_object* v_v_1846_; lean_object* v_msg_1847_; lean_object* v___x_1848_; lean_object* v_bs_x27_1849_; size_t v___x_1850_; size_t v___x_1851_; lean_object* v___x_1852_; 
v_v_1846_ = lean_array_uget_borrowed(v_bs_1844_, v_i_1843_);
v_msg_1847_ = lean_ctor_get(v_v_1846_, 1);
lean_inc_ref(v_msg_1847_);
v___x_1848_ = lean_unsigned_to_nat(0u);
v_bs_x27_1849_ = lean_array_uset(v_bs_1844_, v_i_1843_, v___x_1848_);
v___x_1850_ = ((size_t)1ULL);
v___x_1851_ = lean_usize_add(v_i_1843_, v___x_1850_);
v___x_1852_ = lean_array_uset(v_bs_x27_1849_, v_i_1843_, v_msg_1847_);
v_i_1843_ = v___x_1851_;
v_bs_1844_ = v___x_1852_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1842_ = stack[0].m_num;
size_t v_i_1843_ = stack[1].m_num;
lean_object* v_bs_1844_ = stack[2].m_obj;
lean_object* v_res_1854_;
v_res_1854_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15(v_sz_1842_, v_i_1843_, v_bs_1844_);
stack->m_obj
 = v_res_1854_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15___boxed(lean_object* v_sz_1855_, lean_object* v_i_1856_, lean_object* v_bs_1857_){
_start:
{
size_t v_sz_boxed_1858_; size_t v_i_boxed_1859_; lean_object* v_res_1860_; 
v_sz_boxed_1858_ = lean_unbox_usize(v_sz_1855_);
lean_dec(v_sz_1855_);
v_i_boxed_1859_ = lean_unbox_usize(v_i_1856_);
lean_dec(v_i_1856_);
v_res_1860_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15(v_sz_boxed_1858_, v_i_boxed_1859_, v_bs_1857_);
return v_res_1860_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(lean_object* v_oldTraces_1861_, lean_object* v_data_1862_, lean_object* v_ref_1863_, lean_object* v_msg_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v_toCold_1870_; lean_object* v_currRecDepth_1871_; lean_object* v_ref_1872_; uint16_t v_optionFlags_1873_; uint8_t v_suppressElabErrors_1874_; uint8_t v_isRecordingDeps_1875_; lean_object* v_ref_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v_traceState_1879_; lean_object* v_traces_1880_; lean_object* v___x_1881_; size_t v_sz_1882_; size_t v___x_1883_; lean_object* v___x_1884_; lean_object* v_msg_1885_; lean_object* v___x_1886_; lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1925_; 
v_toCold_1870_ = lean_ctor_get(v___y_1867_, 0);
v_currRecDepth_1871_ = lean_ctor_get(v___y_1867_, 1);
v_ref_1872_ = lean_ctor_get(v___y_1867_, 2);
v_optionFlags_1873_ = lean_ctor_get_uint16(v___y_1867_, sizeof(void*)*3);
v_suppressElabErrors_1874_ = lean_ctor_get_uint8(v___y_1867_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1875_ = lean_ctor_get_uint8(v___y_1867_, sizeof(void*)*3 + 3);
v_ref_1876_ = l_Lean_replaceRef(v_ref_1863_, v_ref_1872_);
lean_inc(v_currRecDepth_1871_);
lean_inc_ref(v_toCold_1870_);
v___x_1877_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1877_, 0, v_toCold_1870_);
lean_ctor_set(v___x_1877_, 1, v_currRecDepth_1871_);
lean_ctor_set(v___x_1877_, 2, v_ref_1876_);
lean_ctor_set_uint16(v___x_1877_, sizeof(void*)*3, v_optionFlags_1873_);
lean_ctor_set_uint8(v___x_1877_, sizeof(void*)*3 + 2, v_suppressElabErrors_1874_);
lean_ctor_set_uint8(v___x_1877_, sizeof(void*)*3 + 3, v_isRecordingDeps_1875_);
v___x_1878_ = lean_st_ref_get(v___y_1868_);
v_traceState_1879_ = lean_ctor_get(v___x_1878_, 4);
lean_inc_ref(v_traceState_1879_);
lean_dec(v___x_1878_);
v_traces_1880_ = lean_ctor_get(v_traceState_1879_, 0);
lean_inc_ref(v_traces_1880_);
lean_dec_ref(v_traceState_1879_);
v___x_1881_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1880_);
lean_dec_ref(v_traces_1880_);
v_sz_1882_ = lean_array_size(v___x_1881_);
v___x_1883_ = ((size_t)0ULL);
v___x_1884_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15(v_sz_1882_, v___x_1883_, v___x_1881_);
v_msg_1885_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1885_, 0, v_data_1862_);
lean_ctor_set(v_msg_1885_, 1, v_msg_1864_);
lean_ctor_set(v_msg_1885_, 2, v___x_1884_);
v___x_1886_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_1885_, v___y_1865_, v___y_1866_, v___x_1877_, v___y_1868_);
lean_dec_ref_known(v___x_1877_, 3);
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1889_ = v___x_1886_;
v_isShared_1890_ = v_isSharedCheck_1925_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1886_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1925_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1891_; lean_object* v_traceState_1892_; lean_object* v_env_1893_; lean_object* v_nextMacroScope_1894_; lean_object* v_ngen_1895_; lean_object* v_auxDeclNGen_1896_; lean_object* v_cache_1897_; lean_object* v_recordedDeps_1898_; lean_object* v_messages_1899_; lean_object* v_infoState_1900_; lean_object* v_snapshotTasks_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1924_; 
v___x_1891_ = lean_st_ref_take(v___y_1868_);
v_traceState_1892_ = lean_ctor_get(v___x_1891_, 4);
v_env_1893_ = lean_ctor_get(v___x_1891_, 0);
v_nextMacroScope_1894_ = lean_ctor_get(v___x_1891_, 1);
v_ngen_1895_ = lean_ctor_get(v___x_1891_, 2);
v_auxDeclNGen_1896_ = lean_ctor_get(v___x_1891_, 3);
v_cache_1897_ = lean_ctor_get(v___x_1891_, 5);
v_recordedDeps_1898_ = lean_ctor_get(v___x_1891_, 6);
v_messages_1899_ = lean_ctor_get(v___x_1891_, 7);
v_infoState_1900_ = lean_ctor_get(v___x_1891_, 8);
v_snapshotTasks_1901_ = lean_ctor_get(v___x_1891_, 9);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1903_ = v___x_1891_;
v_isShared_1904_ = v_isSharedCheck_1924_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_snapshotTasks_1901_);
lean_inc(v_infoState_1900_);
lean_inc(v_messages_1899_);
lean_inc(v_recordedDeps_1898_);
lean_inc(v_cache_1897_);
lean_inc(v_traceState_1892_);
lean_inc(v_auxDeclNGen_1896_);
lean_inc(v_ngen_1895_);
lean_inc(v_nextMacroScope_1894_);
lean_inc(v_env_1893_);
lean_dec(v___x_1891_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1924_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
uint64_t v_tid_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1922_; 
v_tid_1905_ = lean_ctor_get_uint64(v_traceState_1892_, sizeof(void*)*1);
v_isSharedCheck_1922_ = !lean_is_exclusive(v_traceState_1892_);
if (v_isSharedCheck_1922_ == 0)
{
lean_object* v_unused_1923_; 
v_unused_1923_ = lean_ctor_get(v_traceState_1892_, 0);
lean_dec(v_unused_1923_);
v___x_1907_ = v_traceState_1892_;
v_isShared_1908_ = v_isSharedCheck_1922_;
goto v_resetjp_1906_;
}
else
{
lean_dec(v_traceState_1892_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1922_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1913_; 
v___x_1909_ = lean_box(0);
v___x_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1910_, 0, v_ref_1863_);
lean_ctor_set(v___x_1910_, 1, v_a_1887_);
v___x_1911_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1861_, v___x_1910_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1911_);
v___x_1913_ = v___x_1907_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1911_);
lean_ctor_set_uint64(v_reuseFailAlloc_1921_, sizeof(void*)*1, v_tid_1905_);
v___x_1913_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1915_; 
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 4, v___x_1913_);
v___x_1915_ = v___x_1903_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_env_1893_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v_nextMacroScope_1894_);
lean_ctor_set(v_reuseFailAlloc_1920_, 2, v_ngen_1895_);
lean_ctor_set(v_reuseFailAlloc_1920_, 3, v_auxDeclNGen_1896_);
lean_ctor_set(v_reuseFailAlloc_1920_, 4, v___x_1913_);
lean_ctor_set(v_reuseFailAlloc_1920_, 5, v_cache_1897_);
lean_ctor_set(v_reuseFailAlloc_1920_, 6, v_recordedDeps_1898_);
lean_ctor_set(v_reuseFailAlloc_1920_, 7, v_messages_1899_);
lean_ctor_set(v_reuseFailAlloc_1920_, 8, v_infoState_1900_);
lean_ctor_set(v_reuseFailAlloc_1920_, 9, v_snapshotTasks_1901_);
v___x_1915_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
lean_object* v___x_1916_; lean_object* v___x_1918_; 
v___x_1916_ = lean_st_ref_put(v___y_1868_, v___x_1915_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v___x_1909_);
v___x_1918_ = v___x_1889_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1909_);
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
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_1861_ = stack[0].m_obj;
lean_object* v_data_1862_ = stack[1].m_obj;
lean_object* v_ref_1863_ = stack[2].m_obj;
lean_object* v_msg_1864_ = stack[3].m_obj;
lean_object* v___y_1865_ = stack[4].m_obj;
lean_object* v___y_1866_ = stack[5].m_obj;
lean_object* v___y_1867_ = stack[6].m_obj;
lean_object* v___y_1868_ = stack[7].m_obj;
lean_object* v_res_1926_;
v_res_1926_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(v_oldTraces_1861_, v_data_1862_, v_ref_1863_, v_msg_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
stack->m_obj
 = v_res_1926_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13___boxed(lean_object* v_oldTraces_1927_, lean_object* v_data_1928_, lean_object* v_ref_1929_, lean_object* v_msg_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(v_oldTraces_1927_, v_data_1928_, v_ref_1929_, v_msg_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
return v_res_1936_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1(void){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__0));
v___x_1939_ = l_Lean_stringToMessageData(v___x_1938_);
return v___x_1939_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2(void){
_start:
{
lean_object* v___x_1940_; double v___x_1941_; 
v___x_1940_ = lean_unsigned_to_nat(1000u);
v___x_1941_ = lean_float_of_nat(v___x_1940_);
return v___x_1941_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(lean_object* v_cls_1942_, uint8_t v_collapsed_1943_, lean_object* v_tag_1944_, lean_object* v_opts_1945_, uint8_t v_clsEnabled_1946_, lean_object* v_oldTraces_1947_, lean_object* v_msg_1948_, lean_object* v_resStartStop_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_fst_1955_; lean_object* v_snd_1956_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v_data_1960_; lean_object* v_fst_1971_; lean_object* v_snd_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; lean_object* v___y_1976_; lean_object* v_a_1977_; uint8_t v___y_1992_; double v___y_2024_; 
v_fst_1955_ = lean_ctor_get(v_resStartStop_1949_, 0);
lean_inc(v_fst_1955_);
v_snd_1956_ = lean_ctor_get(v_resStartStop_1949_, 1);
lean_inc(v_snd_1956_);
lean_dec_ref(v_resStartStop_1949_);
v_fst_1971_ = lean_ctor_get(v_snd_1956_, 0);
lean_inc(v_fst_1971_);
v_snd_1972_ = lean_ctor_get(v_snd_1956_, 1);
lean_inc(v_snd_1972_);
lean_dec(v_snd_1956_);
v___x_1973_ = l_Lean_trace_profiler;
v___x_1974_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_opts_1945_, v___x_1973_);
if (v___x_1974_ == 0)
{
v___y_1992_ = v___x_1974_;
goto v___jp_1991_;
}
else
{
lean_object* v___x_2029_; uint8_t v___x_2030_; 
v___x_2029_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2030_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_opts_1945_, v___x_2029_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; lean_object* v___x_2032_; double v___x_2033_; double v___x_2034_; double v___x_2035_; 
v___x_2031_ = l_Lean_trace_profiler_threshold;
v___x_2032_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_1945_, v___x_2031_);
v___x_2033_ = lean_float_of_nat(v___x_2032_);
v___x_2034_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2);
v___x_2035_ = lean_float_div(v___x_2033_, v___x_2034_);
v___y_2024_ = v___x_2035_;
goto v___jp_2023_;
}
else
{
lean_object* v___x_2036_; lean_object* v___x_2037_; double v___x_2038_; 
v___x_2036_ = l_Lean_trace_profiler_threshold;
v___x_2037_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_1945_, v___x_2036_);
v___x_2038_ = lean_float_of_nat(v___x_2037_);
v___y_2024_ = v___x_2038_;
goto v___jp_2023_;
}
}
v___jp_1957_:
{
lean_object* v___x_1961_; 
lean_inc(v___y_1959_);
v___x_1961_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(v_oldTraces_1947_, v_data_1960_, v___y_1959_, v___y_1958_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v___x_1962_; 
lean_dec_ref_known(v___x_1961_, 1);
v___x_1962_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(v_fst_1955_);
return v___x_1962_;
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_dec(v_fst_1955_);
v_a_1963_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1961_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1961_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
v___jp_1975_:
{
uint8_t v_result_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; double v___x_1981_; lean_object* v_data_1982_; 
v_result_1978_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(v_fst_1955_);
v___x_1979_ = lean_box(v_result_1978_);
v___x_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
v___x_1981_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0);
lean_inc_ref(v_tag_1944_);
lean_inc_ref(v___x_1980_);
lean_inc(v_cls_1942_);
v_data_1982_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1982_, 0, v_cls_1942_);
lean_ctor_set(v_data_1982_, 1, v___x_1980_);
lean_ctor_set(v_data_1982_, 2, v_tag_1944_);
lean_ctor_set_float(v_data_1982_, sizeof(void*)*3, v___x_1981_);
lean_ctor_set_float(v_data_1982_, sizeof(void*)*3 + 8, v___x_1981_);
lean_ctor_set_uint8(v_data_1982_, sizeof(void*)*3 + 16, v_collapsed_1943_);
if (v___x_1974_ == 0)
{
lean_dec_ref_known(v___x_1980_, 1);
lean_dec(v_snd_1972_);
lean_dec(v_fst_1971_);
lean_dec_ref(v_tag_1944_);
lean_dec(v_cls_1942_);
v___y_1958_ = v_a_1977_;
v___y_1959_ = v___y_1976_;
v_data_1960_ = v_data_1982_;
goto v___jp_1957_;
}
else
{
lean_object* v_data_1983_; double v___x_1984_; double v___x_1985_; 
lean_dec_ref_known(v_data_1982_, 3);
v_data_1983_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1983_, 0, v_cls_1942_);
lean_ctor_set(v_data_1983_, 1, v___x_1980_);
lean_ctor_set(v_data_1983_, 2, v_tag_1944_);
v___x_1984_ = lean_unbox_float(v_fst_1971_);
lean_dec(v_fst_1971_);
lean_ctor_set_float(v_data_1983_, sizeof(void*)*3, v___x_1984_);
v___x_1985_ = lean_unbox_float(v_snd_1972_);
lean_dec(v_snd_1972_);
lean_ctor_set_float(v_data_1983_, sizeof(void*)*3 + 8, v___x_1985_);
lean_ctor_set_uint8(v_data_1983_, sizeof(void*)*3 + 16, v_collapsed_1943_);
v___y_1958_ = v_a_1977_;
v___y_1959_ = v___y_1976_;
v_data_1960_ = v_data_1983_;
goto v___jp_1957_;
}
}
v___jp_1986_:
{
lean_object* v_ref_1987_; lean_object* v___x_1988_; 
v_ref_1987_ = lean_ctor_get(v___y_1952_, 2);
lean_inc(v___y_1953_);
lean_inc_ref(v___y_1952_);
lean_inc(v___y_1951_);
lean_inc_ref(v___y_1950_);
lean_inc(v_fst_1955_);
v___x_1988_ = lean_apply_6(v_msg_1948_, v_fst_1955_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, lean_box(0));
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_a_1989_);
lean_dec_ref_known(v___x_1988_, 1);
v___y_1976_ = v_ref_1987_;
v_a_1977_ = v_a_1989_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_1990_; 
lean_dec_ref_known(v___x_1988_, 1);
v___x_1990_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1);
v___y_1976_ = v_ref_1987_;
v_a_1977_ = v___x_1990_;
goto v___jp_1975_;
}
}
v___jp_1991_:
{
if (v_clsEnabled_1946_ == 0)
{
if (v___y_1992_ == 0)
{
lean_object* v___x_1993_; lean_object* v_traceState_1994_; lean_object* v_env_1995_; lean_object* v_nextMacroScope_1996_; lean_object* v_ngen_1997_; lean_object* v_auxDeclNGen_1998_; lean_object* v_cache_1999_; lean_object* v_recordedDeps_2000_; lean_object* v_messages_2001_; lean_object* v_infoState_2002_; lean_object* v_snapshotTasks_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2022_; 
lean_dec(v_snd_1972_);
lean_dec(v_fst_1971_);
lean_dec_ref(v_msg_1948_);
lean_dec_ref(v_tag_1944_);
lean_dec(v_cls_1942_);
v___x_1993_ = lean_st_ref_take(v___y_1953_);
v_traceState_1994_ = lean_ctor_get(v___x_1993_, 4);
v_env_1995_ = lean_ctor_get(v___x_1993_, 0);
v_nextMacroScope_1996_ = lean_ctor_get(v___x_1993_, 1);
v_ngen_1997_ = lean_ctor_get(v___x_1993_, 2);
v_auxDeclNGen_1998_ = lean_ctor_get(v___x_1993_, 3);
v_cache_1999_ = lean_ctor_get(v___x_1993_, 5);
v_recordedDeps_2000_ = lean_ctor_get(v___x_1993_, 6);
v_messages_2001_ = lean_ctor_get(v___x_1993_, 7);
v_infoState_2002_ = lean_ctor_get(v___x_1993_, 8);
v_snapshotTasks_2003_ = lean_ctor_get(v___x_1993_, 9);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2005_ = v___x_1993_;
v_isShared_2006_ = v_isSharedCheck_2022_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_snapshotTasks_2003_);
lean_inc(v_infoState_2002_);
lean_inc(v_messages_2001_);
lean_inc(v_recordedDeps_2000_);
lean_inc(v_cache_1999_);
lean_inc(v_traceState_1994_);
lean_inc(v_auxDeclNGen_1998_);
lean_inc(v_ngen_1997_);
lean_inc(v_nextMacroScope_1996_);
lean_inc(v_env_1995_);
lean_dec(v___x_1993_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2022_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
uint64_t v_tid_2007_; lean_object* v_traces_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2021_; 
v_tid_2007_ = lean_ctor_get_uint64(v_traceState_1994_, sizeof(void*)*1);
v_traces_2008_ = lean_ctor_get(v_traceState_1994_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v_traceState_1994_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2010_ = v_traceState_1994_;
v_isShared_2011_ = v_isSharedCheck_2021_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_traces_2008_);
lean_dec(v_traceState_1994_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2021_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; lean_object* v___x_2014_; 
v___x_2012_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1947_, v_traces_2008_);
lean_dec_ref(v_traces_2008_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2012_);
v___x_2014_ = v___x_2010_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2012_);
lean_ctor_set_uint64(v_reuseFailAlloc_2020_, sizeof(void*)*1, v_tid_2007_);
v___x_2014_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
lean_object* v___x_2016_; 
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 4, v___x_2014_);
v___x_2016_ = v___x_2005_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_env_1995_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_nextMacroScope_1996_);
lean_ctor_set(v_reuseFailAlloc_2019_, 2, v_ngen_1997_);
lean_ctor_set(v_reuseFailAlloc_2019_, 3, v_auxDeclNGen_1998_);
lean_ctor_set(v_reuseFailAlloc_2019_, 4, v___x_2014_);
lean_ctor_set(v_reuseFailAlloc_2019_, 5, v_cache_1999_);
lean_ctor_set(v_reuseFailAlloc_2019_, 6, v_recordedDeps_2000_);
lean_ctor_set(v_reuseFailAlloc_2019_, 7, v_messages_2001_);
lean_ctor_set(v_reuseFailAlloc_2019_, 8, v_infoState_2002_);
lean_ctor_set(v_reuseFailAlloc_2019_, 9, v_snapshotTasks_2003_);
v___x_2016_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2017_ = lean_st_ref_put(v___y_1953_, v___x_2016_);
v___x_2018_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(v_fst_1955_);
return v___x_2018_;
}
}
}
}
}
else
{
goto v___jp_1986_;
}
}
else
{
goto v___jp_1986_;
}
}
v___jp_2023_:
{
double v___x_2025_; double v___x_2026_; double v___x_2027_; uint8_t v___x_2028_; 
v___x_2025_ = lean_unbox_float(v_snd_1972_);
v___x_2026_ = lean_unbox_float(v_fst_1971_);
v___x_2027_ = lean_float_sub(v___x_2025_, v___x_2026_);
v___x_2028_ = lean_float_decLt(v___y_2024_, v___x_2027_);
v___y_1992_ = v___x_2028_;
goto v___jp_1991_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1942_ = stack[0].m_obj;
uint8_t v_collapsed_1943_ = stack[1].m_num;
lean_object* v_tag_1944_ = stack[2].m_obj;
lean_object* v_opts_1945_ = stack[3].m_obj;
uint8_t v_clsEnabled_1946_ = stack[4].m_num;
lean_object* v_oldTraces_1947_ = stack[5].m_obj;
lean_object* v_msg_1948_ = stack[6].m_obj;
lean_object* v_resStartStop_1949_ = stack[7].m_obj;
lean_object* v___y_1950_ = stack[8].m_obj;
lean_object* v___y_1951_ = stack[9].m_obj;
lean_object* v___y_1952_ = stack[10].m_obj;
lean_object* v___y_1953_ = stack[11].m_obj;
lean_object* v_res_2039_;
v_res_2039_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v_cls_1942_, v_collapsed_1943_, v_tag_1944_, v_opts_1945_, v_clsEnabled_1946_, v_oldTraces_1947_, v_msg_1948_, v_resStartStop_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
stack->m_obj
 = v_res_2039_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___boxed(lean_object* v_cls_2040_, lean_object* v_collapsed_2041_, lean_object* v_tag_2042_, lean_object* v_opts_2043_, lean_object* v_clsEnabled_2044_, lean_object* v_oldTraces_2045_, lean_object* v_msg_2046_, lean_object* v_resStartStop_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
uint8_t v_collapsed_boxed_2053_; uint8_t v_clsEnabled_boxed_2054_; lean_object* v_res_2055_; 
v_collapsed_boxed_2053_ = lean_unbox(v_collapsed_2041_);
v_clsEnabled_boxed_2054_ = lean_unbox(v_clsEnabled_2044_);
v_res_2055_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v_cls_2040_, v_collapsed_boxed_2053_, v_tag_2042_, v_opts_2043_, v_clsEnabled_boxed_2054_, v_oldTraces_2045_, v_msg_2046_, v_resStartStop_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec_ref(v_opts_2043_);
return v_res_2055_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__3(void){
_start:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2060_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__2));
v___x_2061_ = l_Lean_stringToMessageData(v___x_2060_);
return v___x_2061_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__5(void){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2063_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__4));
v___x_2064_ = l_Lean_stringToMessageData(v___x_2063_);
return v___x_2064_;
}
}
static double _init_l_Lean_Meta_rwMatcher___closed__6(void){
_start:
{
lean_object* v___x_2065_; double v___x_2066_; 
v___x_2065_ = lean_unsigned_to_nat(1000000000u);
v___x_2066_ = lean_float_of_nat(v___x_2065_);
return v___x_2066_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__8(void){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2068_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__7));
v___x_2069_ = l_Lean_stringToMessageData(v___x_2068_);
return v___x_2069_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__13(void){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2077_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2078_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
v___x_2079_ = l_Lean_Name_append(v___x_2078_, v___x_2077_);
return v___x_2079_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__15(void){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__14));
v___x_2082_ = l_Lean_stringToMessageData(v___x_2081_);
return v___x_2082_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__17(void){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__16));
v___x_2085_ = l_Lean_stringToMessageData(v___x_2084_);
return v___x_2085_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__19(void){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__18));
v___x_2088_ = l_Lean_stringToMessageData(v___x_2087_);
return v___x_2088_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__21(void){
_start:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2090_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__20));
v___x_2091_ = l_Lean_stringToMessageData(v___x_2090_);
return v___x_2091_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__22(void){
_start:
{
lean_object* v___x_2092_; lean_object* v_dummy_2093_; 
v___x_2092_ = lean_box(0);
v_dummy_2093_ = l_Lean_Expr_sort___override(v___x_2092_);
return v_dummy_2093_;
}
}
lean_object* l_Lean_Meta_rwMatcher(lean_object* v_altIdx_2103_, lean_object* v_e_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v___y_2111_; lean_object* v___y_2130_; lean_object* v___y_2134_; lean_object* v___y_2135_; uint8_t v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; uint8_t v___y_2139_; lean_object* v___y_2168_; uint8_t v___y_2169_; lean_object* v___y_2170_; lean_object* v___y_2171_; lean_object* v_a_2172_; lean_object* v___y_2176_; uint8_t v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2187_; uint8_t v___y_2188_; lean_object* v___y_2189_; uint8_t v___y_2190_; uint8_t v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v_a_2194_; lean_object* v___y_2204_; lean_object* v___y_2205_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; uint8_t v___y_2209_; uint8_t v___y_2210_; uint8_t v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v_a_2215_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; uint8_t v___y_2223_; uint8_t v___y_2224_; uint8_t v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; uint8_t v___y_2245_; lean_object* v___y_2246_; uint8_t v___y_2247_; uint8_t v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v_a_2251_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; uint8_t v___y_2269_; uint8_t v___y_2270_; uint8_t v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v_a_2275_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; uint8_t v___y_2283_; uint8_t v___y_2284_; uint8_t v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2300_; lean_object* v___y_2301_; uint8_t v___y_2302_; lean_object* v___y_2303_; uint8_t v___y_2304_; lean_object* v___y_2305_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; uint8_t v___y_2310_; uint8_t v___y_2311_; uint8_t v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2314_; uint8_t v___y_2380_; uint8_t v___y_2385_; lean_object* v___y_2390_; uint8_t v___y_2391_; lean_object* v_proof_2392_; lean_object* v___y_2397_; lean_object* v___y_2398_; uint8_t v___y_2399_; lean_object* v___y_2400_; uint8_t v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; uint8_t v___y_2410_; uint8_t v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; uint8_t v___y_2420_; lean_object* v___y_2433_; lean_object* v___y_2434_; uint8_t v___y_2435_; lean_object* v___y_2436_; uint8_t v___y_2437_; lean_object* v___y_2438_; uint8_t v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; uint8_t v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; uint8_t v___y_2462_; uint8_t v___y_2463_; lean_object* v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v_a_2467_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; uint8_t v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; uint8_t v___y_2491_; lean_object* v___y_2492_; uint8_t v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2500_; lean_object* v___y_2501_; size_t v___y_2502_; lean_object* v___y_2503_; uint8_t v___y_2504_; lean_object* v___y_2505_; uint8_t v___y_2506_; lean_object* v___y_2507_; uint8_t v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2528_; size_t v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; uint8_t v___y_2532_; uint8_t v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; uint8_t v_fst_2536_; lean_object* v_fst_2537_; lean_object* v_snd_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___x_2562_; uint8_t v___y_2564_; lean_object* v___x_2757_; uint8_t v___x_2758_; 
v___x_2562_ = lean_box(0);
v___x_2757_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__25));
v___x_2758_ = l_Lean_Expr_isAppOf(v_e_2104_, v___x_2757_);
if (v___x_2758_ == 0)
{
lean_object* v___x_2759_; uint8_t v___x_2760_; 
v___x_2759_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__27));
v___x_2760_ = l_Lean_Expr_isAppOf(v_e_2104_, v___x_2759_);
v___y_2564_ = v___x_2760_;
goto v___jp_2563_;
}
else
{
v___y_2564_ = v___x_2758_;
goto v___jp_2563_;
}
v___jp_2110_:
{
if (lean_obj_tag(v___y_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2120_; 
v_a_2112_ = lean_ctor_get(v___y_2111_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___y_2111_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2114_ = v___y_2111_;
v_isShared_2115_ = v_isSharedCheck_2120_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___y_2111_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2120_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v_a_2116_; lean_object* v___x_2118_; 
v_a_2116_ = lean_ctor_get(v_a_2112_, 0);
lean_inc(v_a_2116_);
lean_dec(v_a_2112_);
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 0, v_a_2116_);
v___x_2118_ = v___x_2114_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2116_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
v_a_2121_ = lean_ctor_get(v___y_2111_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___y_2111_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___y_2111_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___y_2111_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
v___jp_2129_:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2131_ = lean_box(0);
lean_inc(v_a_2108_);
lean_inc_ref(v_a_2107_);
lean_inc(v_a_2106_);
lean_inc_ref(v_a_2105_);
v___x_2132_ = lean_apply_6(v___y_2130_, v___x_2131_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, lean_box(0));
v___y_2111_ = v___x_2132_;
goto v___jp_2110_;
}
v___jp_2133_:
{
if (v___y_2139_ == 0)
{
lean_object* v_toCold_2140_; lean_object* v_options_2141_; uint8_t v_hasTrace_2142_; 
v_toCold_2140_ = lean_ctor_get(v_a_2107_, 0);
v_options_2141_ = lean_ctor_get(v_toCold_2140_, 2);
v_hasTrace_2142_ = lean_ctor_get_uint8(v_options_2141_, sizeof(void*)*1);
if (v_hasTrace_2142_ == 0)
{
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
v___y_2130_ = v___y_2137_;
goto v___jp_2129_;
}
else
{
lean_object* v_inheritedTraceOptions_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; 
v_inheritedTraceOptions_2143_ = lean_ctor_get(v_toCold_2140_, 11);
v___x_2144_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2138_);
v___x_2145_ = l_Lean_Name_append(v___x_2144_, v___y_2138_);
v___x_2146_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2143_, v_options_2141_, v___x_2145_);
lean_dec(v___x_2145_);
if (v___x_2146_ == 0)
{
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
v___y_2130_ = v___y_2137_;
goto v___jp_2129_;
}
else
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2147_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__3, &l_Lean_Meta_rwMatcher___closed__3_once, _init_l_Lean_Meta_rwMatcher___closed__3);
v___x_2148_ = l_Lean_MessageData_ofConstName(v___y_2134_, v___y_2136_);
v___x_2149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2147_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__5, &l_Lean_Meta_rwMatcher___closed__5_once, _init_l_Lean_Meta_rwMatcher___closed__5);
v___x_2151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2149_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
v___x_2152_ = l_Lean_Exception_toMessageData(v___y_2135_);
v___x_2153_ = l_Lean_indentD(v___x_2152_);
v___x_2154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2151_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2138_, v___x_2154_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v___x_2157_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_a_2156_);
lean_dec_ref_known(v___x_2155_, 1);
lean_inc(v_a_2108_);
lean_inc_ref(v_a_2107_);
lean_inc(v_a_2106_);
lean_inc_ref(v_a_2105_);
v___x_2157_ = lean_apply_6(v___y_2137_, v_a_2156_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, lean_box(0));
v___y_2111_ = v___x_2157_;
goto v___jp_2110_;
}
else
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
lean_dec_ref(v___y_2137_);
v_a_2158_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2155_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2155_);
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
}
else
{
lean_object* v___x_2166_; 
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2134_);
v___x_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2166_, 0, v___y_2135_);
return v___x_2166_;
}
}
v___jp_2167_:
{
uint8_t v___x_2173_; 
v___x_2173_ = l_Lean_Exception_isInterrupt(v_a_2172_);
if (v___x_2173_ == 0)
{
uint8_t v___x_2174_; 
lean_inc_ref(v_a_2172_);
v___x_2174_ = l_Lean_Exception_isRuntime(v_a_2172_);
v___y_2134_ = v___y_2168_;
v___y_2135_ = v_a_2172_;
v___y_2136_ = v___y_2169_;
v___y_2137_ = v___y_2170_;
v___y_2138_ = v___y_2171_;
v___y_2139_ = v___x_2174_;
goto v___jp_2133_;
}
else
{
v___y_2134_ = v___y_2168_;
v___y_2135_ = v_a_2172_;
v___y_2136_ = v___y_2169_;
v___y_2137_ = v___y_2170_;
v___y_2138_ = v___y_2171_;
v___y_2139_ = v___x_2173_;
goto v___jp_2133_;
}
}
v___jp_2175_:
{
if (lean_obj_tag(v___y_2180_) == 0)
{
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2176_);
return v___y_2180_;
}
else
{
lean_object* v_a_2181_; 
v_a_2181_ = lean_ctor_get(v___y_2180_, 0);
lean_inc(v_a_2181_);
lean_dec_ref_known(v___y_2180_, 1);
v___y_2168_ = v___y_2176_;
v___y_2169_ = v___y_2177_;
v___y_2170_ = v___y_2178_;
v___y_2171_ = v___y_2179_;
v_a_2172_ = v_a_2181_;
goto v___jp_2167_;
}
}
v___jp_2182_:
{
lean_object* v___x_2195_; double v___x_2196_; double v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2195_ = lean_io_get_num_heartbeats();
v___x_2196_ = lean_float_of_nat(v___y_2187_);
v___x_2197_ = lean_float_of_nat(v___x_2195_);
v___x_2198_ = lean_box_float(v___x_2196_);
v___x_2199_ = lean_box_float(v___x_2197_);
v___x_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2198_);
lean_ctor_set(v___x_2200_, 1, v___x_2199_);
v___x_2201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2201_, 0, v_a_2194_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
lean_inc_ref(v___y_2186_);
lean_inc(v___y_2193_);
v___x_2202_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v___y_2193_, v___y_2191_, v___y_2186_, v___y_2185_, v___y_2190_, v___y_2192_, v___y_2183_, v___x_2201_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
v___y_2176_ = v___y_2184_;
v___y_2177_ = v___y_2188_;
v___y_2178_ = v___y_2189_;
v___y_2179_ = v___y_2193_;
v___y_2180_ = v___x_2202_;
goto v___jp_2175_;
}
v___jp_2203_:
{
lean_object* v___x_2216_; 
v___x_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2216_, 0, v_a_2215_);
v___y_2183_ = v___y_2204_;
v___y_2184_ = v___y_2205_;
v___y_2185_ = v___y_2206_;
v___y_2186_ = v___y_2207_;
v___y_2187_ = v___y_2208_;
v___y_2188_ = v___y_2209_;
v___y_2189_ = v___y_2212_;
v___y_2190_ = v___y_2211_;
v___y_2191_ = v___y_2210_;
v___y_2192_ = v___y_2213_;
v___y_2193_ = v___y_2214_;
v_a_2194_ = v___x_2216_;
goto v___jp_2182_;
}
v___jp_2217_:
{
if (lean_obj_tag(v___y_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
v_a_2230_ = lean_ctor_get(v___y_2229_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___y_2229_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___y_2229_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___y_2229_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
lean_ctor_set_tag(v___x_2232_, 1);
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
v___y_2183_ = v___y_2218_;
v___y_2184_ = v___y_2219_;
v___y_2185_ = v___y_2220_;
v___y_2186_ = v___y_2221_;
v___y_2187_ = v___y_2222_;
v___y_2188_ = v___y_2223_;
v___y_2189_ = v___y_2226_;
v___y_2190_ = v___y_2225_;
v___y_2191_ = v___y_2224_;
v___y_2192_ = v___y_2227_;
v___y_2193_ = v___y_2228_;
v_a_2194_ = v___x_2235_;
goto v___jp_2182_;
}
}
}
else
{
lean_object* v_a_2238_; 
v_a_2238_ = lean_ctor_get(v___y_2229_, 0);
lean_inc(v_a_2238_);
lean_dec_ref_known(v___y_2229_, 1);
v___y_2204_ = v___y_2218_;
v___y_2205_ = v___y_2219_;
v___y_2206_ = v___y_2220_;
v___y_2207_ = v___y_2221_;
v___y_2208_ = v___y_2222_;
v___y_2209_ = v___y_2223_;
v___y_2210_ = v___y_2224_;
v___y_2211_ = v___y_2225_;
v___y_2212_ = v___y_2226_;
v___y_2213_ = v___y_2227_;
v___y_2214_ = v___y_2228_;
v_a_2215_ = v_a_2238_;
goto v___jp_2203_;
}
}
v___jp_2239_:
{
lean_object* v___x_2252_; double v___x_2253_; double v___x_2254_; double v___x_2255_; double v___x_2256_; double v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2252_ = lean_io_mono_nanos_now();
v___x_2253_ = lean_float_of_nat(v___y_2244_);
v___x_2254_ = lean_float_once(&l_Lean_Meta_rwMatcher___closed__6, &l_Lean_Meta_rwMatcher___closed__6_once, _init_l_Lean_Meta_rwMatcher___closed__6);
v___x_2255_ = lean_float_div(v___x_2253_, v___x_2254_);
v___x_2256_ = lean_float_of_nat(v___x_2252_);
v___x_2257_ = lean_float_div(v___x_2256_, v___x_2254_);
v___x_2258_ = lean_box_float(v___x_2255_);
v___x_2259_ = lean_box_float(v___x_2257_);
v___x_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2258_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
v___x_2261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2261_, 0, v_a_2251_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
lean_inc_ref(v___y_2243_);
lean_inc(v___y_2250_);
v___x_2262_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v___y_2250_, v___y_2248_, v___y_2243_, v___y_2242_, v___y_2247_, v___y_2249_, v___y_2240_, v___x_2261_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
v___y_2176_ = v___y_2241_;
v___y_2177_ = v___y_2245_;
v___y_2178_ = v___y_2246_;
v___y_2179_ = v___y_2250_;
v___y_2180_ = v___x_2262_;
goto v___jp_2175_;
}
v___jp_2263_:
{
lean_object* v___x_2276_; 
v___x_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2276_, 0, v_a_2275_);
v___y_2240_ = v___y_2264_;
v___y_2241_ = v___y_2265_;
v___y_2242_ = v___y_2266_;
v___y_2243_ = v___y_2268_;
v___y_2244_ = v___y_2267_;
v___y_2245_ = v___y_2269_;
v___y_2246_ = v___y_2272_;
v___y_2247_ = v___y_2271_;
v___y_2248_ = v___y_2270_;
v___y_2249_ = v___y_2273_;
v___y_2250_ = v___y_2274_;
v_a_2251_ = v___x_2276_;
goto v___jp_2239_;
}
v___jp_2277_:
{
if (lean_obj_tag(v___y_2289_) == 0)
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
v_a_2290_ = lean_ctor_get(v___y_2289_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___y_2289_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___y_2289_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___y_2289_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
lean_ctor_set_tag(v___x_2292_, 1);
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
v___y_2240_ = v___y_2278_;
v___y_2241_ = v___y_2279_;
v___y_2242_ = v___y_2280_;
v___y_2243_ = v___y_2282_;
v___y_2244_ = v___y_2281_;
v___y_2245_ = v___y_2283_;
v___y_2246_ = v___y_2286_;
v___y_2247_ = v___y_2285_;
v___y_2248_ = v___y_2284_;
v___y_2249_ = v___y_2287_;
v___y_2250_ = v___y_2288_;
v_a_2251_ = v___x_2295_;
goto v___jp_2239_;
}
}
}
else
{
lean_object* v_a_2298_; 
v_a_2298_ = lean_ctor_get(v___y_2289_, 0);
lean_inc(v_a_2298_);
lean_dec_ref_known(v___y_2289_, 1);
v___y_2264_ = v___y_2278_;
v___y_2265_ = v___y_2279_;
v___y_2266_ = v___y_2280_;
v___y_2267_ = v___y_2281_;
v___y_2268_ = v___y_2282_;
v___y_2269_ = v___y_2283_;
v___y_2270_ = v___y_2284_;
v___y_2271_ = v___y_2285_;
v___y_2272_ = v___y_2286_;
v___y_2273_ = v___y_2287_;
v___y_2274_ = v___y_2288_;
v_a_2275_ = v_a_2298_;
goto v___jp_2263_;
}
}
v___jp_2299_:
{
lean_object* v___x_2315_; lean_object* v_a_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; 
v___x_2315_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg(v_a_2108_);
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref(v___x_2315_);
v___x_2317_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2318_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v___y_2306_, v___x_2317_);
if (v___x_2318_ == 0)
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = lean_io_mono_nanos_now();
lean_inc(v_a_2108_);
lean_inc_ref(v_a_2107_);
lean_inc(v_a_2106_);
lean_inc_ref(v_a_2105_);
v___x_2320_ = lean_infer_type(v___y_2309_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; uint8_t v___x_2322_; lean_object* v___x_2323_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref_known(v___x_2320_, 1);
v___x_2322_ = 0;
v___x_2323_ = l_Lean_Meta_forallMetaTelescope(v_a_2321_, v___x_2322_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v_snd_2325_; lean_object* v_fst_2326_; lean_object* v_snd_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2345_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref_known(v___x_2323_, 1);
v_snd_2325_ = lean_ctor_get(v_a_2324_, 1);
lean_inc(v_snd_2325_);
v_fst_2326_ = lean_ctor_get(v_a_2324_, 0);
lean_inc(v_fst_2326_);
lean_dec(v_a_2324_);
v_snd_2327_ = lean_ctor_get(v_snd_2325_, 1);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_snd_2325_);
if (v_isSharedCheck_2345_ == 0)
{
lean_object* v_unused_2346_; 
v_unused_2346_ = lean_ctor_get(v_snd_2325_, 0);
lean_dec(v_unused_2346_);
v___x_2329_ = v_snd_2325_;
v_isShared_2330_ = v_isSharedCheck_2345_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_snd_2327_);
lean_dec(v_snd_2325_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2345_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; uint8_t v___x_2333_; 
v___x_2331_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2314_);
v___x_2332_ = l_Lean_Name_append(v___x_2331_, v___y_2314_);
v___x_2333_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2307_, v___y_2306_, v___x_2332_);
lean_dec(v___x_2332_);
if (v___x_2333_ == 0)
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
lean_del_object(v___x_2329_);
v___x_2334_ = lean_box(0);
v___x_2335_ = l_Lean_Meta_rwMatcher___lam__2(v___y_2304_, v___y_2303_, v_fst_2326_, v___y_2301_, v_e_2104_, v___y_2302_, v_snd_2327_, v___x_2334_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
lean_dec(v_snd_2327_);
v___y_2278_ = v___y_2300_;
v___y_2279_ = v___y_2305_;
v___y_2280_ = v___y_2306_;
v___y_2281_ = v___x_2319_;
v___y_2282_ = v___y_2308_;
v___y_2283_ = v___y_2310_;
v___y_2284_ = v___y_2311_;
v___y_2285_ = v___y_2312_;
v___y_2286_ = v___y_2313_;
v___y_2287_ = v_a_2316_;
v___y_2288_ = v___y_2314_;
v___y_2289_ = v___x_2335_;
goto v___jp_2277_;
}
else
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2339_; 
v___x_2336_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2327_);
v___x_2337_ = l_Lean_indentExpr(v_snd_2327_);
if (v_isShared_2330_ == 0)
{
lean_ctor_set_tag(v___x_2329_, 7);
lean_ctor_set(v___x_2329_, 1, v___x_2337_);
lean_ctor_set(v___x_2329_, 0, v___x_2336_);
v___x_2339_ = v___x_2329_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2336_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v___x_2337_);
v___x_2339_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
lean_object* v___x_2340_; 
lean_inc(v___y_2314_);
v___x_2340_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2314_, v___x_2339_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v___x_2342_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
lean_dec_ref_known(v___x_2340_, 1);
v___x_2342_ = l_Lean_Meta_rwMatcher___lam__2(v___y_2304_, v___y_2303_, v_fst_2326_, v___y_2301_, v_e_2104_, v___y_2302_, v_snd_2327_, v_a_2341_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
lean_dec(v_snd_2327_);
v___y_2278_ = v___y_2300_;
v___y_2279_ = v___y_2305_;
v___y_2280_ = v___y_2306_;
v___y_2281_ = v___x_2319_;
v___y_2282_ = v___y_2308_;
v___y_2283_ = v___y_2310_;
v___y_2284_ = v___y_2311_;
v___y_2285_ = v___y_2312_;
v___y_2286_ = v___y_2313_;
v___y_2287_ = v_a_2316_;
v___y_2288_ = v___y_2314_;
v___y_2289_ = v___x_2342_;
goto v___jp_2277_;
}
else
{
lean_object* v_a_2343_; 
lean_dec(v_snd_2327_);
lean_dec(v_fst_2326_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2301_);
lean_dec_ref(v_e_2104_);
v_a_2343_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2343_);
lean_dec_ref_known(v___x_2340_, 1);
v___y_2264_ = v___y_2300_;
v___y_2265_ = v___y_2305_;
v___y_2266_ = v___y_2306_;
v___y_2267_ = v___x_2319_;
v___y_2268_ = v___y_2308_;
v___y_2269_ = v___y_2310_;
v___y_2270_ = v___y_2311_;
v___y_2271_ = v___y_2312_;
v___y_2272_ = v___y_2313_;
v___y_2273_ = v_a_2316_;
v___y_2274_ = v___y_2314_;
v_a_2275_ = v_a_2343_;
goto v___jp_2263_;
}
}
}
}
}
else
{
lean_object* v_a_2347_; 
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2301_);
lean_dec_ref(v_e_2104_);
v_a_2347_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2347_);
lean_dec_ref_known(v___x_2323_, 1);
v___y_2264_ = v___y_2300_;
v___y_2265_ = v___y_2305_;
v___y_2266_ = v___y_2306_;
v___y_2267_ = v___x_2319_;
v___y_2268_ = v___y_2308_;
v___y_2269_ = v___y_2310_;
v___y_2270_ = v___y_2311_;
v___y_2271_ = v___y_2312_;
v___y_2272_ = v___y_2313_;
v___y_2273_ = v_a_2316_;
v___y_2274_ = v___y_2314_;
v_a_2275_ = v_a_2347_;
goto v___jp_2263_;
}
}
else
{
lean_object* v_a_2348_; 
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2301_);
lean_dec_ref(v_e_2104_);
v_a_2348_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2348_);
lean_dec_ref_known(v___x_2320_, 1);
v___y_2264_ = v___y_2300_;
v___y_2265_ = v___y_2305_;
v___y_2266_ = v___y_2306_;
v___y_2267_ = v___x_2319_;
v___y_2268_ = v___y_2308_;
v___y_2269_ = v___y_2310_;
v___y_2270_ = v___y_2311_;
v___y_2271_ = v___y_2312_;
v___y_2272_ = v___y_2313_;
v___y_2273_ = v_a_2316_;
v___y_2274_ = v___y_2314_;
v_a_2275_ = v_a_2348_;
goto v___jp_2263_;
}
}
else
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2349_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2108_);
lean_inc_ref(v_a_2107_);
lean_inc(v_a_2106_);
lean_inc_ref(v_a_2105_);
v___x_2350_ = lean_infer_type(v___y_2309_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; uint8_t v___x_2352_; lean_object* v___x_2353_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2351_);
lean_dec_ref_known(v___x_2350_, 1);
v___x_2352_ = 0;
v___x_2353_ = l_Lean_Meta_forallMetaTelescope(v_a_2351_, v___x_2352_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v_snd_2355_; lean_object* v_fst_2356_; lean_object* v_snd_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2375_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2354_);
lean_dec_ref_known(v___x_2353_, 1);
v_snd_2355_ = lean_ctor_get(v_a_2354_, 1);
lean_inc(v_snd_2355_);
v_fst_2356_ = lean_ctor_get(v_a_2354_, 0);
lean_inc(v_fst_2356_);
lean_dec(v_a_2354_);
v_snd_2357_ = lean_ctor_get(v_snd_2355_, 1);
v_isSharedCheck_2375_ = !lean_is_exclusive(v_snd_2355_);
if (v_isSharedCheck_2375_ == 0)
{
lean_object* v_unused_2376_; 
v_unused_2376_ = lean_ctor_get(v_snd_2355_, 0);
lean_dec(v_unused_2376_);
v___x_2359_ = v_snd_2355_;
v_isShared_2360_ = v_isSharedCheck_2375_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_snd_2357_);
lean_dec(v_snd_2355_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2375_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; uint8_t v___x_2363_; 
v___x_2361_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2314_);
v___x_2362_ = l_Lean_Name_append(v___x_2361_, v___y_2314_);
v___x_2363_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2307_, v___y_2306_, v___x_2362_);
lean_dec(v___x_2362_);
if (v___x_2363_ == 0)
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
lean_del_object(v___x_2359_);
v___x_2364_ = lean_box(0);
v___x_2365_ = l_Lean_Meta_rwMatcher___lam__3(v___y_2304_, v___y_2303_, v_fst_2356_, v___y_2301_, v_e_2104_, v___y_2302_, v_snd_2357_, v___x_2364_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
lean_dec(v_snd_2357_);
v___y_2218_ = v___y_2300_;
v___y_2219_ = v___y_2305_;
v___y_2220_ = v___y_2306_;
v___y_2221_ = v___y_2308_;
v___y_2222_ = v___x_2349_;
v___y_2223_ = v___y_2310_;
v___y_2224_ = v___y_2311_;
v___y_2225_ = v___y_2312_;
v___y_2226_ = v___y_2313_;
v___y_2227_ = v_a_2316_;
v___y_2228_ = v___y_2314_;
v___y_2229_ = v___x_2365_;
goto v___jp_2217_;
}
else
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2366_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2357_);
v___x_2367_ = l_Lean_indentExpr(v_snd_2357_);
if (v_isShared_2360_ == 0)
{
lean_ctor_set_tag(v___x_2359_, 7);
lean_ctor_set(v___x_2359_, 1, v___x_2367_);
lean_ctor_set(v___x_2359_, 0, v___x_2366_);
v___x_2369_ = v___x_2359_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2366_);
lean_ctor_set(v_reuseFailAlloc_2374_, 1, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2370_; 
lean_inc(v___y_2314_);
v___x_2370_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2314_, v___x_2369_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v___x_2372_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_a_2371_);
lean_dec_ref_known(v___x_2370_, 1);
v___x_2372_ = l_Lean_Meta_rwMatcher___lam__3(v___y_2304_, v___y_2303_, v_fst_2356_, v___y_2301_, v_e_2104_, v___y_2302_, v_snd_2357_, v_a_2371_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
lean_dec(v_snd_2357_);
v___y_2218_ = v___y_2300_;
v___y_2219_ = v___y_2305_;
v___y_2220_ = v___y_2306_;
v___y_2221_ = v___y_2308_;
v___y_2222_ = v___x_2349_;
v___y_2223_ = v___y_2310_;
v___y_2224_ = v___y_2311_;
v___y_2225_ = v___y_2312_;
v___y_2226_ = v___y_2313_;
v___y_2227_ = v_a_2316_;
v___y_2228_ = v___y_2314_;
v___y_2229_ = v___x_2372_;
goto v___jp_2217_;
}
else
{
lean_object* v_a_2373_; 
lean_dec(v_snd_2357_);
lean_dec(v_fst_2356_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2301_);
lean_dec_ref(v_e_2104_);
v_a_2373_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_a_2373_);
lean_dec_ref_known(v___x_2370_, 1);
v___y_2204_ = v___y_2300_;
v___y_2205_ = v___y_2305_;
v___y_2206_ = v___y_2306_;
v___y_2207_ = v___y_2308_;
v___y_2208_ = v___x_2349_;
v___y_2209_ = v___y_2310_;
v___y_2210_ = v___y_2311_;
v___y_2211_ = v___y_2312_;
v___y_2212_ = v___y_2313_;
v___y_2213_ = v_a_2316_;
v___y_2214_ = v___y_2314_;
v_a_2215_ = v_a_2373_;
goto v___jp_2203_;
}
}
}
}
}
else
{
lean_object* v_a_2377_; 
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2301_);
lean_dec_ref(v_e_2104_);
v_a_2377_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2377_);
lean_dec_ref_known(v___x_2353_, 1);
v___y_2204_ = v___y_2300_;
v___y_2205_ = v___y_2305_;
v___y_2206_ = v___y_2306_;
v___y_2207_ = v___y_2308_;
v___y_2208_ = v___x_2349_;
v___y_2209_ = v___y_2310_;
v___y_2210_ = v___y_2311_;
v___y_2211_ = v___y_2312_;
v___y_2212_ = v___y_2313_;
v___y_2213_ = v_a_2316_;
v___y_2214_ = v___y_2314_;
v_a_2215_ = v_a_2377_;
goto v___jp_2203_;
}
}
else
{
lean_object* v_a_2378_; 
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2301_);
lean_dec_ref(v_e_2104_);
v_a_2378_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2378_);
lean_dec_ref_known(v___x_2350_, 1);
v___y_2204_ = v___y_2300_;
v___y_2205_ = v___y_2305_;
v___y_2206_ = v___y_2306_;
v___y_2207_ = v___y_2308_;
v___y_2208_ = v___x_2349_;
v___y_2209_ = v___y_2310_;
v___y_2210_ = v___y_2311_;
v___y_2211_ = v___y_2312_;
v___y_2212_ = v___y_2313_;
v___y_2213_ = v_a_2316_;
v___y_2214_ = v___y_2314_;
v_a_2215_ = v_a_2378_;
goto v___jp_2203_;
}
}
}
v___jp_2379_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2381_ = lean_box(0);
v___x_2382_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2382_, 0, v_e_2104_);
lean_ctor_set(v___x_2382_, 1, v___x_2381_);
lean_ctor_set_uint8(v___x_2382_, sizeof(void*)*2, v___y_2380_);
v___x_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
return v___x_2383_;
}
v___jp_2384_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2386_ = lean_box(0);
v___x_2387_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2387_, 0, v_e_2104_);
lean_ctor_set(v___x_2387_, 1, v___x_2386_);
lean_ctor_set_uint8(v___x_2387_, sizeof(void*)*2, v___y_2385_);
v___x_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
return v___x_2388_;
}
v___jp_2389_:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2393_, 0, v_proof_2392_);
v___x_2394_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2394_, 0, v___y_2390_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
lean_ctor_set_uint8(v___x_2394_, sizeof(void*)*2, v___y_2391_);
v___x_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2394_);
return v___x_2395_;
}
v___jp_2396_:
{
if (lean_obj_tag(v___y_2403_) == 0)
{
lean_object* v_a_2404_; 
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2397_);
v_a_2404_ = lean_ctor_get(v___y_2403_, 0);
lean_inc(v_a_2404_);
lean_dec_ref_known(v___y_2403_, 1);
v___y_2390_ = v___y_2398_;
v___y_2391_ = v___y_2401_;
v_proof_2392_ = v_a_2404_;
goto v___jp_2389_;
}
else
{
lean_object* v_a_2405_; 
lean_dec_ref(v___y_2398_);
v_a_2405_ = lean_ctor_get(v___y_2403_, 0);
lean_inc(v_a_2405_);
lean_dec_ref_known(v___y_2403_, 1);
v___y_2168_ = v___y_2397_;
v___y_2169_ = v___y_2399_;
v___y_2170_ = v___y_2400_;
v___y_2171_ = v___y_2402_;
v_a_2172_ = v_a_2405_;
goto v___jp_2167_;
}
}
v___jp_2406_:
{
if (v___y_2420_ == 0)
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
lean_dec_ref(v___y_2416_);
v___x_2421_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_2422_ = l_Lean_MessageData_ofExpr(v___y_2417_);
v___x_2423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2421_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_2425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2423_);
lean_ctor_set(v___x_2425_, 1, v___x_2424_);
v___x_2426_ = l_Lean_Exception_toMessageData(v___y_2407_);
v___x_2427_ = l_Lean_indentD(v___x_2426_);
v___x_2428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2425_);
lean_ctor_set(v___x_2428_, 1, v___x_2427_);
v___x_2429_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_2430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2428_);
lean_ctor_set(v___x_2430_, 1, v___x_2429_);
v___x_2431_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2430_, v___y_2419_, v___y_2415_, v___y_2413_, v___y_2409_);
v___y_2397_ = v___y_2408_;
v___y_2398_ = v___y_2414_;
v___y_2399_ = v___y_2410_;
v___y_2400_ = v___y_2418_;
v___y_2401_ = v___y_2411_;
v___y_2402_ = v___y_2412_;
v___y_2403_ = v___x_2431_;
goto v___jp_2396_;
}
else
{
lean_dec_ref(v___y_2417_);
lean_dec_ref(v___y_2407_);
v___y_2397_ = v___y_2408_;
v___y_2398_ = v___y_2414_;
v___y_2399_ = v___y_2410_;
v___y_2400_ = v___y_2418_;
v___y_2401_ = v___y_2411_;
v___y_2402_ = v___y_2412_;
v___y_2403_ = v___y_2416_;
goto v___jp_2396_;
}
}
v___jp_2432_:
{
lean_object* v___x_2445_; lean_object* v_a_2446_; lean_object* v___x_2447_; 
v___x_2445_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_2433_, v___y_2442_);
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_a_2446_);
lean_dec_ref(v___x_2445_);
v___x_2447_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_2436_, v___y_2442_);
if (v___y_2435_ == 0)
{
lean_object* v_a_2448_; 
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2434_);
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
lean_inc(v_a_2448_);
lean_dec_ref(v___x_2447_);
v___y_2390_ = v_a_2446_;
v___y_2391_ = v___y_2439_;
v_proof_2392_ = v_a_2448_;
goto v___jp_2389_;
}
else
{
lean_object* v_a_2449_; lean_object* v___x_2450_; 
v_a_2449_ = lean_ctor_get(v___x_2447_, 0);
lean_inc_n(v_a_2449_, 2);
lean_dec_ref(v___x_2447_);
v___x_2450_ = l_Lean_Meta_mkEqOfHEq(v_a_2449_, v___y_2439_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_dec(v_a_2449_);
v___y_2397_ = v___y_2434_;
v___y_2398_ = v_a_2446_;
v___y_2399_ = v___y_2437_;
v___y_2400_ = v___y_2438_;
v___y_2401_ = v___y_2439_;
v___y_2402_ = v___y_2440_;
v___y_2403_ = v___x_2450_;
goto v___jp_2396_;
}
else
{
lean_object* v_a_2451_; uint8_t v___x_2452_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_a_2451_);
v___x_2452_ = l_Lean_Exception_isInterrupt(v_a_2451_);
if (v___x_2452_ == 0)
{
uint8_t v___x_2453_; 
lean_inc(v_a_2451_);
v___x_2453_ = l_Lean_Exception_isRuntime(v_a_2451_);
v___y_2407_ = v_a_2451_;
v___y_2408_ = v___y_2434_;
v___y_2409_ = v___y_2444_;
v___y_2410_ = v___y_2437_;
v___y_2411_ = v___y_2439_;
v___y_2412_ = v___y_2440_;
v___y_2413_ = v___y_2443_;
v___y_2414_ = v_a_2446_;
v___y_2415_ = v___y_2442_;
v___y_2416_ = v___x_2450_;
v___y_2417_ = v_a_2449_;
v___y_2418_ = v___y_2438_;
v___y_2419_ = v___y_2441_;
v___y_2420_ = v___x_2453_;
goto v___jp_2406_;
}
else
{
v___y_2407_ = v_a_2451_;
v___y_2408_ = v___y_2434_;
v___y_2409_ = v___y_2444_;
v___y_2410_ = v___y_2437_;
v___y_2411_ = v___y_2439_;
v___y_2412_ = v___y_2440_;
v___y_2413_ = v___y_2443_;
v___y_2414_ = v_a_2446_;
v___y_2415_ = v___y_2442_;
v___y_2416_ = v___x_2450_;
v___y_2417_ = v_a_2449_;
v___y_2418_ = v___y_2438_;
v___y_2419_ = v___y_2441_;
v___y_2420_ = v___x_2452_;
goto v___jp_2406_;
}
}
}
}
v___jp_2454_:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; uint8_t v___x_2470_; 
v___x_2468_ = lean_array_get_size(v_a_2467_);
v___x_2469_ = lean_unsigned_to_nat(0u);
v___x_2470_ = lean_nat_dec_eq(v___x_2468_, v___x_2469_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v_a_2482_; 
lean_dec_ref(v___y_2459_);
lean_dec_ref(v___y_2455_);
v___x_2471_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
lean_inc(v___y_2457_);
v___x_2472_ = l_Lean_MessageData_ofConstName(v___y_2457_, v___x_2470_);
v___x_2473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2471_);
lean_ctor_set(v___x_2473_, 1, v___x_2472_);
v___x_2474_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_2475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2473_);
lean_ctor_set(v___x_2475_, 1, v___x_2474_);
v___x_2476_ = lean_array_to_list(v_a_2467_);
v___x_2477_ = lean_box(0);
v___x_2478_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_2476_, v___x_2477_);
v___x_2479_ = l_Lean_MessageData_ofList(v___x_2478_);
v___x_2480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2475_);
lean_ctor_set(v___x_2480_, 1, v___x_2479_);
v___x_2481_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2480_, v___y_2456_, v___y_2461_, v___y_2460_, v___y_2465_);
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_a_2482_);
lean_dec_ref(v___x_2481_);
v___y_2168_ = v___y_2457_;
v___y_2169_ = v___y_2462_;
v___y_2170_ = v___y_2464_;
v___y_2171_ = v___y_2466_;
v_a_2172_ = v_a_2482_;
goto v___jp_2167_;
}
else
{
lean_dec_ref(v_a_2467_);
v___y_2433_ = v___y_2455_;
v___y_2434_ = v___y_2457_;
v___y_2435_ = v___y_2458_;
v___y_2436_ = v___y_2459_;
v___y_2437_ = v___y_2462_;
v___y_2438_ = v___y_2464_;
v___y_2439_ = v___y_2463_;
v___y_2440_ = v___y_2466_;
v___y_2441_ = v___y_2456_;
v___y_2442_ = v___y_2461_;
v___y_2443_ = v___y_2460_;
v___y_2444_ = v___y_2465_;
goto v___jp_2432_;
}
}
v___jp_2483_:
{
if (lean_obj_tag(v___y_2496_) == 0)
{
lean_object* v_a_2497_; 
v_a_2497_ = lean_ctor_get(v___y_2496_, 0);
lean_inc(v_a_2497_);
lean_dec_ref_known(v___y_2496_, 1);
v___y_2455_ = v___y_2484_;
v___y_2456_ = v___y_2486_;
v___y_2457_ = v___y_2485_;
v___y_2458_ = v___y_2487_;
v___y_2459_ = v___y_2488_;
v___y_2460_ = v___y_2490_;
v___y_2461_ = v___y_2489_;
v___y_2462_ = v___y_2491_;
v___y_2463_ = v___y_2493_;
v___y_2464_ = v___y_2492_;
v___y_2465_ = v___y_2494_;
v___y_2466_ = v___y_2495_;
v_a_2467_ = v_a_2497_;
goto v___jp_2454_;
}
else
{
lean_object* v_a_2498_; 
lean_dec_ref(v___y_2488_);
lean_dec_ref(v___y_2484_);
v_a_2498_ = lean_ctor_get(v___y_2496_, 0);
lean_inc(v_a_2498_);
lean_dec_ref_known(v___y_2496_, 1);
v___y_2168_ = v___y_2485_;
v___y_2169_ = v___y_2491_;
v___y_2170_ = v___y_2492_;
v___y_2171_ = v___y_2495_;
v_a_2172_ = v_a_2498_;
goto v___jp_2167_;
}
}
v___jp_2499_:
{
lean_object* v___x_2514_; size_t v_sz_2515_; lean_object* v___x_2516_; 
v___x_2514_ = lean_box(0);
v_sz_2515_ = lean_array_size(v___y_2503_);
v___x_2516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___y_2503_, v_sz_2515_, v___y_2502_, v___x_2514_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; uint8_t v___x_2520_; 
lean_dec_ref_known(v___x_2516_, 1);
v___x_2517_ = lean_unsigned_to_nat(0u);
v___x_2518_ = lean_array_get_size(v___y_2503_);
v___x_2519_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_2520_ = lean_nat_dec_lt(v___x_2517_, v___x_2518_);
if (v___x_2520_ == 0)
{
lean_dec_ref(v___y_2503_);
v___y_2455_ = v___y_2500_;
v___y_2456_ = v___y_2510_;
v___y_2457_ = v___y_2501_;
v___y_2458_ = v___y_2504_;
v___y_2459_ = v___y_2505_;
v___y_2460_ = v___y_2512_;
v___y_2461_ = v___y_2511_;
v___y_2462_ = v___y_2506_;
v___y_2463_ = v___y_2508_;
v___y_2464_ = v___y_2507_;
v___y_2465_ = v___y_2513_;
v___y_2466_ = v___y_2509_;
v_a_2467_ = v___x_2519_;
goto v___jp_2454_;
}
else
{
uint8_t v___x_2521_; 
v___x_2521_ = lean_nat_dec_le(v___x_2518_, v___x_2518_);
if (v___x_2521_ == 0)
{
if (v___x_2520_ == 0)
{
lean_dec_ref(v___y_2503_);
v___y_2455_ = v___y_2500_;
v___y_2456_ = v___y_2510_;
v___y_2457_ = v___y_2501_;
v___y_2458_ = v___y_2504_;
v___y_2459_ = v___y_2505_;
v___y_2460_ = v___y_2512_;
v___y_2461_ = v___y_2511_;
v___y_2462_ = v___y_2506_;
v___y_2463_ = v___y_2508_;
v___y_2464_ = v___y_2507_;
v___y_2465_ = v___y_2513_;
v___y_2466_ = v___y_2509_;
v_a_2467_ = v___x_2519_;
goto v___jp_2454_;
}
else
{
size_t v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = lean_usize_of_nat(v___x_2518_);
v___x_2523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___y_2503_, v___y_2502_, v___x_2522_, v___x_2519_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
lean_dec_ref(v___y_2503_);
v___y_2484_ = v___y_2500_;
v___y_2485_ = v___y_2501_;
v___y_2486_ = v___y_2510_;
v___y_2487_ = v___y_2504_;
v___y_2488_ = v___y_2505_;
v___y_2489_ = v___y_2511_;
v___y_2490_ = v___y_2512_;
v___y_2491_ = v___y_2506_;
v___y_2492_ = v___y_2507_;
v___y_2493_ = v___y_2508_;
v___y_2494_ = v___y_2513_;
v___y_2495_ = v___y_2509_;
v___y_2496_ = v___x_2523_;
goto v___jp_2483_;
}
}
else
{
size_t v___x_2524_; lean_object* v___x_2525_; 
v___x_2524_ = lean_usize_of_nat(v___x_2518_);
v___x_2525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___y_2503_, v___y_2502_, v___x_2524_, v___x_2519_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
lean_dec_ref(v___y_2503_);
v___y_2484_ = v___y_2500_;
v___y_2485_ = v___y_2501_;
v___y_2486_ = v___y_2510_;
v___y_2487_ = v___y_2504_;
v___y_2488_ = v___y_2505_;
v___y_2489_ = v___y_2511_;
v___y_2490_ = v___y_2512_;
v___y_2491_ = v___y_2506_;
v___y_2492_ = v___y_2507_;
v___y_2493_ = v___y_2508_;
v___y_2494_ = v___y_2513_;
v___y_2495_ = v___y_2509_;
v___y_2496_ = v___x_2525_;
goto v___jp_2483_;
}
}
}
else
{
lean_object* v_a_2526_; 
lean_dec_ref(v___y_2505_);
lean_dec_ref(v___y_2503_);
lean_dec_ref(v___y_2500_);
v_a_2526_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_a_2526_);
lean_dec_ref_known(v___x_2516_, 1);
v___y_2168_ = v___y_2501_;
v___y_2169_ = v___y_2506_;
v___y_2170_ = v___y_2507_;
v___y_2171_ = v___y_2509_;
v_a_2172_ = v_a_2526_;
goto v___jp_2167_;
}
}
v___jp_2527_:
{
lean_object* v___x_2543_; 
lean_inc_ref(v_fst_2537_);
lean_inc_ref(v_e_2104_);
v___x_2543_ = l_Lean_Meta_isExprDefEq(v_e_2104_, v_fst_2537_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; uint8_t v___x_2545_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2544_);
lean_dec_ref_known(v___x_2543_, 1);
v___x_2545_ = lean_unbox(v_a_2544_);
lean_dec(v_a_2544_);
if (v___x_2545_ == 0)
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v_a_2560_; 
lean_dec_ref(v_snd_2538_);
lean_dec_ref(v___y_2531_);
lean_dec_ref(v___y_2530_);
v___x_2546_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_2547_ = l_Lean_MessageData_ofExpr(v_fst_2537_);
v___x_2548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2546_);
lean_ctor_set(v___x_2548_, 1, v___x_2547_);
v___x_2549_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_2550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2548_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
lean_inc(v___y_2528_);
v___x_2551_ = l_Lean_MessageData_ofConstName(v___y_2528_, v___y_2532_);
v___x_2552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2550_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
v___x_2553_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_2554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2552_);
lean_ctor_set(v___x_2554_, 1, v___x_2553_);
v___x_2555_ = l_Lean_MessageData_ofExpr(v_e_2104_);
v___x_2556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2554_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
v___x_2557_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_2558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2556_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
v___x_2559_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2558_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_a_2560_);
lean_dec_ref(v___x_2559_);
v___y_2168_ = v___y_2528_;
v___y_2169_ = v___y_2532_;
v___y_2170_ = v___y_2534_;
v___y_2171_ = v___y_2535_;
v_a_2172_ = v_a_2560_;
goto v___jp_2167_;
}
else
{
lean_dec_ref(v_fst_2537_);
lean_dec_ref(v_e_2104_);
v___y_2500_ = v_snd_2538_;
v___y_2501_ = v___y_2528_;
v___y_2502_ = v___y_2529_;
v___y_2503_ = v___y_2530_;
v___y_2504_ = v_fst_2536_;
v___y_2505_ = v___y_2531_;
v___y_2506_ = v___y_2532_;
v___y_2507_ = v___y_2534_;
v___y_2508_ = v___y_2533_;
v___y_2509_ = v___y_2535_;
v___y_2510_ = v___y_2539_;
v___y_2511_ = v___y_2540_;
v___y_2512_ = v___y_2541_;
v___y_2513_ = v___y_2542_;
goto v___jp_2499_;
}
}
else
{
lean_object* v_a_2561_; 
lean_dec_ref(v_snd_2538_);
lean_dec_ref(v_fst_2537_);
lean_dec_ref(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec_ref(v_e_2104_);
v_a_2561_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2561_);
lean_dec_ref_known(v___x_2543_, 1);
v___y_2168_ = v___y_2528_;
v___y_2169_ = v___y_2532_;
v___y_2170_ = v___y_2534_;
v___y_2171_ = v___y_2535_;
v_a_2172_ = v_a_2561_;
goto v___jp_2167_;
}
}
v___jp_2563_:
{
uint8_t v___x_2565_; 
v___x_2565_ = 1;
if (v___y_2564_ == 0)
{
lean_object* v___x_2566_; lean_object* v___f_2567_; lean_object* v___x_2568_; lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2737_; 
v___x_2566_ = lean_box(v___x_2565_);
lean_inc_ref(v_e_2104_);
v___f_2567_ = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2567_, 0, v_e_2104_);
lean_closure_set(v___f_2567_, 1, v___x_2566_);
v___x_2568_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(v_e_2104_, v_a_2108_);
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2571_ = v___x_2568_;
v_isShared_2572_ = v_isSharedCheck_2737_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2568_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2737_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
uint8_t v___x_2573_; 
v___x_2573_ = lean_unbox(v_a_2569_);
lean_dec(v_a_2569_);
if (v___x_2573_ == 0)
{
lean_object* v_toCold_2574_; lean_object* v_options_2575_; uint8_t v_hasTrace_2576_; 
lean_del_object(v___x_2571_);
lean_dec_ref(v___f_2567_);
lean_dec(v_altIdx_2103_);
v_toCold_2574_ = lean_ctor_get(v_a_2107_, 0);
v_options_2575_ = lean_ctor_get(v_toCold_2574_, 2);
v_hasTrace_2576_ = lean_ctor_get_uint8(v_options_2575_, sizeof(void*)*1);
if (v_hasTrace_2576_ == 0)
{
v___y_2385_ = v___x_2565_;
goto v___jp_2384_;
}
else
{
lean_object* v_inheritedTraceOptions_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; uint8_t v___x_2580_; 
v_inheritedTraceOptions_2577_ = lean_ctor_get(v_toCold_2574_, 11);
v___x_2578_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2579_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2580_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2577_, v_options_2575_, v___x_2579_);
if (v___x_2580_ == 0)
{
v___y_2385_ = v___x_2565_;
goto v___jp_2384_;
}
else
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2581_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__15, &l_Lean_Meta_rwMatcher___closed__15_once, _init_l_Lean_Meta_rwMatcher___closed__15);
lean_inc_ref(v_e_2104_);
v___x_2582_ = l_Lean_indentExpr(v_e_2104_);
v___x_2583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2581_);
lean_ctor_set(v___x_2583_, 1, v___x_2582_);
v___x_2584_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2578_, v___x_2583_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_dec_ref_known(v___x_2584_, 1);
v___y_2385_ = v___x_2565_;
goto v___jp_2384_;
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
lean_dec_ref(v_e_2104_);
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2584_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2584_);
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
}
else
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2593_ = l_Lean_Expr_getAppFn(v_e_2104_);
v___x_2594_ = l_Lean_Expr_constName_x21(v___x_2593_);
lean_inc(v_a_2108_);
lean_inc_ref(v_a_2107_);
lean_inc(v_a_2106_);
lean_inc_ref(v_a_2105_);
lean_inc(v___x_2594_);
v___x_2595_ = lean_get_congr_match_equations_for(v___x_2594_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2597_; uint8_t v___x_2598_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2596_);
lean_dec_ref_known(v___x_2595_, 1);
v___x_2597_ = lean_array_get_size(v_a_2596_);
v___x_2598_ = lean_nat_dec_lt(v_altIdx_2103_, v___x_2597_);
if (v___x_2598_ == 0)
{
lean_object* v_toCold_2599_; lean_object* v_options_2600_; uint8_t v_hasTrace_2601_; 
lean_dec(v_a_2596_);
lean_dec_ref(v___x_2593_);
lean_dec_ref(v___f_2567_);
v_toCold_2599_ = lean_ctor_get(v_a_2107_, 0);
v_options_2600_ = lean_ctor_get(v_toCold_2599_, 2);
v_hasTrace_2601_ = lean_ctor_get_uint8(v_options_2600_, sizeof(void*)*1);
if (v_hasTrace_2601_ == 0)
{
lean_dec(v___x_2594_);
lean_del_object(v___x_2571_);
lean_dec(v_altIdx_2103_);
v___y_2380_ = v___x_2565_;
goto v___jp_2379_;
}
else
{
lean_object* v_inheritedTraceOptions_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; uint8_t v___x_2605_; 
v_inheritedTraceOptions_2602_ = lean_ctor_get(v_toCold_2599_, 11);
v___x_2603_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2604_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2605_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2602_, v_options_2600_, v___x_2604_);
if (v___x_2605_ == 0)
{
lean_dec(v___x_2594_);
lean_del_object(v___x_2571_);
lean_dec(v_altIdx_2103_);
v___y_2380_ = v___x_2565_;
goto v___jp_2379_;
}
else
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2609_; 
v___x_2606_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__17, &l_Lean_Meta_rwMatcher___closed__17_once, _init_l_Lean_Meta_rwMatcher___closed__17);
v___x_2607_ = l_Nat_reprFast(v_altIdx_2103_);
if (v_isShared_2572_ == 0)
{
lean_ctor_set_tag(v___x_2571_, 3);
lean_ctor_set(v___x_2571_, 0, v___x_2607_);
v___x_2609_ = v___x_2571_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2607_);
v___x_2609_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2610_ = l_Lean_MessageData_ofFormat(v___x_2609_);
v___x_2611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2606_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
v___x_2612_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__19, &l_Lean_Meta_rwMatcher___closed__19_once, _init_l_Lean_Meta_rwMatcher___closed__19);
v___x_2613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2611_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
v___x_2614_ = l_Nat_reprFast(v___x_2597_);
v___x_2615_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2614_);
v___x_2616_ = l_Lean_MessageData_ofFormat(v___x_2615_);
v___x_2617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2613_);
lean_ctor_set(v___x_2617_, 1, v___x_2616_);
v___x_2618_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__21, &l_Lean_Meta_rwMatcher___closed__21_once, _init_l_Lean_Meta_rwMatcher___closed__21);
v___x_2619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2617_);
lean_ctor_set(v___x_2619_, 1, v___x_2618_);
v___x_2620_ = l_Lean_MessageData_ofConstName(v___x_2594_, v___x_2598_);
v___x_2621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2619_);
lean_ctor_set(v___x_2621_, 1, v___x_2620_);
v___x_2622_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2603_, v___x_2621_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_dec_ref_known(v___x_2622_, 1);
v___y_2380_ = v___x_2565_;
goto v___jp_2379_;
}
else
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
lean_dec_ref(v_e_2104_);
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___x_2622_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2622_);
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
}
else
{
lean_object* v_toCold_2632_; lean_object* v_options_2633_; lean_object* v_inheritedTraceOptions_2634_; uint8_t v_hasTrace_2635_; lean_object* v_nargs_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v_dummy_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; 
lean_dec(v___x_2594_);
lean_del_object(v___x_2571_);
v_toCold_2632_ = lean_ctor_get(v_a_2107_, 0);
v_options_2633_ = lean_ctor_get(v_toCold_2632_, 2);
v_inheritedTraceOptions_2634_ = lean_ctor_get(v_toCold_2632_, 11);
v_hasTrace_2635_ = lean_ctor_get_uint8(v_options_2633_, sizeof(void*)*1);
v_nargs_2636_ = l_Lean_Expr_getAppNumArgs(v_e_2104_);
v___x_2637_ = lean_array_get(v___x_2562_, v_a_2596_, v_altIdx_2103_);
lean_dec(v_altIdx_2103_);
lean_dec(v_a_2596_);
v___x_2638_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2639_ = l_Lean_Expr_constLevels_x21(v___x_2593_);
lean_dec_ref(v___x_2593_);
lean_inc(v___x_2637_);
v___x_2640_ = l_Lean_mkConst(v___x_2637_, v___x_2639_);
v_dummy_2641_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__22, &l_Lean_Meta_rwMatcher___closed__22_once, _init_l_Lean_Meta_rwMatcher___closed__22);
lean_inc(v_nargs_2636_);
v___x_2642_ = lean_mk_array(v_nargs_2636_, v_dummy_2641_);
v___x_2643_ = lean_unsigned_to_nat(1u);
v___x_2644_ = lean_nat_sub(v_nargs_2636_, v___x_2643_);
lean_dec(v_nargs_2636_);
lean_inc_ref(v_e_2104_);
v___x_2645_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2104_, v___x_2642_, v___x_2644_);
v___x_2646_ = l_Lean_mkAppN(v___x_2640_, v___x_2645_);
lean_dec_ref(v___x_2645_);
if (v_hasTrace_2635_ == 0)
{
lean_object* v___x_2647_; 
lean_inc(v_a_2108_);
lean_inc_ref(v_a_2107_);
lean_inc(v_a_2106_);
lean_inc_ref(v_a_2105_);
lean_inc_ref(v___x_2646_);
v___x_2647_ = lean_infer_type(v___x_2646_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v_a_2648_; uint8_t v___x_2649_; lean_object* v___x_2650_; 
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_a_2648_);
lean_dec_ref_known(v___x_2647_, 1);
v___x_2649_ = 0;
v___x_2650_ = l_Lean_Meta_forallMetaTelescope(v_a_2648_, v___x_2649_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v_snd_2652_; lean_object* v_fst_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2691_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2651_);
lean_dec_ref_known(v___x_2650_, 1);
v_snd_2652_ = lean_ctor_get(v_a_2651_, 1);
v_fst_2653_ = lean_ctor_get(v_a_2651_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v_a_2651_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2655_ = v_a_2651_;
v_isShared_2656_ = v_isSharedCheck_2691_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_snd_2652_);
lean_inc(v_fst_2653_);
lean_dec(v_a_2651_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2691_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v_snd_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2689_; 
v_snd_2657_ = lean_ctor_get(v_snd_2652_, 1);
v_isSharedCheck_2689_ = !lean_is_exclusive(v_snd_2652_);
if (v_isSharedCheck_2689_ == 0)
{
lean_object* v_unused_2690_; 
v_unused_2690_ = lean_ctor_get(v_snd_2652_, 0);
lean_dec(v_unused_2690_);
v___x_2659_ = v_snd_2652_;
v_isShared_2660_ = v_isSharedCheck_2689_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_snd_2657_);
lean_dec(v_snd_2652_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2689_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2661_; size_t v_sz_2662_; size_t v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; uint8_t v___x_2667_; 
v___x_2661_ = l_Lean_mkAppN(v___x_2646_, v_fst_2653_);
v_sz_2662_ = lean_array_size(v_fst_2653_);
v___x_2663_ = ((size_t)0ULL);
v___x_2664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_2662_, v___x_2663_, v_fst_2653_);
v___x_2665_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_2666_ = lean_unsigned_to_nat(4u);
v___x_2667_ = l_Lean_Expr_isAppOfArity(v_snd_2657_, v___x_2665_, v___x_2666_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; lean_object* v___x_2669_; uint8_t v___x_2670_; 
v___x_2668_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_2669_ = lean_unsigned_to_nat(3u);
v___x_2670_ = l_Lean_Expr_isAppOfArity(v_snd_2657_, v___x_2668_, v___x_2669_);
if (v___x_2670_ == 0)
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2674_; 
lean_dec_ref(v___x_2664_);
lean_dec_ref(v___x_2661_);
lean_dec(v_snd_2657_);
lean_dec_ref(v_e_2104_);
v___x_2671_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
lean_inc(v___x_2637_);
v___x_2672_ = l_Lean_MessageData_ofConstName(v___x_2637_, v___y_2564_);
if (v_isShared_2660_ == 0)
{
lean_ctor_set_tag(v___x_2659_, 7);
lean_ctor_set(v___x_2659_, 1, v___x_2672_);
lean_ctor_set(v___x_2659_, 0, v___x_2671_);
v___x_2674_ = v___x_2659_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2671_);
lean_ctor_set(v_reuseFailAlloc_2681_, 1, v___x_2672_);
v___x_2674_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
lean_object* v___x_2675_; lean_object* v___x_2677_; 
v___x_2675_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
if (v_isShared_2656_ == 0)
{
lean_ctor_set_tag(v___x_2655_, 7);
lean_ctor_set(v___x_2655_, 1, v___x_2675_);
lean_ctor_set(v___x_2655_, 0, v___x_2674_);
v___x_2677_ = v___x_2655_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2674_);
lean_ctor_set(v_reuseFailAlloc_2680_, 1, v___x_2675_);
v___x_2677_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
lean_object* v___x_2678_; lean_object* v_a_2679_; 
v___x_2678_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2677_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref(v___x_2678_);
v___y_2168_ = v___x_2637_;
v___y_2169_ = v___y_2564_;
v___y_2170_ = v___f_2567_;
v___y_2171_ = v___x_2638_;
v_a_2172_ = v_a_2679_;
goto v___jp_2167_;
}
}
}
else
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
lean_del_object(v___x_2659_);
lean_del_object(v___x_2655_);
v___x_2682_ = l_Lean_Expr_appFn_x21(v_snd_2657_);
v___x_2683_ = l_Lean_Expr_appArg_x21(v___x_2682_);
lean_dec_ref(v___x_2682_);
v___x_2684_ = l_Lean_Expr_appArg_x21(v_snd_2657_);
lean_dec(v_snd_2657_);
v___y_2528_ = v___x_2637_;
v___y_2529_ = v___x_2663_;
v___y_2530_ = v___x_2664_;
v___y_2531_ = v___x_2661_;
v___y_2532_ = v___y_2564_;
v___y_2533_ = v___x_2565_;
v___y_2534_ = v___f_2567_;
v___y_2535_ = v___x_2638_;
v_fst_2536_ = v___y_2564_;
v_fst_2537_ = v___x_2683_;
v_snd_2538_ = v___x_2684_;
v___y_2539_ = v_a_2105_;
v___y_2540_ = v_a_2106_;
v___y_2541_ = v_a_2107_;
v___y_2542_ = v_a_2108_;
goto v___jp_2527_;
}
}
else
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
lean_del_object(v___x_2659_);
lean_del_object(v___x_2655_);
v___x_2685_ = l_Lean_Expr_appFn_x21(v_snd_2657_);
v___x_2686_ = l_Lean_Expr_appFn_x21(v___x_2685_);
lean_dec_ref(v___x_2685_);
v___x_2687_ = l_Lean_Expr_appArg_x21(v___x_2686_);
lean_dec_ref(v___x_2686_);
v___x_2688_ = l_Lean_Expr_appArg_x21(v_snd_2657_);
lean_dec(v_snd_2657_);
v___y_2528_ = v___x_2637_;
v___y_2529_ = v___x_2663_;
v___y_2530_ = v___x_2664_;
v___y_2531_ = v___x_2661_;
v___y_2532_ = v___y_2564_;
v___y_2533_ = v___x_2565_;
v___y_2534_ = v___f_2567_;
v___y_2535_ = v___x_2638_;
v_fst_2536_ = v___x_2565_;
v_fst_2537_ = v___x_2687_;
v_snd_2538_ = v___x_2688_;
v___y_2539_ = v_a_2105_;
v___y_2540_ = v_a_2106_;
v___y_2541_ = v_a_2107_;
v___y_2542_ = v_a_2108_;
goto v___jp_2527_;
}
}
}
}
else
{
lean_object* v_a_2692_; 
lean_dec_ref(v___x_2646_);
lean_dec_ref(v_e_2104_);
v_a_2692_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2692_);
lean_dec_ref_known(v___x_2650_, 1);
v___y_2168_ = v___x_2637_;
v___y_2169_ = v___y_2564_;
v___y_2170_ = v___f_2567_;
v___y_2171_ = v___x_2638_;
v_a_2172_ = v_a_2692_;
goto v___jp_2167_;
}
}
else
{
lean_object* v_a_2693_; 
lean_dec_ref(v___x_2646_);
lean_dec_ref(v_e_2104_);
v_a_2693_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_a_2693_);
lean_dec_ref_known(v___x_2647_, 1);
v___y_2168_ = v___x_2637_;
v___y_2169_ = v___y_2564_;
v___y_2170_ = v___f_2567_;
v___y_2171_ = v___x_2638_;
v_a_2172_ = v_a_2693_;
goto v___jp_2167_;
}
}
else
{
lean_object* v___x_2694_; lean_object* v___f_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; uint8_t v___x_2698_; 
v___x_2694_ = lean_box(v___y_2564_);
lean_inc_ref(v_e_2104_);
lean_inc(v___x_2637_);
v___f_2695_ = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__1___boxed), 9, 3);
lean_closure_set(v___f_2695_, 0, v___x_2637_);
lean_closure_set(v___f_2695_, 1, v___x_2694_);
lean_closure_set(v___f_2695_, 2, v_e_2104_);
v___x_2696_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1));
v___x_2697_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2698_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2634_, v_options_2633_, v___x_2697_);
if (v___x_2698_ == 0)
{
lean_object* v___x_2699_; uint8_t v___x_2700_; 
v___x_2699_ = l_Lean_trace_profiler;
v___x_2700_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_options_2633_, v___x_2699_);
if (v___x_2700_ == 0)
{
lean_object* v___x_2701_; 
lean_dec_ref(v___f_2695_);
lean_inc(v_a_2108_);
lean_inc_ref(v_a_2107_);
lean_inc(v_a_2106_);
lean_inc_ref(v_a_2105_);
lean_inc_ref(v___x_2646_);
v___x_2701_ = lean_infer_type(v___x_2646_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; uint8_t v___x_2703_; lean_object* v___x_2704_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2702_);
lean_dec_ref_known(v___x_2701_, 1);
v___x_2703_ = 0;
v___x_2704_ = l_Lean_Meta_forallMetaTelescope(v_a_2702_, v___x_2703_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v_a_2705_; lean_object* v_snd_2706_; 
v_a_2705_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_a_2705_);
lean_dec_ref_known(v___x_2704_, 1);
v_snd_2706_ = lean_ctor_get(v_a_2705_, 1);
lean_inc(v_snd_2706_);
if (v___x_2698_ == 0)
{
lean_object* v_fst_2707_; lean_object* v_snd_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v_fst_2707_ = lean_ctor_get(v_a_2705_, 0);
lean_inc(v_fst_2707_);
lean_dec(v_a_2705_);
v_snd_2708_ = lean_ctor_get(v_snd_2706_, 1);
lean_inc(v_snd_2708_);
lean_dec(v_snd_2706_);
v___x_2709_ = lean_box(0);
lean_inc(v___x_2637_);
v___x_2710_ = l_Lean_Meta_rwMatcher___lam__4(v___x_2565_, v___x_2646_, v_fst_2707_, v___x_2637_, v_e_2104_, v___y_2564_, v_snd_2708_, v___x_2709_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
lean_dec(v_snd_2708_);
v___y_2176_ = v___x_2637_;
v___y_2177_ = v___y_2564_;
v___y_2178_ = v___f_2567_;
v___y_2179_ = v___x_2638_;
v___y_2180_ = v___x_2710_;
goto v___jp_2175_;
}
else
{
lean_object* v_fst_2711_; lean_object* v_snd_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2725_; 
v_fst_2711_ = lean_ctor_get(v_a_2705_, 0);
lean_inc(v_fst_2711_);
lean_dec(v_a_2705_);
v_snd_2712_ = lean_ctor_get(v_snd_2706_, 1);
v_isSharedCheck_2725_ = !lean_is_exclusive(v_snd_2706_);
if (v_isSharedCheck_2725_ == 0)
{
lean_object* v_unused_2726_; 
v_unused_2726_ = lean_ctor_get(v_snd_2706_, 0);
lean_dec(v_unused_2726_);
v___x_2714_ = v_snd_2706_;
v_isShared_2715_ = v_isSharedCheck_2725_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_snd_2712_);
lean_dec(v_snd_2706_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2725_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2719_; 
v___x_2716_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2712_);
v___x_2717_ = l_Lean_indentExpr(v_snd_2712_);
if (v_isShared_2715_ == 0)
{
lean_ctor_set_tag(v___x_2714_, 7);
lean_ctor_set(v___x_2714_, 1, v___x_2717_);
lean_ctor_set(v___x_2714_, 0, v___x_2716_);
v___x_2719_ = v___x_2714_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2716_);
lean_ctor_set(v_reuseFailAlloc_2724_, 1, v___x_2717_);
v___x_2719_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
lean_object* v___x_2720_; 
v___x_2720_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2638_, v___x_2719_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v_a_2721_; lean_object* v___x_2722_; 
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2721_);
lean_dec_ref_known(v___x_2720_, 1);
lean_inc(v___x_2637_);
v___x_2722_ = l_Lean_Meta_rwMatcher___lam__4(v___x_2565_, v___x_2646_, v_fst_2711_, v___x_2637_, v_e_2104_, v___y_2564_, v_snd_2712_, v_a_2721_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
lean_dec(v_snd_2712_);
v___y_2176_ = v___x_2637_;
v___y_2177_ = v___y_2564_;
v___y_2178_ = v___f_2567_;
v___y_2179_ = v___x_2638_;
v___y_2180_ = v___x_2722_;
goto v___jp_2175_;
}
else
{
lean_object* v_a_2723_; 
lean_dec(v_snd_2712_);
lean_dec(v_fst_2711_);
lean_dec_ref(v___x_2646_);
lean_dec_ref(v_e_2104_);
v_a_2723_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2723_);
lean_dec_ref_known(v___x_2720_, 1);
v___y_2168_ = v___x_2637_;
v___y_2169_ = v___y_2564_;
v___y_2170_ = v___f_2567_;
v___y_2171_ = v___x_2638_;
v_a_2172_ = v_a_2723_;
goto v___jp_2167_;
}
}
}
}
}
else
{
lean_object* v_a_2727_; 
lean_dec_ref(v___x_2646_);
lean_dec_ref(v_e_2104_);
v_a_2727_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_a_2727_);
lean_dec_ref_known(v___x_2704_, 1);
v___y_2168_ = v___x_2637_;
v___y_2169_ = v___y_2564_;
v___y_2170_ = v___f_2567_;
v___y_2171_ = v___x_2638_;
v_a_2172_ = v_a_2727_;
goto v___jp_2167_;
}
}
else
{
lean_object* v_a_2728_; 
lean_dec_ref(v___x_2646_);
lean_dec_ref(v_e_2104_);
v_a_2728_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2728_);
lean_dec_ref_known(v___x_2701_, 1);
v___y_2168_ = v___x_2637_;
v___y_2169_ = v___y_2564_;
v___y_2170_ = v___f_2567_;
v___y_2171_ = v___x_2638_;
v_a_2172_ = v_a_2728_;
goto v___jp_2167_;
}
}
else
{
lean_inc_ref(v___x_2646_);
lean_inc(v___x_2637_);
v___y_2300_ = v___f_2695_;
v___y_2301_ = v___x_2637_;
v___y_2302_ = v___y_2564_;
v___y_2303_ = v___x_2646_;
v___y_2304_ = v___x_2565_;
v___y_2305_ = v___x_2637_;
v___y_2306_ = v_options_2633_;
v___y_2307_ = v_inheritedTraceOptions_2634_;
v___y_2308_ = v___x_2696_;
v___y_2309_ = v___x_2646_;
v___y_2310_ = v___y_2564_;
v___y_2311_ = v___x_2565_;
v___y_2312_ = v___x_2698_;
v___y_2313_ = v___f_2567_;
v___y_2314_ = v___x_2638_;
goto v___jp_2299_;
}
}
else
{
lean_inc_ref(v___x_2646_);
lean_inc(v___x_2637_);
v___y_2300_ = v___f_2695_;
v___y_2301_ = v___x_2637_;
v___y_2302_ = v___y_2564_;
v___y_2303_ = v___x_2646_;
v___y_2304_ = v___x_2565_;
v___y_2305_ = v___x_2637_;
v___y_2306_ = v_options_2633_;
v___y_2307_ = v_inheritedTraceOptions_2634_;
v___y_2308_ = v___x_2696_;
v___y_2309_ = v___x_2646_;
v___y_2310_ = v___y_2564_;
v___y_2311_ = v___x_2565_;
v___y_2312_ = v___x_2698_;
v___y_2313_ = v___f_2567_;
v___y_2314_ = v___x_2638_;
goto v___jp_2299_;
}
}
}
}
else
{
lean_object* v_a_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2736_; 
lean_dec(v___x_2594_);
lean_dec_ref(v___x_2593_);
lean_del_object(v___x_2571_);
lean_dec_ref(v___f_2567_);
lean_dec_ref(v_e_2104_);
lean_dec(v_altIdx_2103_);
v_a_2729_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2731_ = v___x_2595_;
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_a_2729_);
lean_dec(v___x_2595_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2734_; 
if (v_isShared_2732_ == 0)
{
v___x_2734_ = v___x_2731_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_a_2729_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
}
}
}
else
{
lean_object* v___x_2738_; 
lean_dec(v_altIdx_2103_);
v___x_2738_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(v_e_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2748_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2741_ = v___x_2738_;
v_isShared_2742_ = v_isSharedCheck_2748_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2738_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2748_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2746_; 
v___x_2743_ = lean_box(0);
v___x_2744_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2744_, 0, v_a_2739_);
lean_ctor_set(v___x_2744_, 1, v___x_2743_);
lean_ctor_set_uint8(v___x_2744_, sizeof(void*)*2, v___x_2565_);
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 0, v___x_2744_);
v___x_2746_ = v___x_2741_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v___x_2744_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
else
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2756_; 
v_a_2749_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2751_ = v___x_2738_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2738_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2754_; 
if (v_isShared_2752_ == 0)
{
v___x_2754_ = v___x_2751_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_rwMatcher_0interp(lean_interpreter_value* stack)
{
lean_object* v_altIdx_2103_ = stack[0].m_obj;
lean_object* v_e_2104_ = stack[1].m_obj;
lean_object* v_a_2105_ = stack[2].m_obj;
lean_object* v_a_2106_ = stack[3].m_obj;
lean_object* v_a_2107_ = stack[4].m_obj;
lean_object* v_a_2108_ = stack[5].m_obj;
lean_object* v_res_2761_;
v_res_2761_ = l_Lean_Meta_rwMatcher(v_altIdx_2103_, v_e_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
stack->m_obj
 = v_res_2761_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___boxed(lean_object* v_altIdx_2762_, lean_object* v_e_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l_Lean_Meta_rwMatcher(v_altIdx_2762_, v_e_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
lean_dec(v_a_2765_);
lean_dec_ref(v_a_2764_);
return v_res_2769_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(lean_object* v_mvarId_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_mvarId_2770_, v___y_2772_);
return v___x_2776_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2770_ = stack[0].m_obj;
lean_object* v___y_2771_ = stack[1].m_obj;
lean_object* v___y_2772_ = stack[2].m_obj;
lean_object* v___y_2773_ = stack[3].m_obj;
lean_object* v___y_2774_ = stack[4].m_obj;
lean_object* v_res_2777_;
v_res_2777_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(v_mvarId_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
stack->m_obj
 = v_res_2777_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___boxed(lean_object* v_mvarId_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(v_mvarId_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v_mvarId_2778_);
return v_res_2784_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5(lean_object* v_00_u03b1_2785_, lean_object* v_msg_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v___x_2792_; 
v___x_2792_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v_msg_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
return v___x_2792_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2786_ = stack[1].m_obj;
lean_object* v___y_2787_ = stack[2].m_obj;
lean_object* v___y_2788_ = stack[3].m_obj;
lean_object* v___y_2789_ = stack[4].m_obj;
lean_object* v___y_2790_ = stack[5].m_obj;
lean_object* v_res_2793_;
v_res_2793_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5(lean_box(0), v_msg_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
stack->m_obj
 = v_res_2793_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___boxed(lean_object* v_00_u03b1_2794_, lean_object* v_msg_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5(v_00_u03b1_2794_, v_msg_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
return v_res_2801_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14(lean_object* v_00_u03b1_2802_, lean_object* v_x_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v___x_2809_; 
v___x_2809_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(v_x_2803_);
return v___x_2809_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2803_ = stack[1].m_obj;
lean_object* v___y_2804_ = stack[2].m_obj;
lean_object* v___y_2805_ = stack[3].m_obj;
lean_object* v___y_2806_ = stack[4].m_obj;
lean_object* v___y_2807_ = stack[5].m_obj;
lean_object* v_res_2810_;
v_res_2810_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14(lean_box(0), v_x_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
stack->m_obj
 = v_res_2810_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___boxed(lean_object* v_00_u03b1_2811_, lean_object* v_x_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14(v_00_u03b1_2811_, v_x_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
return v_res_2818_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12(lean_object* v_inst_2819_, lean_object* v_a_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v___x_2826_; 
v___x_2826_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(v_a_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
return v___x_2826_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2820_ = stack[1].m_obj;
lean_object* v___y_2821_ = stack[2].m_obj;
lean_object* v___y_2822_ = stack[3].m_obj;
lean_object* v___y_2823_ = stack[4].m_obj;
lean_object* v___y_2824_ = stack[5].m_obj;
lean_object* v_res_2827_;
v_res_2827_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12(lean_box(0), v_a_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
stack->m_obj
 = v_res_2827_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___boxed(lean_object* v_inst_2828_, lean_object* v_a_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12(v_inst_2828_, v_a_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
return v_res_2835_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(lean_object* v_00_u03b2_2836_, lean_object* v_x_2837_, lean_object* v_x_2838_){
_start:
{
uint8_t v___x_2839_; 
v___x_2839_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_x_2837_, v_x_2838_);
return v___x_2839_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2837_ = stack[1].m_obj;
lean_object* v_x_2838_ = stack[2].m_obj;
uint8_t v_res_2840_;
v_res_2840_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(lean_box(0), v_x_2837_, v_x_2838_);
stack->m_num = v_res_2840_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2841_, lean_object* v_x_2842_, lean_object* v_x_2843_){
_start:
{
uint8_t v_res_2844_; lean_object* v_r_2845_; 
v_res_2844_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(v_00_u03b2_2841_, v_x_2842_, v_x_2843_);
lean_dec(v_x_2843_);
lean_dec_ref(v_x_2842_);
v_r_2845_ = lean_box(v_res_2844_);
return v_r_2845_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5(lean_object* v_00_u03b2_2846_, lean_object* v_x_2847_, size_t v_x_2848_, lean_object* v_x_2849_){
_start:
{
uint8_t v___x_2850_; 
v___x_2850_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_2847_, v_x_2848_, v_x_2849_);
return v___x_2850_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2847_ = stack[1].m_obj;
size_t v_x_2848_ = stack[2].m_num;
lean_object* v_x_2849_ = stack[3].m_obj;
uint8_t v_res_2851_;
v_res_2851_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5(lean_box(0), v_x_2847_, v_x_2848_, v_x_2849_);
stack->m_num = v_res_2851_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b2_2852_, lean_object* v_x_2853_, lean_object* v_x_2854_, lean_object* v_x_2855_){
_start:
{
size_t v_x_90522__boxed_2856_; uint8_t v_res_2857_; lean_object* v_r_2858_; 
v_x_90522__boxed_2856_ = lean_unbox_usize(v_x_2854_);
lean_dec(v_x_2854_);
v_res_2857_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5(v_00_u03b2_2852_, v_x_2853_, v_x_90522__boxed_2856_, v_x_2855_);
lean_dec(v_x_2855_);
lean_dec_ref(v_x_2853_);
v_r_2858_ = lean_box(v_res_2857_);
return v_r_2858_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18(lean_object* v_00_u03b2_2859_, lean_object* v_keys_2860_, lean_object* v_vals_2861_, lean_object* v_heq_2862_, lean_object* v_i_2863_, lean_object* v_k_2864_){
_start:
{
uint8_t v___x_2865_; 
v___x_2865_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(v_keys_2860_, v_i_2863_, v_k_2864_);
return v___x_2865_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2860_ = stack[1].m_obj;
lean_object* v_vals_2861_ = stack[2].m_obj;
lean_object* v_i_2863_ = stack[4].m_obj;
lean_object* v_k_2864_ = stack[5].m_obj;
uint8_t v_res_2866_;
v_res_2866_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18(lean_box(0), v_keys_2860_, v_vals_2861_, lean_box(0), v_i_2863_, v_k_2864_);
stack->m_num = v_res_2866_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___boxed(lean_object* v_00_u03b2_2867_, lean_object* v_keys_2868_, lean_object* v_vals_2869_, lean_object* v_heq_2870_, lean_object* v_i_2871_, lean_object* v_k_2872_){
_start:
{
uint8_t v_res_2873_; lean_object* v_r_2874_; 
v_res_2873_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18(v_00_u03b2_2867_, v_keys_2868_, v_vals_2869_, v_heq_2870_, v_i_2871_, v_k_2872_);
lean_dec(v_k_2872_);
lean_dec_ref(v_vals_2869_);
lean_dec_ref(v_keys_2868_);
v_r_2874_ = lean_box(v_res_2873_);
return v_r_2874_;
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
