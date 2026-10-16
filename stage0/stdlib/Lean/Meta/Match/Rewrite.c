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
uint8_t v___x_85215__boxed_538_; lean_object* v_res_539_; 
v___x_85215__boxed_538_ = lean_unbox(v___x_531_);
v_res_539_ = l_Lean_Meta_rwMatcher___lam__0(v_e_530_, v___x_85215__boxed_538_, v_____r_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
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
uint8_t v___x_85257__boxed_572_; lean_object* v_res_573_; 
v___x_85257__boxed_572_ = lean_unbox(v___x_564_);
v_res_573_ = l_Lean_Meta_rwMatcher___lam__1(v___x_563_, v___x_85257__boxed_572_, v_e_565_, v_x_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
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
size_t v_x_85378__boxed_660_; uint8_t v_res_661_; lean_object* v_r_662_; 
v_x_85378__boxed_660_ = lean_unbox_usize(v_x_658_);
lean_dec(v_x_658_);
v_res_661_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6___redArg(v_x_657_, v_x_85378__boxed_660_, v_x_659_);
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
lean_inc_n(v_a_716_, 2);
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
lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_745_; 
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_745_ == 0)
{
lean_object* v_unused_746_; 
v_unused_746_ = lean_ctor_get(v___x_733_, 0);
lean_dec(v_unused_746_);
v___x_735_ = v___x_733_;
v_isShared_736_ = v_isSharedCheck_745_;
goto v_resetjp_734_;
}
else
{
lean_dec(v___x_733_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_745_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_737_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1);
lean_inc(v_a_711_);
if (v_isShared_736_ == 0)
{
lean_ctor_set_tag(v___x_735_, 1);
lean_ctor_set(v___x_735_, 0, v_a_711_);
v___x_739_ = v___x_735_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_711_);
v___x_739_ = v_reuseFailAlloc_744_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_737_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
v___x_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_742_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_dec_ref_known(v___x_743_, 1);
v_a_704_ = v___x_710_;
goto v___jp_703_;
}
else
{
return v___x_743_;
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
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
v_a_747_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_727_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_727_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
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
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
v_a_755_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_720_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_720_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
}
else
{
lean_object* v___x_763_; 
lean_dec(v_a_716_);
v___x_763_ = l_Lean_Meta_saveState___redArg(v___y_699_, v___y_701_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___x_765_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
lean_inc(v_a_711_);
v___x_765_ = l_Lean_MVarId_assumption(v_a_711_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_dec_ref_known(v___x_765_, 1);
lean_dec(v_a_764_);
v_a_704_ = v___x_710_;
goto v___jp_703_;
}
else
{
lean_object* v_a_766_; uint8_t v___x_767_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
v___x_767_ = l_Lean_Exception_isInterrupt(v_a_766_);
if (v___x_767_ == 0)
{
uint8_t v___x_768_; 
lean_inc(v_a_766_);
v___x_768_ = l_Lean_Exception_isRuntime(v_a_766_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; 
lean_dec_ref_known(v___x_765_, 1);
v___x_769_ = l_Lean_Meta_SavedState_restore___redArg(v_a_764_, v___y_699_, v___y_701_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v___x_770_; 
lean_dec_ref_known(v___x_769_, 1);
v___x_770_ = l_Lean_Meta_saveState___redArg(v___y_699_, v___y_701_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_772_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref_known(v___x_770_, 1);
lean_inc(v_a_711_);
v___x_772_ = l_Lean_MVarId_refl(v_a_711_, v___x_708_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_dec_ref_known(v___x_772_, 1);
lean_dec(v_a_771_);
v_a_704_ = v___x_710_;
goto v___jp_703_;
}
else
{
lean_object* v_a_773_; uint8_t v___x_774_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
v___x_774_ = l_Lean_Exception_isInterrupt(v_a_773_);
if (v___x_774_ == 0)
{
uint8_t v___x_775_; 
lean_inc(v_a_773_);
v___x_775_ = l_Lean_Exception_isRuntime(v_a_773_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; 
lean_dec_ref_known(v___x_772_, 1);
v___x_776_ = l_Lean_Meta_SavedState_restore___redArg(v_a_771_, v___y_699_, v___y_701_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_788_; 
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; 
v_unused_789_ = lean_ctor_get(v___x_776_, 0);
lean_dec(v_unused_789_);
v___x_778_ = v___x_776_;
v_isShared_779_ = v_isSharedCheck_788_;
goto v_resetjp_777_;
}
else
{
lean_dec(v___x_776_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_788_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v___x_782_; 
v___x_780_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__1);
lean_inc(v_a_711_);
if (v_isShared_779_ == 0)
{
lean_ctor_set_tag(v___x_778_, 1);
lean_ctor_set(v___x_778_, 0, v_a_711_);
v___x_782_ = v___x_778_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_711_);
v___x_782_ = v_reuseFailAlloc_787_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_780_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
v___x_785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_783_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_785_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_dec_ref_known(v___x_786_, 1);
v_a_704_ = v___x_710_;
goto v___jp_703_;
}
else
{
return v___x_786_;
}
}
}
}
else
{
return v___x_776_;
}
}
else
{
lean_dec(v_a_771_);
return v___x_772_;
}
}
else
{
lean_dec(v_a_771_);
return v___x_772_;
}
}
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
v_a_790_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_770_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_770_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
else
{
return v___x_769_;
}
}
else
{
lean_dec(v_a_764_);
return v___x_765_;
}
}
else
{
lean_dec(v_a_764_);
return v___x_765_;
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
v_a_798_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_763_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_763_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
else
{
lean_object* v___x_806_; 
lean_dec(v_a_716_);
v___x_806_ = l_Lean_Meta_saveState___redArg(v___y_699_, v___y_701_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v___x_808_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_807_);
lean_dec_ref_known(v___x_806_, 1);
lean_inc(v_a_711_);
v___x_808_ = l_Lean_MVarId_assumption(v_a_711_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_dec_ref_known(v___x_808_, 1);
lean_dec(v_a_807_);
v_a_704_ = v___x_710_;
goto v___jp_703_;
}
else
{
lean_object* v_a_809_; uint8_t v___x_810_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
v___x_810_ = l_Lean_Exception_isInterrupt(v_a_809_);
if (v___x_810_ == 0)
{
uint8_t v___x_811_; 
lean_inc(v_a_809_);
v___x_811_ = l_Lean_Exception_isRuntime(v_a_809_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; 
lean_dec_ref_known(v___x_808_, 1);
v___x_812_ = l_Lean_Meta_SavedState_restore___redArg(v_a_807_, v___y_699_, v___y_701_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_824_; 
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; 
v_unused_825_ = lean_ctor_get(v___x_812_, 0);
lean_dec(v_unused_825_);
v___x_814_ = v___x_812_;
v_isShared_815_ = v_isSharedCheck_824_;
goto v_resetjp_813_;
}
else
{
lean_dec(v___x_812_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_824_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_816_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__5);
lean_inc(v_a_711_);
if (v_isShared_815_ == 0)
{
lean_ctor_set_tag(v___x_814_, 1);
lean_ctor_set(v___x_814_, 0, v_a_711_);
v___x_818_ = v___x_814_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_711_);
v___x_818_ = v_reuseFailAlloc_823_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_816_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
v___x_821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_819_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_821_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_dec_ref_known(v___x_822_, 1);
v_a_704_ = v___x_710_;
goto v___jp_703_;
}
else
{
return v___x_822_;
}
}
}
}
else
{
return v___x_812_;
}
}
else
{
lean_dec(v_a_807_);
return v___x_808_;
}
}
else
{
lean_dec(v_a_807_);
return v___x_808_;
}
}
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
v_a_826_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_806_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_806_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
v_a_834_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_715_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_715_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
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
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
v_a_842_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_712_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_712_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___boxed(lean_object* v_as_850_, lean_object* v_sz_851_, lean_object* v_i_852_, lean_object* v_b_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
size_t v_sz_boxed_859_; size_t v_i_boxed_860_; lean_object* v_res_861_; 
v_sz_boxed_859_ = lean_unbox_usize(v_sz_851_);
lean_dec(v_sz_851_);
v_i_boxed_860_ = lean_unbox_usize(v_i_852_);
lean_dec(v_i_852_);
v_res_861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8(v_as_850_, v_sz_boxed_859_, v_i_boxed_860_, v_b_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec_ref(v_as_850_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9(lean_object* v_as_862_, size_t v_i_863_, size_t v_stop_864_, lean_object* v_b_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_a_872_; uint8_t v___x_876_; 
v___x_876_ = lean_usize_dec_eq(v_i_863_, v_stop_864_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_array_uget_borrowed(v_as_862_, v_i_863_);
v___x_878_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1___redArg(v___x_877_, v___y_867_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; uint8_t v___x_880_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_a_879_);
lean_dec_ref_known(v___x_878_, 1);
v___x_880_ = lean_unbox(v_a_879_);
lean_dec(v_a_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; 
lean_inc(v___x_877_);
v___x_881_ = lean_array_push(v_b_865_, v___x_877_);
v_a_872_ = v___x_881_;
goto v___jp_871_;
}
else
{
v_a_872_ = v_b_865_;
goto v___jp_871_;
}
}
else
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
lean_dec_ref(v_b_865_);
v_a_882_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_878_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_878_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
else
{
lean_object* v___x_890_; 
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v_b_865_);
return v___x_890_;
}
v___jp_871_:
{
size_t v___x_873_; size_t v___x_874_; 
v___x_873_ = ((size_t)1ULL);
v___x_874_ = lean_usize_add(v_i_863_, v___x_873_);
v_i_863_ = v___x_874_;
v_b_865_ = v_a_872_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9___boxed(lean_object* v_as_891_, lean_object* v_i_892_, lean_object* v_stop_893_, lean_object* v_b_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
size_t v_i_boxed_900_; size_t v_stop_boxed_901_; lean_object* v_res_902_; 
v_i_boxed_900_ = lean_unbox_usize(v_i_892_);
lean_dec(v_i_892_);
v_stop_boxed_901_ = lean_unbox_usize(v_stop_893_);
lean_dec(v_stop_893_);
v_res_902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9(v_as_891_, v_i_boxed_900_, v_stop_boxed_901_, v_b_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec_ref(v_as_891_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4(size_t v_sz_903_, size_t v_i_904_, lean_object* v_bs_905_){
_start:
{
uint8_t v___x_906_; 
v___x_906_ = lean_usize_dec_lt(v_i_904_, v_sz_903_);
if (v___x_906_ == 0)
{
return v_bs_905_;
}
else
{
lean_object* v_v_907_; lean_object* v___x_908_; lean_object* v_bs_x27_909_; lean_object* v___x_910_; size_t v___x_911_; size_t v___x_912_; lean_object* v___x_913_; 
v_v_907_ = lean_array_uget(v_bs_905_, v_i_904_);
v___x_908_ = lean_unsigned_to_nat(0u);
v_bs_x27_909_ = lean_array_uset(v_bs_905_, v_i_904_, v___x_908_);
v___x_910_ = l_Lean_Expr_mvarId_x21(v_v_907_);
lean_dec(v_v_907_);
v___x_911_ = ((size_t)1ULL);
v___x_912_ = lean_usize_add(v_i_904_, v___x_911_);
v___x_913_ = lean_array_uset(v_bs_x27_909_, v_i_904_, v___x_910_);
v_i_904_ = v___x_912_;
v_bs_905_ = v___x_913_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4___boxed(lean_object* v_sz_915_, lean_object* v_i_916_, lean_object* v_bs_917_){
_start:
{
size_t v_sz_boxed_918_; size_t v_i_boxed_919_; lean_object* v_res_920_; 
v_sz_boxed_918_ = lean_unbox_usize(v_sz_915_);
lean_dec(v_sz_915_);
v_i_boxed_919_ = lean_unbox_usize(v_i_916_);
lean_dec(v_i_916_);
v_res_920_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4(v_sz_boxed_918_, v_i_boxed_919_, v_bs_917_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__7(lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
if (lean_obj_tag(v_a_921_) == 0)
{
lean_object* v___x_923_; 
v___x_923_ = l_List_reverse___redArg(v_a_922_);
return v___x_923_;
}
else
{
lean_object* v_head_924_; lean_object* v_tail_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_934_; 
v_head_924_ = lean_ctor_get(v_a_921_, 0);
v_tail_925_ = lean_ctor_get(v_a_921_, 1);
v_isSharedCheck_934_ = !lean_is_exclusive(v_a_921_);
if (v_isSharedCheck_934_ == 0)
{
v___x_927_ = v_a_921_;
v_isShared_928_ = v_isSharedCheck_934_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_tail_925_);
lean_inc(v_head_924_);
lean_dec(v_a_921_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_934_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; lean_object* v___x_931_; 
v___x_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_929_, 0, v_head_924_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 1, v_a_922_);
lean_ctor_set(v___x_927_, 0, v___x_929_);
v___x_931_ = v___x_927_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_a_922_);
v___x_931_ = v_reuseFailAlloc_933_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
v_a_921_ = v_tail_925_;
v_a_922_ = v___x_931_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__1(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__0));
v___x_937_ = l_Lean_stringToMessageData(v___x_936_);
return v___x_937_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__3(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__2));
v___x_940_ = l_Lean_stringToMessageData(v___x_939_);
return v___x_940_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__5(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__4));
v___x_943_ = l_Lean_stringToMessageData(v___x_942_);
return v___x_943_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__7(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__6));
v___x_946_ = l_Lean_stringToMessageData(v___x_945_);
return v___x_946_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__9(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__8));
v___x_949_ = l_Lean_stringToMessageData(v___x_948_);
return v___x_949_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__12(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__11));
v___x_954_ = l_Lean_stringToMessageData(v___x_953_);
return v___x_954_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__14(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__13));
v___x_957_ = l_Lean_stringToMessageData(v___x_956_);
return v___x_957_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__16(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__15));
v___x_960_ = l_Lean_stringToMessageData(v___x_959_);
return v___x_960_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__22(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__21));
v___x_969_ = l_Lean_stringToMessageData(v___x_968_);
return v___x_969_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__24(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__23));
v___x_972_ = l_Lean_stringToMessageData(v___x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2(uint8_t v___x_973_, lean_object* v___x_974_, lean_object* v_fst_975_, lean_object* v___x_976_, lean_object* v_e_977_, uint8_t v___x_978_, lean_object* v_snd_979_, lean_object* v_____r_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___y_987_; lean_object* v_proof_988_; lean_object* v___x_992_; lean_object* v___y_994_; uint8_t v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; uint8_t v___y_1044_; lean_object* v___y_1045_; lean_object* v_a_1046_; size_t v_sz_1069_; size_t v___x_1070_; lean_object* v___x_1071_; lean_object* v___y_1073_; uint8_t v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; uint8_t v_fst_1106_; lean_object* v_fst_1107_; lean_object* v_snd_1108_; lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_992_ = l_Lean_mkAppN(v___x_974_, v_fst_975_);
v_sz_1069_ = lean_array_size(v_fst_975_);
v___x_1070_ = ((size_t)0ULL);
v___x_1071_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4(v_sz_1069_, v___x_1070_, v_fst_975_);
v___x_1142_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1143_ = lean_unsigned_to_nat(4u);
v___x_1144_ = l_Lean_Expr_isAppOfArity(v_snd_979_, v___x_1142_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1145_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1146_ = lean_unsigned_to_nat(3u);
v___x_1147_ = l_Lean_Expr_isAppOfArity(v_snd_979_, v___x_1145_, v___x_1146_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec_ref(v___x_1071_);
lean_dec_ref(v___x_992_);
lean_dec_ref(v_e_977_);
v___x_1148_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1149_ = l_Lean_MessageData_ofConstName(v___x_976_, v___x_978_);
v___x_1150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1148_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1150_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___x_1153_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1152_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1153_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1153_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
else
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1162_ = l_Lean_Expr_appFn_x21(v_snd_979_);
v___x_1163_ = l_Lean_Expr_appArg_x21(v___x_1162_);
lean_dec_ref(v___x_1162_);
v___x_1164_ = l_Lean_Expr_appArg_x21(v_snd_979_);
v_fst_1106_ = v___x_978_;
v_fst_1107_ = v___x_1163_;
v_snd_1108_ = v___x_1164_;
goto v___jp_1105_;
}
}
else
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1165_ = l_Lean_Expr_appFn_x21(v_snd_979_);
v___x_1166_ = l_Lean_Expr_appFn_x21(v___x_1165_);
lean_dec_ref(v___x_1165_);
v___x_1167_ = l_Lean_Expr_appArg_x21(v___x_1166_);
lean_dec_ref(v___x_1166_);
v___x_1168_ = l_Lean_Expr_appArg_x21(v_snd_979_);
v_fst_1106_ = v___x_973_;
v_fst_1107_ = v___x_1167_;
v_snd_1108_ = v___x_1168_;
goto v___jp_1105_;
}
v___jp_986_:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_989_, 0, v_proof_988_);
v___x_990_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_990_, 0, v___y_987_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
lean_ctor_set_uint8(v___x_990_, sizeof(void*)*2, v___x_973_);
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
return v___x_991_;
}
v___jp_993_:
{
lean_object* v___x_1000_; lean_object* v_a_1001_; lean_object* v___x_1002_; 
v___x_1000_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___y_994_, v___y_997_);
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref(v___x_1000_);
v___x_1002_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_992_, v___y_997_);
if (v___y_995_ == 0)
{
lean_object* v_a_1003_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_a_1003_);
lean_dec_ref(v___x_1002_);
v___y_987_ = v_a_1001_;
v_proof_988_ = v_a_1003_;
goto v___jp_986_;
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1005_; 
v_a_1004_ = lean_ctor_get(v___x_1002_, 0);
lean_inc_n(v_a_1004_, 2);
lean_dec_ref(v___x_1002_);
v___x_1005_ = l_Lean_Meta_mkEqOfHEq(v_a_1004_, v___x_973_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; 
lean_dec(v_a_1004_);
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1005_, 1);
v___y_987_ = v_a_1001_;
v_proof_988_ = v_a_1006_;
goto v___jp_986_;
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1038_; 
lean_dec(v_a_1001_);
v_a_1007_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1009_ = v___x_1005_;
v_isShared_1010_ = v_isSharedCheck_1038_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1005_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1038_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
uint8_t v___x_1011_; 
v___x_1011_ = l_Lean_Exception_isInterrupt(v_a_1007_);
if (v___x_1011_ == 0)
{
uint8_t v___x_1012_; 
lean_inc(v_a_1007_);
v___x_1012_ = l_Lean_Exception_isRuntime(v_a_1007_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_del_object(v___x_1009_);
v___x_1013_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1014_ = l_Lean_MessageData_ofExpr(v_a_1004_);
v___x_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = l_Lean_Exception_toMessageData(v_a_1007_);
v___x_1019_ = l_Lean_indentD(v___x_1018_);
v___x_1020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1017_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1022_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1023_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1023_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
else
{
lean_object* v___x_1033_; 
lean_dec(v_a_1004_);
if (v_isShared_1010_ == 0)
{
v___x_1033_ = v___x_1009_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1007_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
else
{
lean_object* v___x_1036_; 
lean_dec(v_a_1004_);
if (v_isShared_1010_ == 0)
{
v___x_1036_ = v___x_1009_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1007_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
}
v___jp_1039_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1047_ = lean_array_get_size(v_a_1046_);
v___x_1048_ = lean_unsigned_to_nat(0u);
v___x_1049_ = lean_nat_dec_eq(v___x_1047_, v___x_1048_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec_ref(v___y_1042_);
lean_dec_ref(v___x_992_);
v___x_1050_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1051_ = l_Lean_MessageData_ofConstName(v___x_976_, v___x_1049_);
v___x_1052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = lean_array_to_list(v_a_1046_);
v___x_1056_ = lean_box(0);
v___x_1057_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1055_, v___x_1056_);
v___x_1058_ = l_Lean_MessageData_ofList(v___x_1057_);
v___x_1059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1054_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1059_, v___y_1041_, v___y_1040_, v___y_1043_, v___y_1045_);
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1060_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1060_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
else
{
lean_dec_ref(v_a_1046_);
lean_dec(v___x_976_);
v___y_994_ = v___y_1042_;
v___y_995_ = v___y_1044_;
v___y_996_ = v___y_1041_;
v___y_997_ = v___y_1040_;
v___y_998_ = v___y_1043_;
v___y_999_ = v___y_1045_;
goto v___jp_993_;
}
}
v___jp_1072_:
{
lean_object* v___x_1079_; size_t v_sz_1080_; lean_object* v___x_1081_; 
v___x_1079_ = lean_box(0);
v_sz_1080_ = lean_array_size(v___x_1071_);
v___x_1081_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8(v___x_1071_, v_sz_1080_, v___x_1070_, v___x_1079_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
lean_dec_ref_known(v___x_1081_, 1);
v___x_1082_ = lean_unsigned_to_nat(0u);
v___x_1083_ = lean_array_get_size(v___x_1071_);
v___x_1084_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1085_ = lean_nat_dec_lt(v___x_1082_, v___x_1083_);
if (v___x_1085_ == 0)
{
lean_dec_ref(v___x_1071_);
v___y_1040_ = v___y_1076_;
v___y_1041_ = v___y_1075_;
v___y_1042_ = v___y_1073_;
v___y_1043_ = v___y_1077_;
v___y_1044_ = v___y_1074_;
v___y_1045_ = v___y_1078_;
v_a_1046_ = v___x_1084_;
goto v___jp_1039_;
}
else
{
size_t v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = lean_usize_of_nat(v___x_1083_);
v___x_1087_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9(v___x_1071_, v___x_1070_, v___x_1086_, v___x_1084_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec_ref(v___x_1071_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v___x_1087_, 1);
v___y_1040_ = v___y_1076_;
v___y_1041_ = v___y_1075_;
v___y_1042_ = v___y_1073_;
v___y_1043_ = v___y_1077_;
v___y_1044_ = v___y_1074_;
v___y_1045_ = v___y_1078_;
v_a_1046_ = v_a_1088_;
goto v___jp_1039_;
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
lean_dec_ref(v___y_1073_);
lean_dec_ref(v___x_992_);
lean_dec(v___x_976_);
v_a_1089_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1087_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1087_);
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
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec_ref(v___y_1073_);
lean_dec_ref(v___x_1071_);
lean_dec_ref(v___x_992_);
lean_dec(v___x_976_);
v_a_1097_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1081_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1081_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
v___jp_1105_:
{
lean_object* v___x_1109_; 
lean_inc_ref(v_fst_1107_);
lean_inc_ref(v_e_977_);
v___x_1109_ = l_Lean_Meta_isExprDefEq(v_e_977_, v_fst_1107_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; uint8_t v___x_1111_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___x_1109_, 1);
v___x_1111_ = lean_unbox(v_a_1110_);
lean_dec(v_a_1110_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_dec_ref(v_snd_1108_);
lean_dec_ref(v___x_1071_);
lean_dec_ref(v___x_992_);
v___x_1112_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1113_ = l_Lean_MessageData_ofExpr(v_fst_1107_);
v___x_1114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1112_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
v___x_1115_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1114_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
v___x_1117_ = l_Lean_MessageData_ofConstName(v___x_976_, v___x_978_);
v___x_1118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1118_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = l_Lean_MessageData_ofExpr(v_e_977_);
v___x_1122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1120_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
v___x_1124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1122_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1124_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1125_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1125_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
else
{
lean_dec_ref(v_fst_1107_);
lean_dec_ref(v_e_977_);
v___y_1073_ = v_snd_1108_;
v___y_1074_ = v_fst_1106_;
v___y_1075_ = v___y_981_;
v___y_1076_ = v___y_982_;
v___y_1077_ = v___y_983_;
v___y_1078_ = v___y_984_;
goto v___jp_1072_;
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec_ref(v_snd_1108_);
lean_dec_ref(v_fst_1107_);
lean_dec_ref(v___x_1071_);
lean_dec_ref(v___x_992_);
lean_dec_ref(v_e_977_);
lean_dec(v___x_976_);
v_a_1134_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1109_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1109_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2___boxed(lean_object* v___x_1169_, lean_object* v___x_1170_, lean_object* v_fst_1171_, lean_object* v___x_1172_, lean_object* v_e_1173_, lean_object* v___x_1174_, lean_object* v_snd_1175_, lean_object* v_____r_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
uint8_t v___x_85984__boxed_1182_; uint8_t v___x_85988__boxed_1183_; lean_object* v_res_1184_; 
v___x_85984__boxed_1182_ = lean_unbox(v___x_1169_);
v___x_85988__boxed_1183_ = lean_unbox(v___x_1174_);
v_res_1184_ = l_Lean_Meta_rwMatcher___lam__2(v___x_85984__boxed_1182_, v___x_1170_, v_fst_1171_, v___x_1172_, v_e_1173_, v___x_85988__boxed_1183_, v_snd_1175_, v_____r_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec_ref(v_snd_1175_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3(uint8_t v___x_1185_, lean_object* v___x_1186_, lean_object* v_fst_1187_, lean_object* v___x_1188_, lean_object* v_e_1189_, uint8_t v___x_1190_, lean_object* v_snd_1191_, lean_object* v_____r_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v___y_1199_; lean_object* v_proof_1200_; lean_object* v___x_1204_; uint8_t v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; uint8_t v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v_a_1258_; size_t v_sz_1281_; size_t v___x_1282_; lean_object* v___x_1283_; uint8_t v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; uint8_t v_fst_1318_; lean_object* v_fst_1319_; lean_object* v_snd_1320_; lean_object* v___x_1354_; lean_object* v___x_1355_; uint8_t v___x_1356_; 
v___x_1204_ = l_Lean_mkAppN(v___x_1186_, v_fst_1187_);
v_sz_1281_ = lean_array_size(v_fst_1187_);
v___x_1282_ = ((size_t)0ULL);
v___x_1283_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4(v_sz_1281_, v___x_1282_, v_fst_1187_);
v___x_1354_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1355_ = lean_unsigned_to_nat(4u);
v___x_1356_ = l_Lean_Expr_isAppOfArity(v_snd_1191_, v___x_1354_, v___x_1355_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; 
v___x_1357_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1358_ = lean_unsigned_to_nat(3u);
v___x_1359_ = l_Lean_Expr_isAppOfArity(v_snd_1191_, v___x_1357_, v___x_1358_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_dec_ref(v___x_1283_);
lean_dec_ref(v___x_1204_);
lean_dec_ref(v_e_1189_);
v___x_1360_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1361_ = l_Lean_MessageData_ofConstName(v___x_1188_, v___x_1190_);
v___x_1362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1360_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
v___x_1363_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1362_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
v___x_1365_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1364_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1365_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1365_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
else
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1374_ = l_Lean_Expr_appFn_x21(v_snd_1191_);
v___x_1375_ = l_Lean_Expr_appArg_x21(v___x_1374_);
lean_dec_ref(v___x_1374_);
v___x_1376_ = l_Lean_Expr_appArg_x21(v_snd_1191_);
v_fst_1318_ = v___x_1190_;
v_fst_1319_ = v___x_1375_;
v_snd_1320_ = v___x_1376_;
goto v___jp_1317_;
}
}
else
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1377_ = l_Lean_Expr_appFn_x21(v_snd_1191_);
v___x_1378_ = l_Lean_Expr_appFn_x21(v___x_1377_);
lean_dec_ref(v___x_1377_);
v___x_1379_ = l_Lean_Expr_appArg_x21(v___x_1378_);
lean_dec_ref(v___x_1378_);
v___x_1380_ = l_Lean_Expr_appArg_x21(v_snd_1191_);
v_fst_1318_ = v___x_1185_;
v_fst_1319_ = v___x_1379_;
v_snd_1320_ = v___x_1380_;
goto v___jp_1317_;
}
v___jp_1198_:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1201_, 0, v_proof_1200_);
v___x_1202_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1202_, 0, v___y_1199_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
lean_ctor_set_uint8(v___x_1202_, sizeof(void*)*2, v___x_1185_);
v___x_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
return v___x_1203_;
}
v___jp_1205_:
{
lean_object* v___x_1212_; lean_object* v_a_1213_; lean_object* v___x_1214_; 
v___x_1212_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___y_1207_, v___y_1209_);
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1213_);
lean_dec_ref(v___x_1212_);
v___x_1214_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1204_, v___y_1209_);
if (v___y_1206_ == 0)
{
lean_object* v_a_1215_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1215_);
lean_dec_ref(v___x_1214_);
v___y_1199_ = v_a_1213_;
v_proof_1200_ = v_a_1215_;
goto v___jp_1198_;
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1217_; 
v_a_1216_ = lean_ctor_get(v___x_1214_, 0);
lean_inc_n(v_a_1216_, 2);
lean_dec_ref(v___x_1214_);
v___x_1217_ = l_Lean_Meta_mkEqOfHEq(v_a_1216_, v___x_1185_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; 
lean_dec(v_a_1216_);
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1218_);
lean_dec_ref_known(v___x_1217_, 1);
v___y_1199_ = v_a_1213_;
v_proof_1200_ = v_a_1218_;
goto v___jp_1198_;
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1250_; 
lean_dec(v_a_1213_);
v_a_1219_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1221_ = v___x_1217_;
v_isShared_1222_ = v_isSharedCheck_1250_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1217_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1250_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
uint8_t v___x_1223_; 
v___x_1223_ = l_Lean_Exception_isInterrupt(v_a_1219_);
if (v___x_1223_ == 0)
{
uint8_t v___x_1224_; 
lean_inc(v_a_1219_);
v___x_1224_ = l_Lean_Exception_isRuntime(v_a_1219_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1243_; 
lean_del_object(v___x_1221_);
v___x_1225_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1226_ = l_Lean_MessageData_ofExpr(v_a_1216_);
v___x_1227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1225_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
v___x_1228_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1227_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
v___x_1230_ = l_Lean_Exception_toMessageData(v_a_1219_);
v___x_1231_ = l_Lean_indentD(v___x_1230_);
v___x_1232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1229_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
v___x_1233_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1232_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
v___x_1235_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1234_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1238_ = v___x_1235_;
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1235_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_a_1236_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
else
{
lean_object* v___x_1245_; 
lean_dec(v_a_1216_);
if (v_isShared_1222_ == 0)
{
v___x_1245_ = v___x_1221_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1219_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
else
{
lean_object* v___x_1248_; 
lean_dec(v_a_1216_);
if (v_isShared_1222_ == 0)
{
v___x_1248_ = v___x_1221_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1219_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
}
}
v___jp_1251_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
v___x_1259_ = lean_array_get_size(v_a_1258_);
v___x_1260_ = lean_unsigned_to_nat(0u);
v___x_1261_ = lean_nat_dec_eq(v___x_1259_, v___x_1260_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_dec_ref(v___y_1255_);
lean_dec_ref(v___x_1204_);
v___x_1262_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1263_ = l_Lean_MessageData_ofConstName(v___x_1188_, v___x_1261_);
v___x_1264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1262_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
v___x_1265_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1264_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = lean_array_to_list(v_a_1258_);
v___x_1268_ = lean_box(0);
v___x_1269_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1267_, v___x_1268_);
v___x_1270_ = l_Lean_MessageData_ofList(v___x_1269_);
v___x_1271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1266_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
v___x_1272_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1271_, v___y_1254_, v___y_1256_, v___y_1253_, v___y_1257_);
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1272_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1272_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
else
{
lean_dec_ref(v_a_1258_);
lean_dec(v___x_1188_);
v___y_1206_ = v___y_1252_;
v___y_1207_ = v___y_1255_;
v___y_1208_ = v___y_1254_;
v___y_1209_ = v___y_1256_;
v___y_1210_ = v___y_1253_;
v___y_1211_ = v___y_1257_;
goto v___jp_1205_;
}
}
v___jp_1284_:
{
lean_object* v___x_1291_; size_t v_sz_1292_; lean_object* v___x_1293_; 
v___x_1291_ = lean_box(0);
v_sz_1292_ = lean_array_size(v___x_1283_);
v___x_1293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8(v___x_1283_, v_sz_1292_, v___x_1282_, v___x_1291_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
lean_dec_ref_known(v___x_1293_, 1);
v___x_1294_ = lean_unsigned_to_nat(0u);
v___x_1295_ = lean_array_get_size(v___x_1283_);
v___x_1296_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1297_ = lean_nat_dec_lt(v___x_1294_, v___x_1295_);
if (v___x_1297_ == 0)
{
lean_dec_ref(v___x_1283_);
v___y_1252_ = v___y_1285_;
v___y_1253_ = v___y_1289_;
v___y_1254_ = v___y_1287_;
v___y_1255_ = v___y_1286_;
v___y_1256_ = v___y_1288_;
v___y_1257_ = v___y_1290_;
v_a_1258_ = v___x_1296_;
goto v___jp_1251_;
}
else
{
size_t v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = lean_usize_of_nat(v___x_1295_);
v___x_1299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9(v___x_1283_, v___x_1282_, v___x_1298_, v___x_1296_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
lean_dec_ref(v___x_1283_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1300_);
lean_dec_ref_known(v___x_1299_, 1);
v___y_1252_ = v___y_1285_;
v___y_1253_ = v___y_1289_;
v___y_1254_ = v___y_1287_;
v___y_1255_ = v___y_1286_;
v___y_1256_ = v___y_1288_;
v___y_1257_ = v___y_1290_;
v_a_1258_ = v_a_1300_;
goto v___jp_1251_;
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
lean_dec_ref(v___y_1286_);
lean_dec_ref(v___x_1204_);
lean_dec(v___x_1188_);
v_a_1301_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1299_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1299_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_dec_ref(v___y_1286_);
lean_dec_ref(v___x_1283_);
lean_dec_ref(v___x_1204_);
lean_dec(v___x_1188_);
v_a_1309_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1293_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1293_);
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
lean_object* v___x_1321_; 
lean_inc_ref(v_fst_1319_);
lean_inc_ref(v_e_1189_);
v___x_1321_ = l_Lean_Meta_isExprDefEq(v_e_1189_, v_fst_1319_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; uint8_t v___x_1323_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_a_1322_);
lean_dec_ref_known(v___x_1321_, 1);
v___x_1323_ = lean_unbox(v_a_1322_);
lean_dec(v_a_1322_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
lean_dec_ref(v_snd_1320_);
lean_dec_ref(v___x_1283_);
lean_dec_ref(v___x_1204_);
v___x_1324_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1325_ = l_Lean_MessageData_ofExpr(v_fst_1319_);
v___x_1326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1324_);
lean_ctor_set(v___x_1326_, 1, v___x_1325_);
v___x_1327_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1326_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
v___x_1329_ = l_Lean_MessageData_ofConstName(v___x_1188_, v___x_1190_);
v___x_1330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1328_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
v___x_1331_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1330_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
v___x_1333_ = l_Lean_MessageData_ofExpr(v_e_1189_);
v___x_1334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1332_);
lean_ctor_set(v___x_1334_, 1, v___x_1333_);
v___x_1335_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
v___x_1336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1334_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
v___x_1337_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1336_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1337_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1337_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
else
{
lean_dec_ref(v_fst_1319_);
lean_dec_ref(v_e_1189_);
v___y_1285_ = v_fst_1318_;
v___y_1286_ = v_snd_1320_;
v___y_1287_ = v___y_1193_;
v___y_1288_ = v___y_1194_;
v___y_1289_ = v___y_1195_;
v___y_1290_ = v___y_1196_;
goto v___jp_1284_;
}
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_dec_ref(v_snd_1320_);
lean_dec_ref(v_fst_1319_);
lean_dec_ref(v___x_1283_);
lean_dec_ref(v___x_1204_);
lean_dec_ref(v_e_1189_);
lean_dec(v___x_1188_);
v_a_1346_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1321_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1321_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3___boxed(lean_object* v___x_1381_, lean_object* v___x_1382_, lean_object* v_fst_1383_, lean_object* v___x_1384_, lean_object* v_e_1385_, lean_object* v___x_1386_, lean_object* v_snd_1387_, lean_object* v_____r_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
uint8_t v___x_86466__boxed_1394_; uint8_t v___x_86470__boxed_1395_; lean_object* v_res_1396_; 
v___x_86466__boxed_1394_ = lean_unbox(v___x_1381_);
v___x_86470__boxed_1395_ = lean_unbox(v___x_1386_);
v_res_1396_ = l_Lean_Meta_rwMatcher___lam__3(v___x_86466__boxed_1394_, v___x_1382_, v_fst_1383_, v___x_1384_, v_e_1385_, v___x_86470__boxed_1395_, v_snd_1387_, v_____r_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec_ref(v_snd_1387_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4(uint8_t v___x_1397_, lean_object* v___x_1398_, lean_object* v_fst_1399_, lean_object* v___x_1400_, lean_object* v_e_1401_, uint8_t v___x_1402_, lean_object* v_snd_1403_, lean_object* v_____r_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v___y_1411_; lean_object* v_proof_1412_; lean_object* v___x_1416_; uint8_t v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; uint8_t v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v_a_1470_; size_t v_sz_1493_; size_t v___x_1494_; lean_object* v___x_1495_; uint8_t v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; uint8_t v_fst_1530_; lean_object* v_fst_1531_; lean_object* v_snd_1532_; lean_object* v___x_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; 
v___x_1416_ = l_Lean_mkAppN(v___x_1398_, v_fst_1399_);
v_sz_1493_ = lean_array_size(v_fst_1399_);
v___x_1494_ = ((size_t)0ULL);
v___x_1495_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4(v_sz_1493_, v___x_1494_, v_fst_1399_);
v___x_1566_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1567_ = lean_unsigned_to_nat(4u);
v___x_1568_ = l_Lean_Expr_isAppOfArity(v_snd_1403_, v___x_1566_, v___x_1567_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; 
v___x_1569_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1570_ = lean_unsigned_to_nat(3u);
v___x_1571_ = l_Lean_Expr_isAppOfArity(v_snd_1403_, v___x_1569_, v___x_1570_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_dec_ref(v___x_1495_);
lean_dec_ref(v___x_1416_);
lean_dec_ref(v_e_1401_);
v___x_1572_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1573_ = l_Lean_MessageData_ofConstName(v___x_1400_, v___x_1402_);
v___x_1574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1572_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
v___x_1575_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1574_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1576_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1577_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1577_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1586_ = l_Lean_Expr_appFn_x21(v_snd_1403_);
v___x_1587_ = l_Lean_Expr_appArg_x21(v___x_1586_);
lean_dec_ref(v___x_1586_);
v___x_1588_ = l_Lean_Expr_appArg_x21(v_snd_1403_);
v_fst_1530_ = v___x_1402_;
v_fst_1531_ = v___x_1587_;
v_snd_1532_ = v___x_1588_;
goto v___jp_1529_;
}
}
else
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1589_ = l_Lean_Expr_appFn_x21(v_snd_1403_);
v___x_1590_ = l_Lean_Expr_appFn_x21(v___x_1589_);
lean_dec_ref(v___x_1589_);
v___x_1591_ = l_Lean_Expr_appArg_x21(v___x_1590_);
lean_dec_ref(v___x_1590_);
v___x_1592_ = l_Lean_Expr_appArg_x21(v_snd_1403_);
v_fst_1530_ = v___x_1397_;
v_fst_1531_ = v___x_1591_;
v_snd_1532_ = v___x_1592_;
goto v___jp_1529_;
}
v___jp_1410_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1413_, 0, v_proof_1412_);
v___x_1414_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1414_, 0, v___y_1411_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
lean_ctor_set_uint8(v___x_1414_, sizeof(void*)*2, v___x_1397_);
v___x_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
return v___x_1415_;
}
v___jp_1417_:
{
lean_object* v___x_1424_; lean_object* v_a_1425_; lean_object* v___x_1426_; 
v___x_1424_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___y_1419_, v___y_1421_);
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
lean_dec_ref(v___x_1424_);
v___x_1426_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1416_, v___y_1421_);
if (v___y_1418_ == 0)
{
lean_object* v_a_1427_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref(v___x_1426_);
v___y_1411_ = v_a_1425_;
v_proof_1412_ = v_a_1427_;
goto v___jp_1410_;
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1429_; 
v_a_1428_ = lean_ctor_get(v___x_1426_, 0);
lean_inc_n(v_a_1428_, 2);
lean_dec_ref(v___x_1426_);
v___x_1429_ = l_Lean_Meta_mkEqOfHEq(v_a_1428_, v___x_1397_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; 
lean_dec(v_a_1428_);
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref_known(v___x_1429_, 1);
v___y_1411_ = v_a_1425_;
v_proof_1412_ = v_a_1430_;
goto v___jp_1410_;
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1462_; 
lean_dec(v_a_1425_);
v_a_1431_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1433_ = v___x_1429_;
v_isShared_1434_ = v_isSharedCheck_1462_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1429_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1462_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
uint8_t v___x_1435_; 
v___x_1435_ = l_Lean_Exception_isInterrupt(v_a_1431_);
if (v___x_1435_ == 0)
{
uint8_t v___x_1436_; 
lean_inc(v_a_1431_);
v___x_1436_ = l_Lean_Exception_isRuntime(v_a_1431_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_del_object(v___x_1433_);
v___x_1437_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1438_ = l_Lean_MessageData_ofExpr(v_a_1428_);
v___x_1439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1437_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
v___x_1440_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1439_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
v___x_1442_ = l_Lean_Exception_toMessageData(v_a_1431_);
v___x_1443_ = l_Lean_indentD(v___x_1442_);
v___x_1444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1441_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
v___x_1445_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1444_);
lean_ctor_set(v___x_1446_, 1, v___x_1445_);
v___x_1447_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1446_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
else
{
lean_object* v___x_1457_; 
lean_dec(v_a_1428_);
if (v_isShared_1434_ == 0)
{
v___x_1457_ = v___x_1433_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1431_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
else
{
lean_object* v___x_1460_; 
lean_dec(v_a_1428_);
if (v_isShared_1434_ == 0)
{
v___x_1460_ = v___x_1433_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1431_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
}
}
v___jp_1463_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; 
v___x_1471_ = lean_array_get_size(v_a_1470_);
v___x_1472_ = lean_unsigned_to_nat(0u);
v___x_1473_ = lean_nat_dec_eq(v___x_1471_, v___x_1472_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec_ref(v___y_1468_);
lean_dec_ref(v___x_1416_);
v___x_1474_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1475_ = l_Lean_MessageData_ofConstName(v___x_1400_, v___x_1473_);
v___x_1476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1474_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
v___x_1477_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1476_);
lean_ctor_set(v___x_1478_, 1, v___x_1477_);
v___x_1479_ = lean_array_to_list(v_a_1470_);
v___x_1480_ = lean_box(0);
v___x_1481_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1479_, v___x_1480_);
v___x_1482_ = l_Lean_MessageData_ofList(v___x_1481_);
v___x_1483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1478_);
lean_ctor_set(v___x_1483_, 1, v___x_1482_);
v___x_1484_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1483_, v___y_1465_, v___y_1466_, v___y_1469_, v___y_1464_);
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
else
{
lean_dec_ref(v_a_1470_);
lean_dec(v___x_1400_);
v___y_1418_ = v___y_1467_;
v___y_1419_ = v___y_1468_;
v___y_1420_ = v___y_1465_;
v___y_1421_ = v___y_1466_;
v___y_1422_ = v___y_1469_;
v___y_1423_ = v___y_1464_;
goto v___jp_1417_;
}
}
v___jp_1496_:
{
lean_object* v___x_1503_; size_t v_sz_1504_; lean_object* v___x_1505_; 
v___x_1503_ = lean_box(0);
v_sz_1504_ = lean_array_size(v___x_1495_);
v___x_1505_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8(v___x_1495_, v_sz_1504_, v___x_1494_, v___x_1503_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; uint8_t v___x_1509_; 
lean_dec_ref_known(v___x_1505_, 1);
v___x_1506_ = lean_unsigned_to_nat(0u);
v___x_1507_ = lean_array_get_size(v___x_1495_);
v___x_1508_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1509_ = lean_nat_dec_lt(v___x_1506_, v___x_1507_);
if (v___x_1509_ == 0)
{
lean_dec_ref(v___x_1495_);
v___y_1464_ = v___y_1502_;
v___y_1465_ = v___y_1499_;
v___y_1466_ = v___y_1500_;
v___y_1467_ = v___y_1497_;
v___y_1468_ = v___y_1498_;
v___y_1469_ = v___y_1501_;
v_a_1470_ = v___x_1508_;
goto v___jp_1463_;
}
else
{
size_t v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = lean_usize_of_nat(v___x_1507_);
v___x_1511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9(v___x_1495_, v___x_1494_, v___x_1510_, v___x_1508_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
lean_dec_ref(v___x_1495_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1512_);
lean_dec_ref_known(v___x_1511_, 1);
v___y_1464_ = v___y_1502_;
v___y_1465_ = v___y_1499_;
v___y_1466_ = v___y_1500_;
v___y_1467_ = v___y_1497_;
v___y_1468_ = v___y_1498_;
v___y_1469_ = v___y_1501_;
v_a_1470_ = v_a_1512_;
goto v___jp_1463_;
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec_ref(v___y_1498_);
lean_dec_ref(v___x_1416_);
lean_dec(v___x_1400_);
v_a_1513_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1511_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1511_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
lean_dec_ref(v___y_1498_);
lean_dec_ref(v___x_1495_);
lean_dec_ref(v___x_1416_);
lean_dec(v___x_1400_);
v_a_1521_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1505_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1505_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
v___jp_1529_:
{
lean_object* v___x_1533_; 
lean_inc_ref(v_fst_1531_);
lean_inc_ref(v_e_1401_);
v___x_1533_ = l_Lean_Meta_isExprDefEq(v_e_1401_, v_fst_1531_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; uint8_t v___x_1535_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1534_);
lean_dec_ref_known(v___x_1533_, 1);
v___x_1535_ = lean_unbox(v_a_1534_);
lean_dec(v_a_1534_);
if (v___x_1535_ == 0)
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
lean_dec_ref(v_snd_1532_);
lean_dec_ref(v___x_1495_);
lean_dec_ref(v___x_1416_);
v___x_1536_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1537_ = l_Lean_MessageData_ofExpr(v_fst_1531_);
v___x_1538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1536_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1538_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = l_Lean_MessageData_ofConstName(v___x_1400_, v___x_1402_);
v___x_1542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1540_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
v___x_1543_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1542_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
v___x_1545_ = l_Lean_MessageData_ofExpr(v_e_1401_);
v___x_1546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1544_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
v___x_1547_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
v___x_1548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1546_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v___x_1549_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_1548_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1549_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1549_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
else
{
lean_dec_ref(v_fst_1531_);
lean_dec_ref(v_e_1401_);
v___y_1497_ = v_fst_1530_;
v___y_1498_ = v_snd_1532_;
v___y_1499_ = v___y_1405_;
v___y_1500_ = v___y_1406_;
v___y_1501_ = v___y_1407_;
v___y_1502_ = v___y_1408_;
goto v___jp_1496_;
}
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_dec_ref(v_snd_1532_);
lean_dec_ref(v_fst_1531_);
lean_dec_ref(v___x_1495_);
lean_dec_ref(v___x_1416_);
lean_dec_ref(v_e_1401_);
lean_dec(v___x_1400_);
v_a_1558_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1533_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1533_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4___boxed(lean_object* v___x_1593_, lean_object* v___x_1594_, lean_object* v_fst_1595_, lean_object* v___x_1596_, lean_object* v_e_1597_, lean_object* v___x_1598_, lean_object* v_snd_1599_, lean_object* v_____r_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
uint8_t v___x_86923__boxed_1606_; uint8_t v___x_86927__boxed_1607_; lean_object* v_res_1608_; 
v___x_86923__boxed_1606_ = lean_unbox(v___x_1593_);
v___x_86927__boxed_1607_ = lean_unbox(v___x_1598_);
v_res_1608_ = l_Lean_Meta_rwMatcher___lam__4(v___x_86923__boxed_1606_, v___x_1594_, v_fst_1595_, v___x_1596_, v_e_1597_, v___x_86927__boxed_1607_, v_snd_1599_, v_____r_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec_ref(v_snd_1599_);
return v_res_1608_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1609_; double v___x_1610_; 
v___x_1609_ = lean_unsigned_to_nat(0u);
v___x_1610_ = lean_float_of_nat(v___x_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(lean_object* v_cls_1614_, lean_object* v_msg_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v_ref_1621_; lean_object* v___x_1622_; lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1668_; 
v_ref_1621_ = lean_ctor_get(v___y_1618_, 2);
v___x_1622_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3_spec__4(v_msg_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1625_ = v___x_1622_;
v_isShared_1626_ = v_isSharedCheck_1668_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1668_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v_traceState_1628_; lean_object* v_env_1629_; lean_object* v_nextMacroScope_1630_; lean_object* v_ngen_1631_; lean_object* v_auxDeclNGen_1632_; lean_object* v_cache_1633_; lean_object* v_recordedDeps_1634_; lean_object* v_messages_1635_; lean_object* v_infoState_1636_; lean_object* v_snapshotTasks_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1667_; 
v___x_1627_ = lean_st_ref_take(v___y_1619_);
v_traceState_1628_ = lean_ctor_get(v___x_1627_, 4);
v_env_1629_ = lean_ctor_get(v___x_1627_, 0);
v_nextMacroScope_1630_ = lean_ctor_get(v___x_1627_, 1);
v_ngen_1631_ = lean_ctor_get(v___x_1627_, 2);
v_auxDeclNGen_1632_ = lean_ctor_get(v___x_1627_, 3);
v_cache_1633_ = lean_ctor_get(v___x_1627_, 5);
v_recordedDeps_1634_ = lean_ctor_get(v___x_1627_, 6);
v_messages_1635_ = lean_ctor_get(v___x_1627_, 7);
v_infoState_1636_ = lean_ctor_get(v___x_1627_, 8);
v_snapshotTasks_1637_ = lean_ctor_get(v___x_1627_, 9);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1639_ = v___x_1627_;
v_isShared_1640_ = v_isSharedCheck_1667_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_snapshotTasks_1637_);
lean_inc(v_infoState_1636_);
lean_inc(v_messages_1635_);
lean_inc(v_recordedDeps_1634_);
lean_inc(v_cache_1633_);
lean_inc(v_traceState_1628_);
lean_inc(v_auxDeclNGen_1632_);
lean_inc(v_ngen_1631_);
lean_inc(v_nextMacroScope_1630_);
lean_inc(v_env_1629_);
lean_dec(v___x_1627_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1667_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
uint64_t v_tid_1641_; lean_object* v_traces_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1666_; 
v_tid_1641_ = lean_ctor_get_uint64(v_traceState_1628_, sizeof(void*)*1);
v_traces_1642_ = lean_ctor_get(v_traceState_1628_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_traceState_1628_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1644_ = v_traceState_1628_;
v_isShared_1645_ = v_isSharedCheck_1666_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_traces_1642_);
lean_dec(v_traceState_1628_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1666_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; double v___x_1648_; uint8_t v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1657_; 
v___x_1646_ = lean_box(0);
v___x_1647_ = lean_box(0);
v___x_1648_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0);
v___x_1649_ = 0;
v___x_1650_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__1));
v___x_1651_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1651_, 0, v_cls_1614_);
lean_ctor_set(v___x_1651_, 1, v___x_1647_);
lean_ctor_set(v___x_1651_, 2, v___x_1650_);
lean_ctor_set_float(v___x_1651_, sizeof(void*)*3, v___x_1648_);
lean_ctor_set_float(v___x_1651_, sizeof(void*)*3 + 8, v___x_1648_);
lean_ctor_set_uint8(v___x_1651_, sizeof(void*)*3 + 16, v___x_1649_);
v___x_1652_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__2));
v___x_1653_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1651_);
lean_ctor_set(v___x_1653_, 1, v_a_1623_);
lean_ctor_set(v___x_1653_, 2, v___x_1652_);
lean_inc(v_ref_1621_);
v___x_1654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1654_, 0, v_ref_1621_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = l_Lean_PersistentArray_push___redArg(v_traces_1642_, v___x_1654_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v___x_1655_);
v___x_1657_ = v___x_1644_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1655_);
lean_ctor_set_uint64(v_reuseFailAlloc_1665_, sizeof(void*)*1, v_tid_1641_);
v___x_1657_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v___x_1659_; 
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 4, v___x_1657_);
v___x_1659_ = v___x_1639_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_env_1629_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_nextMacroScope_1630_);
lean_ctor_set(v_reuseFailAlloc_1664_, 2, v_ngen_1631_);
lean_ctor_set(v_reuseFailAlloc_1664_, 3, v_auxDeclNGen_1632_);
lean_ctor_set(v_reuseFailAlloc_1664_, 4, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1664_, 5, v_cache_1633_);
lean_ctor_set(v_reuseFailAlloc_1664_, 6, v_recordedDeps_1634_);
lean_ctor_set(v_reuseFailAlloc_1664_, 7, v_messages_1635_);
lean_ctor_set(v_reuseFailAlloc_1664_, 8, v_infoState_1636_);
lean_ctor_set(v_reuseFailAlloc_1664_, 9, v_snapshotTasks_1637_);
v___x_1659_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
lean_object* v___x_1660_; lean_object* v___x_1662_; 
v___x_1660_ = lean_st_ref_put(v___y_1619_, v___x_1659_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v___x_1646_);
v___x_1662_ = v___x_1625_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1646_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___boxed(lean_object* v_cls_1669_, lean_object* v_msg_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(v_cls_1669_, v_msg_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__17(lean_object* v_opts_1677_, lean_object* v_opt_1678_){
_start:
{
lean_object* v_name_1679_; lean_object* v_defValue_1680_; lean_object* v_map_1681_; lean_object* v___x_1682_; 
v_name_1679_ = lean_ctor_get(v_opt_1678_, 0);
v_defValue_1680_ = lean_ctor_get(v_opt_1678_, 1);
v_map_1681_ = lean_ctor_get(v_opts_1677_, 0);
v___x_1682_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1681_, v_name_1679_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_inc(v_defValue_1680_);
return v_defValue_1680_;
}
else
{
lean_object* v_val_1683_; 
v_val_1683_ = lean_ctor_get(v___x_1682_, 0);
lean_inc(v_val_1683_);
lean_dec_ref_known(v___x_1682_, 1);
if (lean_obj_tag(v_val_1683_) == 3)
{
lean_object* v_v_1684_; 
v_v_1684_ = lean_ctor_get(v_val_1683_, 0);
lean_inc(v_v_1684_);
lean_dec_ref_known(v_val_1683_, 1);
return v_v_1684_;
}
else
{
lean_dec(v_val_1683_);
lean_inc(v_defValue_1680_);
return v_defValue_1680_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__17___boxed(lean_object* v_opts_1685_, lean_object* v_opt_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__17(v_opts_1685_, v_opt_1686_);
lean_dec_ref(v_opt_1686_);
lean_dec_ref(v_opts_1685_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___redArg(lean_object* v_x_1688_){
_start:
{
if (lean_obj_tag(v_x_1688_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
v_a_1690_ = lean_ctor_get(v_x_1688_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_x_1688_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v_x_1688_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v_x_1688_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
lean_ctor_set_tag(v___x_1692_, 1);
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
v_a_1698_ = lean_ctor_get(v_x_1688_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v_x_1688_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v_x_1688_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v_x_1688_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
lean_ctor_set_tag(v___x_1700_, 0);
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___redArg___boxed(lean_object* v_x_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___redArg(v_x_1706_);
return v_res_1708_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16(lean_object* v_e_1709_){
_start:
{
if (lean_obj_tag(v_e_1709_) == 0)
{
uint8_t v___x_1710_; 
v___x_1710_ = 2;
return v___x_1710_;
}
else
{
uint8_t v___x_1711_; 
v___x_1711_ = 0;
return v___x_1711_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16___boxed(lean_object* v_e_1712_){
_start:
{
uint8_t v_res_1713_; lean_object* v_r_1714_; 
v_res_1713_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16(v_e_1712_);
lean_dec_ref(v_e_1712_);
v_r_1714_ = lean_box(v_res_1713_);
return v_r_1714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14_spec__16(size_t v_sz_1715_, size_t v_i_1716_, lean_object* v_bs_1717_){
_start:
{
uint8_t v___x_1718_; 
v___x_1718_ = lean_usize_dec_lt(v_i_1716_, v_sz_1715_);
if (v___x_1718_ == 0)
{
return v_bs_1717_;
}
else
{
lean_object* v_v_1719_; lean_object* v_msg_1720_; lean_object* v___x_1721_; lean_object* v_bs_x27_1722_; size_t v___x_1723_; size_t v___x_1724_; lean_object* v___x_1725_; 
v_v_1719_ = lean_array_uget_borrowed(v_bs_1717_, v_i_1716_);
v_msg_1720_ = lean_ctor_get(v_v_1719_, 1);
lean_inc_ref(v_msg_1720_);
v___x_1721_ = lean_unsigned_to_nat(0u);
v_bs_x27_1722_ = lean_array_uset(v_bs_1717_, v_i_1716_, v___x_1721_);
v___x_1723_ = ((size_t)1ULL);
v___x_1724_ = lean_usize_add(v_i_1716_, v___x_1723_);
v___x_1725_ = lean_array_uset(v_bs_x27_1722_, v_i_1716_, v_msg_1720_);
v_i_1716_ = v___x_1724_;
v_bs_1717_ = v___x_1725_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14_spec__16___boxed(lean_object* v_sz_1727_, lean_object* v_i_1728_, lean_object* v_bs_1729_){
_start:
{
size_t v_sz_boxed_1730_; size_t v_i_boxed_1731_; lean_object* v_res_1732_; 
v_sz_boxed_1730_ = lean_unbox_usize(v_sz_1727_);
lean_dec(v_sz_1727_);
v_i_boxed_1731_ = lean_unbox_usize(v_i_1728_);
lean_dec(v_i_1728_);
v_res_1732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14_spec__16(v_sz_boxed_1730_, v_i_boxed_1731_, v_bs_1729_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14(lean_object* v_oldTraces_1733_, lean_object* v_data_1734_, lean_object* v_ref_1735_, lean_object* v_msg_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v_toCold_1742_; lean_object* v_currRecDepth_1743_; lean_object* v_ref_1744_; uint16_t v_optionFlags_1745_; uint8_t v_suppressElabErrors_1746_; uint8_t v_isRecordingDeps_1747_; lean_object* v_ref_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v_traceState_1751_; lean_object* v_traces_1752_; lean_object* v___x_1753_; size_t v_sz_1754_; size_t v___x_1755_; lean_object* v___x_1756_; lean_object* v_msg_1757_; lean_object* v___x_1758_; lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1797_; 
v_toCold_1742_ = lean_ctor_get(v___y_1739_, 0);
v_currRecDepth_1743_ = lean_ctor_get(v___y_1739_, 1);
v_ref_1744_ = lean_ctor_get(v___y_1739_, 2);
v_optionFlags_1745_ = lean_ctor_get_uint16(v___y_1739_, sizeof(void*)*3);
v_suppressElabErrors_1746_ = lean_ctor_get_uint8(v___y_1739_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1747_ = lean_ctor_get_uint8(v___y_1739_, sizeof(void*)*3 + 3);
v_ref_1748_ = l_Lean_replaceRef(v_ref_1735_, v_ref_1744_);
lean_inc(v_currRecDepth_1743_);
lean_inc_ref(v_toCold_1742_);
v___x_1749_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1749_, 0, v_toCold_1742_);
lean_ctor_set(v___x_1749_, 1, v_currRecDepth_1743_);
lean_ctor_set(v___x_1749_, 2, v_ref_1748_);
lean_ctor_set_uint16(v___x_1749_, sizeof(void*)*3, v_optionFlags_1745_);
lean_ctor_set_uint8(v___x_1749_, sizeof(void*)*3 + 2, v_suppressElabErrors_1746_);
lean_ctor_set_uint8(v___x_1749_, sizeof(void*)*3 + 3, v_isRecordingDeps_1747_);
v___x_1750_ = lean_st_ref_get(v___y_1740_);
v_traceState_1751_ = lean_ctor_get(v___x_1750_, 4);
lean_inc_ref(v_traceState_1751_);
lean_dec(v___x_1750_);
v_traces_1752_ = lean_ctor_get(v_traceState_1751_, 0);
lean_inc_ref(v_traces_1752_);
lean_dec_ref(v_traceState_1751_);
v___x_1753_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1752_);
lean_dec_ref(v_traces_1752_);
v_sz_1754_ = lean_array_size(v___x_1753_);
v___x_1755_ = ((size_t)0ULL);
v___x_1756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14_spec__16(v_sz_1754_, v___x_1755_, v___x_1753_);
v_msg_1757_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1757_, 0, v_data_1734_);
lean_ctor_set(v_msg_1757_, 1, v_msg_1736_);
lean_ctor_set(v_msg_1757_, 2, v___x_1756_);
v___x_1758_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3_spec__4(v_msg_1757_, v___y_1737_, v___y_1738_, v___x_1749_, v___y_1740_);
lean_dec_ref_known(v___x_1749_, 3);
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1761_ = v___x_1758_;
v_isShared_1762_ = v_isSharedCheck_1797_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1797_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1763_; lean_object* v_traceState_1764_; lean_object* v_env_1765_; lean_object* v_nextMacroScope_1766_; lean_object* v_ngen_1767_; lean_object* v_auxDeclNGen_1768_; lean_object* v_cache_1769_; lean_object* v_recordedDeps_1770_; lean_object* v_messages_1771_; lean_object* v_infoState_1772_; lean_object* v_snapshotTasks_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1796_; 
v___x_1763_ = lean_st_ref_take(v___y_1740_);
v_traceState_1764_ = lean_ctor_get(v___x_1763_, 4);
v_env_1765_ = lean_ctor_get(v___x_1763_, 0);
v_nextMacroScope_1766_ = lean_ctor_get(v___x_1763_, 1);
v_ngen_1767_ = lean_ctor_get(v___x_1763_, 2);
v_auxDeclNGen_1768_ = lean_ctor_get(v___x_1763_, 3);
v_cache_1769_ = lean_ctor_get(v___x_1763_, 5);
v_recordedDeps_1770_ = lean_ctor_get(v___x_1763_, 6);
v_messages_1771_ = lean_ctor_get(v___x_1763_, 7);
v_infoState_1772_ = lean_ctor_get(v___x_1763_, 8);
v_snapshotTasks_1773_ = lean_ctor_get(v___x_1763_, 9);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1775_ = v___x_1763_;
v_isShared_1776_ = v_isSharedCheck_1796_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_snapshotTasks_1773_);
lean_inc(v_infoState_1772_);
lean_inc(v_messages_1771_);
lean_inc(v_recordedDeps_1770_);
lean_inc(v_cache_1769_);
lean_inc(v_traceState_1764_);
lean_inc(v_auxDeclNGen_1768_);
lean_inc(v_ngen_1767_);
lean_inc(v_nextMacroScope_1766_);
lean_inc(v_env_1765_);
lean_dec(v___x_1763_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1796_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
uint64_t v_tid_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1794_; 
v_tid_1777_ = lean_ctor_get_uint64(v_traceState_1764_, sizeof(void*)*1);
v_isSharedCheck_1794_ = !lean_is_exclusive(v_traceState_1764_);
if (v_isSharedCheck_1794_ == 0)
{
lean_object* v_unused_1795_; 
v_unused_1795_ = lean_ctor_get(v_traceState_1764_, 0);
lean_dec(v_unused_1795_);
v___x_1779_ = v_traceState_1764_;
v_isShared_1780_ = v_isSharedCheck_1794_;
goto v_resetjp_1778_;
}
else
{
lean_dec(v_traceState_1764_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1794_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1785_; 
v___x_1781_ = lean_box(0);
v___x_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1782_, 0, v_ref_1735_);
lean_ctor_set(v___x_1782_, 1, v_a_1759_);
v___x_1783_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1733_, v___x_1782_);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1783_);
v___x_1785_ = v___x_1779_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1783_);
lean_ctor_set_uint64(v_reuseFailAlloc_1793_, sizeof(void*)*1, v_tid_1777_);
v___x_1785_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
lean_object* v___x_1787_; 
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 4, v___x_1785_);
v___x_1787_ = v___x_1775_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_env_1765_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_nextMacroScope_1766_);
lean_ctor_set(v_reuseFailAlloc_1792_, 2, v_ngen_1767_);
lean_ctor_set(v_reuseFailAlloc_1792_, 3, v_auxDeclNGen_1768_);
lean_ctor_set(v_reuseFailAlloc_1792_, 4, v___x_1785_);
lean_ctor_set(v_reuseFailAlloc_1792_, 5, v_cache_1769_);
lean_ctor_set(v_reuseFailAlloc_1792_, 6, v_recordedDeps_1770_);
lean_ctor_set(v_reuseFailAlloc_1792_, 7, v_messages_1771_);
lean_ctor_set(v_reuseFailAlloc_1792_, 8, v_infoState_1772_);
lean_ctor_set(v_reuseFailAlloc_1792_, 9, v_snapshotTasks_1773_);
v___x_1787_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_object* v___x_1788_; lean_object* v___x_1790_; 
v___x_1788_ = lean_st_ref_put(v___y_1740_, v___x_1787_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v___x_1781_);
v___x_1790_ = v___x_1761_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1781_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14___boxed(lean_object* v_oldTraces_1798_, lean_object* v_data_1799_, lean_object* v_ref_1800_, lean_object* v_msg_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14(v_oldTraces_1798_, v_data_1799_, v_ref_1800_, v_msg_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
return v_res_1807_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__1(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__0));
v___x_1810_ = l_Lean_stringToMessageData(v___x_1809_);
return v___x_1810_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__2(void){
_start:
{
lean_object* v___x_1811_; double v___x_1812_; 
v___x_1811_ = lean_unsigned_to_nat(1000u);
v___x_1812_ = lean_float_of_nat(v___x_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12(lean_object* v_cls_1813_, uint8_t v_collapsed_1814_, lean_object* v_tag_1815_, lean_object* v_opts_1816_, uint8_t v_clsEnabled_1817_, lean_object* v_oldTraces_1818_, lean_object* v_msg_1819_, lean_object* v_resStartStop_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v_fst_1826_; lean_object* v_snd_1827_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v_data_1831_; lean_object* v_fst_1842_; lean_object* v_snd_1843_; lean_object* v___x_1844_; uint8_t v___x_1845_; lean_object* v___y_1847_; lean_object* v_a_1848_; uint8_t v___y_1863_; double v___y_1895_; 
v_fst_1826_ = lean_ctor_get(v_resStartStop_1820_, 0);
lean_inc(v_fst_1826_);
v_snd_1827_ = lean_ctor_get(v_resStartStop_1820_, 1);
lean_inc(v_snd_1827_);
lean_dec_ref(v_resStartStop_1820_);
v_fst_1842_ = lean_ctor_get(v_snd_1827_, 0);
lean_inc(v_fst_1842_);
v_snd_1843_ = lean_ctor_get(v_snd_1827_, 1);
lean_inc(v_snd_1843_);
lean_dec(v_snd_1827_);
v___x_1844_ = l_Lean_trace_profiler;
v___x_1845_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11(v_opts_1816_, v___x_1844_);
if (v___x_1845_ == 0)
{
v___y_1863_ = v___x_1845_;
goto v___jp_1862_;
}
else
{
lean_object* v___x_1900_; uint8_t v___x_1901_; 
v___x_1900_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1901_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11(v_opts_1816_, v___x_1900_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1902_; lean_object* v___x_1903_; double v___x_1904_; double v___x_1905_; double v___x_1906_; 
v___x_1902_ = l_Lean_trace_profiler_threshold;
v___x_1903_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__17(v_opts_1816_, v___x_1902_);
v___x_1904_ = lean_float_of_nat(v___x_1903_);
v___x_1905_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__2);
v___x_1906_ = lean_float_div(v___x_1904_, v___x_1905_);
v___y_1895_ = v___x_1906_;
goto v___jp_1894_;
}
else
{
lean_object* v___x_1907_; lean_object* v___x_1908_; double v___x_1909_; 
v___x_1907_ = l_Lean_trace_profiler_threshold;
v___x_1908_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__17(v_opts_1816_, v___x_1907_);
v___x_1909_ = lean_float_of_nat(v___x_1908_);
v___y_1895_ = v___x_1909_;
goto v___jp_1894_;
}
}
v___jp_1828_:
{
lean_object* v___x_1832_; 
lean_inc(v___y_1829_);
v___x_1832_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__14(v_oldTraces_1818_, v_data_1831_, v___y_1829_, v___y_1830_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v___x_1833_; 
lean_dec_ref_known(v___x_1832_, 1);
v___x_1833_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___redArg(v_fst_1826_);
return v___x_1833_;
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
lean_dec(v_fst_1826_);
v_a_1834_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1832_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1832_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
v___jp_1846_:
{
uint8_t v_result_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; double v___x_1852_; lean_object* v_data_1853_; 
v_result_1849_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__16(v_fst_1826_);
v___x_1850_ = lean_box(v_result_1849_);
v___x_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
v___x_1852_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__0);
lean_inc_ref(v_tag_1815_);
lean_inc_ref(v___x_1851_);
lean_inc(v_cls_1813_);
v_data_1853_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1853_, 0, v_cls_1813_);
lean_ctor_set(v_data_1853_, 1, v___x_1851_);
lean_ctor_set(v_data_1853_, 2, v_tag_1815_);
lean_ctor_set_float(v_data_1853_, sizeof(void*)*3, v___x_1852_);
lean_ctor_set_float(v_data_1853_, sizeof(void*)*3 + 8, v___x_1852_);
lean_ctor_set_uint8(v_data_1853_, sizeof(void*)*3 + 16, v_collapsed_1814_);
if (v___x_1845_ == 0)
{
lean_dec_ref_known(v___x_1851_, 1);
lean_dec(v_snd_1843_);
lean_dec(v_fst_1842_);
lean_dec_ref(v_tag_1815_);
lean_dec(v_cls_1813_);
v___y_1829_ = v___y_1847_;
v___y_1830_ = v_a_1848_;
v_data_1831_ = v_data_1853_;
goto v___jp_1828_;
}
else
{
lean_object* v_data_1854_; double v___x_1855_; double v___x_1856_; 
lean_dec_ref_known(v_data_1853_, 3);
v_data_1854_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1854_, 0, v_cls_1813_);
lean_ctor_set(v_data_1854_, 1, v___x_1851_);
lean_ctor_set(v_data_1854_, 2, v_tag_1815_);
v___x_1855_ = lean_unbox_float(v_fst_1842_);
lean_dec(v_fst_1842_);
lean_ctor_set_float(v_data_1854_, sizeof(void*)*3, v___x_1855_);
v___x_1856_ = lean_unbox_float(v_snd_1843_);
lean_dec(v_snd_1843_);
lean_ctor_set_float(v_data_1854_, sizeof(void*)*3 + 8, v___x_1856_);
lean_ctor_set_uint8(v_data_1854_, sizeof(void*)*3 + 16, v_collapsed_1814_);
v___y_1829_ = v___y_1847_;
v___y_1830_ = v_a_1848_;
v_data_1831_ = v_data_1854_;
goto v___jp_1828_;
}
}
v___jp_1857_:
{
lean_object* v_ref_1858_; lean_object* v___x_1859_; 
v_ref_1858_ = lean_ctor_get(v___y_1823_, 2);
lean_inc(v___y_1824_);
lean_inc_ref(v___y_1823_);
lean_inc(v___y_1822_);
lean_inc_ref(v___y_1821_);
lean_inc(v_fst_1826_);
v___x_1859_ = lean_apply_6(v_msg_1819_, v_fst_1826_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, lean_box(0));
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_a_1860_);
lean_dec_ref_known(v___x_1859_, 1);
v___y_1847_ = v_ref_1858_;
v_a_1848_ = v_a_1860_;
goto v___jp_1846_;
}
else
{
lean_object* v___x_1861_; 
lean_dec_ref_known(v___x_1859_, 1);
v___x_1861_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___closed__1);
v___y_1847_ = v_ref_1858_;
v_a_1848_ = v___x_1861_;
goto v___jp_1846_;
}
}
v___jp_1862_:
{
if (v_clsEnabled_1817_ == 0)
{
if (v___y_1863_ == 0)
{
lean_object* v___x_1864_; lean_object* v_traceState_1865_; lean_object* v_env_1866_; lean_object* v_nextMacroScope_1867_; lean_object* v_ngen_1868_; lean_object* v_auxDeclNGen_1869_; lean_object* v_cache_1870_; lean_object* v_recordedDeps_1871_; lean_object* v_messages_1872_; lean_object* v_infoState_1873_; lean_object* v_snapshotTasks_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1893_; 
lean_dec(v_snd_1843_);
lean_dec(v_fst_1842_);
lean_dec_ref(v_msg_1819_);
lean_dec_ref(v_tag_1815_);
lean_dec(v_cls_1813_);
v___x_1864_ = lean_st_ref_take(v___y_1824_);
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
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1876_ = v___x_1864_;
v_isShared_1877_ = v_isSharedCheck_1893_;
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
v_isShared_1877_ = v_isSharedCheck_1893_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
uint64_t v_tid_1878_; lean_object* v_traces_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1892_; 
v_tid_1878_ = lean_ctor_get_uint64(v_traceState_1865_, sizeof(void*)*1);
v_traces_1879_ = lean_ctor_get(v_traceState_1865_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v_traceState_1865_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1881_ = v_traceState_1865_;
v_isShared_1882_ = v_isSharedCheck_1892_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_traces_1879_);
lean_dec(v_traceState_1865_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1892_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1883_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1818_, v_traces_1879_);
lean_dec_ref(v_traces_1879_);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 0, v___x_1883_);
v___x_1885_ = v___x_1881_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1883_);
lean_ctor_set_uint64(v_reuseFailAlloc_1891_, sizeof(void*)*1, v_tid_1878_);
v___x_1885_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1887_; 
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 4, v___x_1885_);
v___x_1887_ = v___x_1876_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_env_1866_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v_nextMacroScope_1867_);
lean_ctor_set(v_reuseFailAlloc_1890_, 2, v_ngen_1868_);
lean_ctor_set(v_reuseFailAlloc_1890_, 3, v_auxDeclNGen_1869_);
lean_ctor_set(v_reuseFailAlloc_1890_, 4, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1890_, 5, v_cache_1870_);
lean_ctor_set(v_reuseFailAlloc_1890_, 6, v_recordedDeps_1871_);
lean_ctor_set(v_reuseFailAlloc_1890_, 7, v_messages_1872_);
lean_ctor_set(v_reuseFailAlloc_1890_, 8, v_infoState_1873_);
lean_ctor_set(v_reuseFailAlloc_1890_, 9, v_snapshotTasks_1874_);
v___x_1887_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = lean_st_ref_put(v___y_1824_, v___x_1887_);
v___x_1889_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___redArg(v_fst_1826_);
return v___x_1889_;
}
}
}
}
}
else
{
goto v___jp_1857_;
}
}
else
{
goto v___jp_1857_;
}
}
v___jp_1894_:
{
double v___x_1896_; double v___x_1897_; double v___x_1898_; uint8_t v___x_1899_; 
v___x_1896_ = lean_unbox_float(v_snd_1843_);
v___x_1897_ = lean_unbox_float(v_fst_1842_);
v___x_1898_ = lean_float_sub(v___x_1896_, v___x_1897_);
v___x_1899_ = lean_float_decLt(v___y_1895_, v___x_1898_);
v___y_1863_ = v___x_1899_;
goto v___jp_1862_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12___boxed(lean_object* v_cls_1910_, lean_object* v_collapsed_1911_, lean_object* v_tag_1912_, lean_object* v_opts_1913_, lean_object* v_clsEnabled_1914_, lean_object* v_oldTraces_1915_, lean_object* v_msg_1916_, lean_object* v_resStartStop_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
uint8_t v_collapsed_boxed_1923_; uint8_t v_clsEnabled_boxed_1924_; lean_object* v_res_1925_; 
v_collapsed_boxed_1923_ = lean_unbox(v_collapsed_1911_);
v_clsEnabled_boxed_1924_ = lean_unbox(v_clsEnabled_1914_);
v_res_1925_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12(v_cls_1910_, v_collapsed_boxed_1923_, v_tag_1912_, v_opts_1913_, v_clsEnabled_boxed_1924_, v_oldTraces_1915_, v_msg_1916_, v_resStartStop_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec_ref(v_opts_1913_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__0___redArg(lean_object* v_a_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v___x_1932_; 
v___x_1932_ = l_Lean_Meta_reduceRecMatcher_x3f(v_a_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1946_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1935_ = v___x_1932_;
v_isShared_1936_ = v_isSharedCheck_1946_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1932_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1946_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
if (lean_obj_tag(v_a_1933_) == 1)
{
lean_object* v_val_1937_; lean_object* v___x_1938_; 
lean_del_object(v___x_1935_);
lean_dec_ref(v_a_1926_);
v_val_1937_ = lean_ctor_get(v_a_1933_, 0);
lean_inc(v_val_1937_);
lean_dec_ref_known(v_a_1933_, 1);
v___x_1938_ = l_Lean_Expr_headBeta(v_val_1937_);
v_a_1926_ = v___x_1938_;
goto _start;
}
else
{
lean_object* v___x_1940_; uint8_t v___x_1941_; 
lean_dec(v_a_1933_);
lean_inc_ref(v_a_1926_);
v___x_1940_ = l_Lean_Expr_headBeta(v_a_1926_);
v___x_1941_ = lean_expr_eqv(v_a_1926_, v___x_1940_);
if (v___x_1941_ == 0)
{
lean_del_object(v___x_1935_);
lean_dec_ref(v_a_1926_);
v_a_1926_ = v___x_1940_;
goto _start;
}
else
{
lean_object* v___x_1944_; 
lean_dec_ref(v___x_1940_);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 0, v_a_1926_);
v___x_1944_ = v___x_1935_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1926_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_dec_ref(v_a_1926_);
v_a_1947_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1932_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1932_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__0___redArg___boxed(lean_object* v_a_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_a_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
return v_res_1961_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__11(void){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1981_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__8));
v___x_1982_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__10));
v___x_1983_ = l_Lean_Name_append(v___x_1982_, v___x_1981_);
return v___x_1983_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__13(void){
_start:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1985_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_1986_ = l_Lean_stringToMessageData(v___x_1985_);
return v___x_1986_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__15(void){
_start:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1988_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__14));
v___x_1989_ = l_Lean_stringToMessageData(v___x_1988_);
return v___x_1989_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__17(void){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1991_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__16));
v___x_1992_ = l_Lean_stringToMessageData(v___x_1991_);
return v___x_1992_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__19(void){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1994_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__18));
v___x_1995_ = l_Lean_stringToMessageData(v___x_1994_);
return v___x_1995_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__21(void){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__20));
v___x_1998_ = l_Lean_stringToMessageData(v___x_1997_);
return v___x_1998_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__23(void){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__22));
v___x_2001_ = l_Lean_stringToMessageData(v___x_2000_);
return v___x_2001_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__24(void){
_start:
{
lean_object* v___x_2002_; lean_object* v_dummy_2003_; 
v___x_2002_ = lean_box(0);
v_dummy_2003_ = l_Lean_Expr_sort___override(v___x_2002_);
return v_dummy_2003_;
}
}
static double _init_l_Lean_Meta_rwMatcher___closed__25(void){
_start:
{
lean_object* v___x_2004_; double v___x_2005_; 
v___x_2004_ = lean_unsigned_to_nat(1000000000u);
v___x_2005_ = lean_float_of_nat(v___x_2004_);
return v___x_2005_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__27(void){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__26));
v___x_2008_ = l_Lean_stringToMessageData(v___x_2007_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher(lean_object* v_altIdx_2009_, lean_object* v_e_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v___y_2038_; lean_object* v___x_2048_; uint8_t v___x_2049_; 
v___x_2048_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__2));
v___x_2049_ = l_Lean_Expr_isAppOf(v_e_2010_, v___x_2048_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2050_; uint8_t v___x_2051_; 
v___x_2050_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__4));
v___x_2051_ = l_Lean_Expr_isAppOf(v_e_2010_, v___x_2050_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; uint8_t v___x_2053_; lean_object* v___y_2055_; lean_object* v_proof_2056_; lean_object* v___x_2071_; lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2504_; 
v___x_2052_ = lean_box(0);
v___x_2053_ = 1;
v___x_2071_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__2___redArg(v_e_2010_, v_a_2014_);
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2074_ = v___x_2071_;
v_isShared_2075_ = v_isSharedCheck_2504_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2071_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2504_;
goto v_resetjp_2073_;
}
v___jp_2054_:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2057_, 0, v_proof_2056_);
v___x_2058_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2058_, 0, v___y_2055_);
lean_ctor_set(v___x_2058_, 1, v___x_2057_);
lean_ctor_set_uint8(v___x_2058_, sizeof(void*)*2, v___x_2053_);
v___x_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
return v___x_2059_;
}
v___jp_2060_:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2061_ = lean_box(0);
v___x_2062_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2062_, 0, v_e_2010_);
lean_ctor_set(v___x_2062_, 1, v___x_2061_);
lean_ctor_set_uint8(v___x_2062_, sizeof(void*)*2, v___x_2053_);
v___x_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
return v___x_2063_;
}
v___jp_2064_:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2065_ = lean_box(0);
v___x_2066_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2066_, 0, v_e_2010_);
lean_ctor_set(v___x_2066_, 1, v___x_2065_);
lean_ctor_set_uint8(v___x_2066_, sizeof(void*)*2, v___x_2053_);
v___x_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
return v___x_2067_;
}
v___jp_2068_:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2069_ = lean_box(0);
v___x_2070_ = l_Lean_Meta_rwMatcher___lam__0(v_e_2010_, v___x_2053_, v___x_2069_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
v___y_2038_ = v___x_2070_;
goto v___jp_2037_;
}
v_resetjp_2073_:
{
uint8_t v___x_2076_; 
v___x_2076_ = lean_unbox(v_a_2072_);
lean_dec(v_a_2072_);
if (v___x_2076_ == 0)
{
lean_object* v_toCold_2077_; lean_object* v_options_2078_; uint8_t v_hasTrace_2079_; 
lean_del_object(v___x_2074_);
lean_dec(v_altIdx_2009_);
v_toCold_2077_ = lean_ctor_get(v_a_2013_, 0);
v_options_2078_ = lean_ctor_get(v_toCold_2077_, 2);
v_hasTrace_2079_ = lean_ctor_get_uint8(v_options_2078_, sizeof(void*)*1);
if (v_hasTrace_2079_ == 0)
{
goto v___jp_2060_;
}
else
{
lean_object* v_inheritedTraceOptions_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; 
v_inheritedTraceOptions_2080_ = lean_ctor_get(v_toCold_2077_, 11);
v___x_2081_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__8));
v___x_2082_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__11, &l_Lean_Meta_rwMatcher___closed__11_once, _init_l_Lean_Meta_rwMatcher___closed__11);
v___x_2083_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2080_, v_options_2078_, v___x_2082_);
if (v___x_2083_ == 0)
{
goto v___jp_2060_;
}
else
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2084_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
lean_inc_ref(v_e_2010_);
v___x_2085_ = l_Lean_indentExpr(v_e_2010_);
v___x_2086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2084_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
v___x_2087_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(v___x_2081_, v___x_2086_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_dec_ref_known(v___x_2087_, 1);
goto v___jp_2060_;
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
lean_dec_ref(v_e_2010_);
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2087_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2087_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
}
}
else
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2096_ = l_Lean_Expr_getAppFn(v_e_2010_);
v___x_2097_ = l_Lean_Expr_constName_x21(v___x_2096_);
lean_inc(v_a_2014_);
lean_inc_ref(v_a_2013_);
lean_inc(v_a_2012_);
lean_inc_ref(v_a_2011_);
lean_inc(v___x_2097_);
v___x_2098_ = lean_get_congr_match_equations_for(v___x_2097_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2495_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2101_ = v___x_2098_;
v_isShared_2102_ = v_isSharedCheck_2495_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2495_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2103_ = lean_array_get_size(v_a_2099_);
v___x_2104_ = lean_nat_dec_lt(v_altIdx_2009_, v___x_2103_);
if (v___x_2104_ == 0)
{
lean_object* v_toCold_2105_; lean_object* v_options_2106_; uint8_t v_hasTrace_2107_; 
lean_del_object(v___x_2101_);
lean_dec(v_a_2099_);
lean_dec_ref(v___x_2096_);
v_toCold_2105_ = lean_ctor_get(v_a_2013_, 0);
v_options_2106_ = lean_ctor_get(v_toCold_2105_, 2);
v_hasTrace_2107_ = lean_ctor_get_uint8(v_options_2106_, sizeof(void*)*1);
if (v_hasTrace_2107_ == 0)
{
lean_dec(v___x_2097_);
lean_del_object(v___x_2074_);
lean_dec(v_altIdx_2009_);
goto v___jp_2064_;
}
else
{
lean_object* v_inheritedTraceOptions_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v_inheritedTraceOptions_2108_ = lean_ctor_get(v_toCold_2105_, 11);
v___x_2109_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__8));
v___x_2110_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__11, &l_Lean_Meta_rwMatcher___closed__11_once, _init_l_Lean_Meta_rwMatcher___closed__11);
v___x_2111_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2108_, v_options_2106_, v___x_2110_);
if (v___x_2111_ == 0)
{
lean_dec(v___x_2097_);
lean_del_object(v___x_2074_);
lean_dec(v_altIdx_2009_);
goto v___jp_2064_;
}
else
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2115_; 
v___x_2112_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__15, &l_Lean_Meta_rwMatcher___closed__15_once, _init_l_Lean_Meta_rwMatcher___closed__15);
v___x_2113_ = l_Nat_reprFast(v_altIdx_2009_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set_tag(v___x_2074_, 3);
lean_ctor_set(v___x_2074_, 0, v___x_2113_);
v___x_2115_ = v___x_2074_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2116_ = l_Lean_MessageData_ofFormat(v___x_2115_);
v___x_2117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2112_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
v___x_2118_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__17, &l_Lean_Meta_rwMatcher___closed__17_once, _init_l_Lean_Meta_rwMatcher___closed__17);
v___x_2119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2117_);
lean_ctor_set(v___x_2119_, 1, v___x_2118_);
v___x_2120_ = l_Nat_reprFast(v___x_2103_);
v___x_2121_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
v___x_2122_ = l_Lean_MessageData_ofFormat(v___x_2121_);
v___x_2123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2119_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
v___x_2124_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__19, &l_Lean_Meta_rwMatcher___closed__19_once, _init_l_Lean_Meta_rwMatcher___closed__19);
v___x_2125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2123_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = l_Lean_MessageData_ofConstName(v___x_2097_, v___x_2104_);
v___x_2127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2125_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
v___x_2128_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(v___x_2109_, v___x_2127_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_dec_ref_known(v___x_2128_, 1);
goto v___jp_2064_;
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
lean_dec_ref(v_e_2010_);
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2128_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2128_);
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
}
else
{
lean_object* v_toCold_2138_; lean_object* v_options_2139_; lean_object* v_inheritedTraceOptions_2140_; uint8_t v_hasTrace_2141_; lean_object* v_nargs_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v_a_2146_; lean_object* v___y_2177_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v_dummy_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
lean_dec(v___x_2097_);
v_toCold_2138_ = lean_ctor_get(v_a_2013_, 0);
v_options_2139_ = lean_ctor_get(v_toCold_2138_, 2);
v_inheritedTraceOptions_2140_ = lean_ctor_get(v_toCold_2138_, 11);
v_hasTrace_2141_ = lean_ctor_get_uint8(v_options_2139_, sizeof(void*)*1);
v_nargs_2142_ = l_Lean_Expr_getAppNumArgs(v_e_2010_);
v___x_2143_ = lean_array_get(v___x_2052_, v_a_2099_, v_altIdx_2009_);
lean_dec(v_altIdx_2009_);
lean_dec(v_a_2099_);
v___x_2144_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__8));
v___x_2179_ = l_Lean_Expr_constLevels_x21(v___x_2096_);
lean_dec_ref(v___x_2096_);
lean_inc(v___x_2143_);
v___x_2180_ = l_Lean_mkConst(v___x_2143_, v___x_2179_);
v_dummy_2181_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__24, &l_Lean_Meta_rwMatcher___closed__24_once, _init_l_Lean_Meta_rwMatcher___closed__24);
lean_inc(v_nargs_2142_);
v___x_2182_ = lean_mk_array(v_nargs_2142_, v_dummy_2181_);
v___x_2183_ = lean_unsigned_to_nat(1u);
v___x_2184_ = lean_nat_sub(v_nargs_2142_, v___x_2183_);
lean_dec(v_nargs_2142_);
lean_inc_ref(v_e_2010_);
v___x_2185_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2010_, v___x_2182_, v___x_2184_);
v___x_2186_ = l_Lean_mkAppN(v___x_2180_, v___x_2185_);
lean_dec_ref(v___x_2185_);
if (v_hasTrace_2141_ == 0)
{
lean_object* v___x_2187_; 
lean_del_object(v___x_2074_);
lean_inc(v_a_2014_);
lean_inc_ref(v_a_2013_);
lean_inc(v_a_2012_);
lean_inc_ref(v_a_2011_);
lean_inc_ref(v___x_2186_);
v___x_2187_ = lean_infer_type(v___x_2186_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_a_2188_; uint8_t v___x_2189_; lean_object* v___x_2190_; 
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_a_2188_);
lean_dec_ref_known(v___x_2187_, 1);
v___x_2189_ = 0;
v___x_2190_ = l_Lean_Meta_forallMetaTelescope(v_a_2188_, v___x_2189_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v_snd_2192_; lean_object* v_fst_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2329_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2191_);
lean_dec_ref_known(v___x_2190_, 1);
v_snd_2192_ = lean_ctor_get(v_a_2191_, 1);
v_fst_2193_ = lean_ctor_get(v_a_2191_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v_a_2191_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2195_ = v_a_2191_;
v_isShared_2196_ = v_isSharedCheck_2329_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_snd_2192_);
lean_inc(v_fst_2193_);
lean_dec(v_a_2191_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2329_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v_snd_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2327_; 
v_snd_2197_ = lean_ctor_get(v_snd_2192_, 1);
v_isSharedCheck_2327_ = !lean_is_exclusive(v_snd_2192_);
if (v_isSharedCheck_2327_ == 0)
{
lean_object* v_unused_2328_; 
v_unused_2328_ = lean_ctor_get(v_snd_2192_, 0);
lean_dec(v_unused_2328_);
v___x_2199_ = v_snd_2192_;
v_isShared_2200_ = v_isSharedCheck_2327_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_snd_2197_);
lean_dec(v_snd_2192_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2327_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2201_; lean_object* v___y_2203_; uint8_t v___y_2204_; lean_object* v___y_2205_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; uint8_t v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v_a_2242_; size_t v_sz_2258_; size_t v___x_2259_; lean_object* v___x_2260_; lean_object* v___y_2262_; uint8_t v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; uint8_t v_fst_2281_; lean_object* v_fst_2282_; lean_object* v_snd_2283_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___x_2307_; lean_object* v___x_2308_; uint8_t v___x_2309_; 
v___x_2201_ = l_Lean_mkAppN(v___x_2186_, v_fst_2193_);
v_sz_2258_ = lean_array_size(v_fst_2193_);
v___x_2259_ = ((size_t)0ULL);
v___x_2260_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__4(v_sz_2258_, v___x_2259_, v_fst_2193_);
v___x_2307_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_2308_ = lean_unsigned_to_nat(4u);
v___x_2309_ = l_Lean_Expr_isAppOfArity(v_snd_2197_, v___x_2307_, v___x_2308_);
if (v___x_2309_ == 0)
{
lean_object* v___x_2310_; lean_object* v___x_2311_; uint8_t v___x_2312_; 
v___x_2310_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_2311_ = lean_unsigned_to_nat(3u);
v___x_2312_ = l_Lean_Expr_isAppOfArity(v_snd_2197_, v___x_2310_, v___x_2311_);
if (v___x_2312_ == 0)
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v_a_2319_; 
lean_dec_ref(v___x_2260_);
lean_dec_ref(v___x_2201_);
lean_del_object(v___x_2199_);
lean_dec(v_snd_2197_);
lean_del_object(v___x_2195_);
v___x_2313_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
lean_inc(v___x_2143_);
v___x_2314_ = l_Lean_MessageData_ofConstName(v___x_2143_, v___x_2051_);
v___x_2315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2313_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___x_2316_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2315_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_2317_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref(v___x_2318_);
v_a_2146_ = v_a_2319_;
goto v___jp_2145_;
}
else
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2320_ = l_Lean_Expr_appFn_x21(v_snd_2197_);
v___x_2321_ = l_Lean_Expr_appArg_x21(v___x_2320_);
lean_dec_ref(v___x_2320_);
v___x_2322_ = l_Lean_Expr_appArg_x21(v_snd_2197_);
lean_dec(v_snd_2197_);
v_fst_2281_ = v___x_2051_;
v_fst_2282_ = v___x_2321_;
v_snd_2283_ = v___x_2322_;
v___y_2284_ = v_a_2011_;
v___y_2285_ = v_a_2012_;
v___y_2286_ = v_a_2013_;
v___y_2287_ = v_a_2014_;
goto v___jp_2280_;
}
}
else
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2323_ = l_Lean_Expr_appFn_x21(v_snd_2197_);
v___x_2324_ = l_Lean_Expr_appFn_x21(v___x_2323_);
lean_dec_ref(v___x_2323_);
v___x_2325_ = l_Lean_Expr_appArg_x21(v___x_2324_);
lean_dec_ref(v___x_2324_);
v___x_2326_ = l_Lean_Expr_appArg_x21(v_snd_2197_);
lean_dec(v_snd_2197_);
v_fst_2281_ = v___x_2053_;
v_fst_2282_ = v___x_2325_;
v_snd_2283_ = v___x_2326_;
v___y_2284_ = v_a_2011_;
v___y_2285_ = v_a_2012_;
v___y_2286_ = v_a_2013_;
v___y_2287_ = v_a_2014_;
goto v___jp_2280_;
}
v___jp_2202_:
{
lean_object* v___x_2209_; lean_object* v_a_2210_; lean_object* v___x_2211_; 
v___x_2209_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___y_2203_, v___y_2206_);
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2210_);
lean_dec_ref(v___x_2209_);
v___x_2211_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2201_, v___y_2206_);
if (v___y_2204_ == 0)
{
lean_object* v_a_2212_; 
lean_del_object(v___x_2199_);
lean_del_object(v___x_2195_);
lean_dec(v___x_2143_);
lean_del_object(v___x_2101_);
lean_dec_ref(v_e_2010_);
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
lean_inc(v_a_2212_);
lean_dec_ref(v___x_2211_);
v___y_2055_ = v_a_2210_;
v_proof_2056_ = v_a_2212_;
goto v___jp_2054_;
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2214_; 
v_a_2213_ = lean_ctor_get(v___x_2211_, 0);
lean_inc_n(v_a_2213_, 2);
lean_dec_ref(v___x_2211_);
v___x_2214_ = l_Lean_Meta_mkEqOfHEq(v_a_2213_, v___x_2053_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; 
lean_dec(v_a_2213_);
lean_del_object(v___x_2199_);
lean_del_object(v___x_2195_);
lean_dec(v___x_2143_);
lean_del_object(v___x_2101_);
lean_dec_ref(v_e_2010_);
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
lean_dec_ref_known(v___x_2214_, 1);
v___y_2055_ = v_a_2210_;
v_proof_2056_ = v_a_2215_;
goto v___jp_2054_;
}
else
{
lean_object* v_a_2216_; uint8_t v___x_2217_; 
lean_dec(v_a_2210_);
v_a_2216_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2216_);
lean_dec_ref_known(v___x_2214_, 1);
v___x_2217_ = l_Lean_Exception_isInterrupt(v_a_2216_);
if (v___x_2217_ == 0)
{
uint8_t v___x_2218_; 
lean_inc(v_a_2216_);
v___x_2218_ = l_Lean_Exception_isRuntime(v_a_2216_);
if (v___x_2218_ == 0)
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2222_; 
v___x_2219_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_2220_ = l_Lean_MessageData_ofExpr(v_a_2213_);
if (v_isShared_2200_ == 0)
{
lean_ctor_set_tag(v___x_2199_, 7);
lean_ctor_set(v___x_2199_, 1, v___x_2220_);
lean_ctor_set(v___x_2199_, 0, v___x_2219_);
v___x_2222_ = v___x_2199_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2219_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v___x_2220_);
v___x_2222_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2223_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
if (v_isShared_2196_ == 0)
{
lean_ctor_set_tag(v___x_2195_, 7);
lean_ctor_set(v___x_2195_, 1, v___x_2223_);
lean_ctor_set(v___x_2195_, 0, v___x_2222_);
v___x_2225_ = v___x_2195_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2222_);
lean_ctor_set(v_reuseFailAlloc_2233_, 1, v___x_2223_);
v___x_2225_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v_a_2232_; 
v___x_2226_ = l_Lean_Exception_toMessageData(v_a_2216_);
v___x_2227_ = l_Lean_indentD(v___x_2226_);
v___x_2228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2225_);
lean_ctor_set(v___x_2228_, 1, v___x_2227_);
v___x_2229_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_2230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2228_);
lean_ctor_set(v___x_2230_, 1, v___x_2229_);
v___x_2231_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_2230_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2232_);
lean_dec_ref(v___x_2231_);
v_a_2146_ = v_a_2232_;
goto v___jp_2145_;
}
}
}
else
{
lean_dec(v_a_2213_);
lean_del_object(v___x_2199_);
lean_del_object(v___x_2195_);
v_a_2146_ = v_a_2216_;
goto v___jp_2145_;
}
}
else
{
lean_dec(v_a_2213_);
lean_del_object(v___x_2199_);
lean_del_object(v___x_2195_);
v_a_2146_ = v_a_2216_;
goto v___jp_2145_;
}
}
}
}
v___jp_2235_:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; uint8_t v___x_2245_; 
v___x_2243_ = lean_array_get_size(v_a_2242_);
v___x_2244_ = lean_unsigned_to_nat(0u);
v___x_2245_ = lean_nat_dec_eq(v___x_2243_, v___x_2244_);
if (v___x_2245_ == 0)
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v_a_2257_; 
lean_dec_ref(v___y_2236_);
lean_dec_ref(v___x_2201_);
lean_del_object(v___x_2199_);
lean_del_object(v___x_2195_);
v___x_2246_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
lean_inc(v___x_2143_);
v___x_2247_ = l_Lean_MessageData_ofConstName(v___x_2143_, v___x_2245_);
v___x_2248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2246_);
lean_ctor_set(v___x_2248_, 1, v___x_2247_);
v___x_2249_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_2250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2248_);
lean_ctor_set(v___x_2250_, 1, v___x_2249_);
v___x_2251_ = lean_array_to_list(v_a_2242_);
v___x_2252_ = lean_box(0);
v___x_2253_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_2251_, v___x_2252_);
v___x_2254_ = l_Lean_MessageData_ofList(v___x_2253_);
v___x_2255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2250_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
v___x_2256_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_2255_, v___y_2241_, v___y_2238_, v___y_2237_, v___y_2240_);
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_a_2257_);
lean_dec_ref(v___x_2256_);
v_a_2146_ = v_a_2257_;
goto v___jp_2145_;
}
else
{
lean_dec_ref(v_a_2242_);
v___y_2203_ = v___y_2236_;
v___y_2204_ = v___y_2239_;
v___y_2205_ = v___y_2241_;
v___y_2206_ = v___y_2238_;
v___y_2207_ = v___y_2237_;
v___y_2208_ = v___y_2240_;
goto v___jp_2202_;
}
}
v___jp_2261_:
{
lean_object* v___x_2268_; size_t v_sz_2269_; lean_object* v___x_2270_; 
v___x_2268_ = lean_box(0);
v_sz_2269_ = lean_array_size(v___x_2260_);
v___x_2270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8(v___x_2260_, v_sz_2269_, v___x_2259_, v___x_2268_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; 
lean_dec_ref_known(v___x_2270_, 1);
v___x_2271_ = lean_unsigned_to_nat(0u);
v___x_2272_ = lean_array_get_size(v___x_2260_);
v___x_2273_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_2274_ = lean_nat_dec_lt(v___x_2271_, v___x_2272_);
if (v___x_2274_ == 0)
{
lean_dec_ref(v___x_2260_);
v___y_2236_ = v___y_2262_;
v___y_2237_ = v___y_2266_;
v___y_2238_ = v___y_2265_;
v___y_2239_ = v___y_2263_;
v___y_2240_ = v___y_2267_;
v___y_2241_ = v___y_2264_;
v_a_2242_ = v___x_2273_;
goto v___jp_2235_;
}
else
{
size_t v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = lean_usize_of_nat(v___x_2272_);
v___x_2276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__9(v___x_2260_, v___x_2259_, v___x_2275_, v___x_2273_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
lean_dec_ref(v___x_2260_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v_a_2277_; 
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2277_);
lean_dec_ref_known(v___x_2276_, 1);
v___y_2236_ = v___y_2262_;
v___y_2237_ = v___y_2266_;
v___y_2238_ = v___y_2265_;
v___y_2239_ = v___y_2263_;
v___y_2240_ = v___y_2267_;
v___y_2241_ = v___y_2264_;
v_a_2242_ = v_a_2277_;
goto v___jp_2235_;
}
else
{
lean_object* v_a_2278_; 
lean_dec_ref(v___y_2262_);
lean_dec_ref(v___x_2201_);
lean_del_object(v___x_2199_);
lean_del_object(v___x_2195_);
v_a_2278_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2278_);
lean_dec_ref_known(v___x_2276_, 1);
v_a_2146_ = v_a_2278_;
goto v___jp_2145_;
}
}
}
else
{
lean_object* v_a_2279_; 
lean_dec_ref(v___y_2262_);
lean_dec_ref(v___x_2260_);
lean_dec_ref(v___x_2201_);
lean_del_object(v___x_2199_);
lean_del_object(v___x_2195_);
v_a_2279_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2279_);
lean_dec_ref_known(v___x_2270_, 1);
v_a_2146_ = v_a_2279_;
goto v___jp_2145_;
}
}
v___jp_2280_:
{
lean_object* v___x_2288_; 
lean_inc_ref(v_fst_2282_);
lean_inc_ref(v_e_2010_);
v___x_2288_ = l_Lean_Meta_isExprDefEq(v_e_2010_, v_fst_2282_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; uint8_t v___x_2290_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_a_2289_);
lean_dec_ref_known(v___x_2288_, 1);
v___x_2290_ = lean_unbox(v_a_2289_);
lean_dec(v_a_2289_);
if (v___x_2290_ == 0)
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v_a_2305_; 
lean_dec_ref(v_snd_2283_);
lean_dec_ref(v___x_2260_);
lean_dec_ref(v___x_2201_);
lean_del_object(v___x_2199_);
lean_del_object(v___x_2195_);
v___x_2291_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_2292_ = l_Lean_MessageData_ofExpr(v_fst_2282_);
v___x_2293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2291_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_2295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2293_);
lean_ctor_set(v___x_2295_, 1, v___x_2294_);
lean_inc(v___x_2143_);
v___x_2296_ = l_Lean_MessageData_ofConstName(v___x_2143_, v___x_2051_);
v___x_2297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2295_);
lean_ctor_set(v___x_2297_, 1, v___x_2296_);
v___x_2298_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_2299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2297_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
lean_inc_ref(v_e_2010_);
v___x_2300_ = l_Lean_MessageData_ofExpr(v_e_2010_);
v___x_2301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2299_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__8___closed__3);
v___x_2303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2301_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
v___x_2304_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v___x_2303_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2305_);
lean_dec_ref(v___x_2304_);
v_a_2146_ = v_a_2305_;
goto v___jp_2145_;
}
else
{
lean_dec_ref(v_fst_2282_);
v___y_2262_ = v_snd_2283_;
v___y_2263_ = v_fst_2281_;
v___y_2264_ = v___y_2284_;
v___y_2265_ = v___y_2285_;
v___y_2266_ = v___y_2286_;
v___y_2267_ = v___y_2287_;
goto v___jp_2261_;
}
}
else
{
lean_object* v_a_2306_; 
lean_dec_ref(v_snd_2283_);
lean_dec_ref(v_fst_2282_);
lean_dec_ref(v___x_2260_);
lean_dec_ref(v___x_2201_);
lean_del_object(v___x_2199_);
lean_del_object(v___x_2195_);
v_a_2306_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2288_, 1);
v_a_2146_ = v_a_2306_;
goto v___jp_2145_;
}
}
}
}
}
else
{
lean_object* v_a_2330_; 
lean_dec_ref(v___x_2186_);
v_a_2330_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2330_);
lean_dec_ref_known(v___x_2190_, 1);
v_a_2146_ = v_a_2330_;
goto v___jp_2145_;
}
}
else
{
lean_object* v_a_2331_; 
lean_dec_ref(v___x_2186_);
v_a_2331_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_a_2331_);
lean_dec_ref_known(v___x_2187_, 1);
v_a_2146_ = v_a_2331_;
goto v___jp_2145_;
}
}
else
{
lean_object* v___x_2332_; lean_object* v___f_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; uint8_t v___x_2336_; lean_object* v___y_2338_; lean_object* v___y_2339_; lean_object* v_a_2340_; lean_object* v___y_2353_; lean_object* v___y_2354_; lean_object* v_a_2355_; lean_object* v___y_2360_; lean_object* v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v_a_2375_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v_a_2387_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2392_; 
v___x_2332_ = lean_box(v___x_2051_);
lean_inc_ref(v_e_2010_);
lean_inc(v___x_2143_);
v___f_2333_ = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__1___boxed), 9, 3);
lean_closure_set(v___f_2333_, 0, v___x_2143_);
lean_closure_set(v___f_2333_, 1, v___x_2332_);
lean_closure_set(v___f_2333_, 2, v_e_2010_);
v___x_2334_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3___closed__1));
v___x_2335_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__11, &l_Lean_Meta_rwMatcher___closed__11_once, _init_l_Lean_Meta_rwMatcher___closed__11);
v___x_2336_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2140_, v_options_2139_, v___x_2335_);
if (v___x_2336_ == 0)
{
lean_object* v___x_2465_; uint8_t v___x_2466_; 
v___x_2465_ = l_Lean_trace_profiler;
v___x_2466_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11(v_options_2139_, v___x_2465_);
if (v___x_2466_ == 0)
{
lean_object* v___x_2467_; 
lean_dec_ref(v___f_2333_);
lean_del_object(v___x_2074_);
lean_inc(v_a_2014_);
lean_inc_ref(v_a_2013_);
lean_inc(v_a_2012_);
lean_inc_ref(v_a_2011_);
lean_inc_ref(v___x_2186_);
v___x_2467_ = lean_infer_type(v___x_2186_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; uint8_t v___x_2469_; lean_object* v___x_2470_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_a_2468_);
lean_dec_ref_known(v___x_2467_, 1);
v___x_2469_ = 0;
v___x_2470_ = l_Lean_Meta_forallMetaTelescope(v_a_2468_, v___x_2469_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v_a_2471_; lean_object* v_snd_2472_; 
v_a_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_a_2471_);
lean_dec_ref_known(v___x_2470_, 1);
v_snd_2472_ = lean_ctor_get(v_a_2471_, 1);
lean_inc(v_snd_2472_);
if (v___x_2336_ == 0)
{
lean_object* v_fst_2473_; lean_object* v_snd_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v_fst_2473_ = lean_ctor_get(v_a_2471_, 0);
lean_inc(v_fst_2473_);
lean_dec(v_a_2471_);
v_snd_2474_ = lean_ctor_get(v_snd_2472_, 1);
lean_inc(v_snd_2474_);
lean_dec(v_snd_2472_);
v___x_2475_ = lean_box(0);
lean_inc_ref(v_e_2010_);
lean_inc(v___x_2143_);
v___x_2476_ = l_Lean_Meta_rwMatcher___lam__4(v___x_2053_, v___x_2186_, v_fst_2473_, v___x_2143_, v_e_2010_, v___x_2051_, v_snd_2474_, v___x_2475_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
lean_dec(v_snd_2474_);
v___y_2177_ = v___x_2476_;
goto v___jp_2176_;
}
else
{
lean_object* v_fst_2477_; lean_object* v_snd_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2491_; 
v_fst_2477_ = lean_ctor_get(v_a_2471_, 0);
lean_inc(v_fst_2477_);
lean_dec(v_a_2471_);
v_snd_2478_ = lean_ctor_get(v_snd_2472_, 1);
v_isSharedCheck_2491_ = !lean_is_exclusive(v_snd_2472_);
if (v_isSharedCheck_2491_ == 0)
{
lean_object* v_unused_2492_; 
v_unused_2492_ = lean_ctor_get(v_snd_2472_, 0);
lean_dec(v_unused_2492_);
v___x_2480_ = v_snd_2472_;
v_isShared_2481_ = v_isSharedCheck_2491_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_snd_2478_);
lean_dec(v_snd_2472_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2491_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2485_; 
v___x_2482_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__27, &l_Lean_Meta_rwMatcher___closed__27_once, _init_l_Lean_Meta_rwMatcher___closed__27);
lean_inc(v_snd_2478_);
v___x_2483_ = l_Lean_indentExpr(v_snd_2478_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set_tag(v___x_2480_, 7);
lean_ctor_set(v___x_2480_, 1, v___x_2483_);
lean_ctor_set(v___x_2480_, 0, v___x_2482_);
v___x_2485_ = v___x_2480_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2482_);
lean_ctor_set(v_reuseFailAlloc_2490_, 1, v___x_2483_);
v___x_2485_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2486_; 
v___x_2486_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(v___x_2144_, v___x_2485_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_a_2487_; lean_object* v___x_2488_; 
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_a_2487_);
lean_dec_ref_known(v___x_2486_, 1);
lean_inc_ref(v_e_2010_);
lean_inc(v___x_2143_);
v___x_2488_ = l_Lean_Meta_rwMatcher___lam__4(v___x_2053_, v___x_2186_, v_fst_2477_, v___x_2143_, v_e_2010_, v___x_2051_, v_snd_2478_, v_a_2487_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
lean_dec(v_snd_2478_);
v___y_2177_ = v___x_2488_;
goto v___jp_2176_;
}
else
{
lean_object* v_a_2489_; 
lean_dec(v_snd_2478_);
lean_dec(v_fst_2477_);
lean_dec_ref(v___x_2186_);
v_a_2489_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_a_2489_);
lean_dec_ref_known(v___x_2486_, 1);
v_a_2146_ = v_a_2489_;
goto v___jp_2145_;
}
}
}
}
}
else
{
lean_object* v_a_2493_; 
lean_dec_ref(v___x_2186_);
v_a_2493_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_a_2493_);
lean_dec_ref_known(v___x_2470_, 1);
v_a_2146_ = v_a_2493_;
goto v___jp_2145_;
}
}
else
{
lean_object* v_a_2494_; 
lean_dec_ref(v___x_2186_);
v_a_2494_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_a_2494_);
lean_dec_ref_known(v___x_2467_, 1);
v_a_2146_ = v_a_2494_;
goto v___jp_2145_;
}
}
else
{
goto v___jp_2402_;
}
}
else
{
goto v___jp_2402_;
}
v___jp_2337_:
{
lean_object* v___x_2341_; double v___x_2342_; double v___x_2343_; double v___x_2344_; double v___x_2345_; double v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2341_ = lean_io_mono_nanos_now();
v___x_2342_ = lean_float_of_nat(v___y_2339_);
v___x_2343_ = lean_float_once(&l_Lean_Meta_rwMatcher___closed__25, &l_Lean_Meta_rwMatcher___closed__25_once, _init_l_Lean_Meta_rwMatcher___closed__25);
v___x_2344_ = lean_float_div(v___x_2342_, v___x_2343_);
v___x_2345_ = lean_float_of_nat(v___x_2341_);
v___x_2346_ = lean_float_div(v___x_2345_, v___x_2343_);
v___x_2347_ = lean_box_float(v___x_2344_);
v___x_2348_ = lean_box_float(v___x_2346_);
v___x_2349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2347_);
lean_ctor_set(v___x_2349_, 1, v___x_2348_);
v___x_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2350_, 0, v_a_2340_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
v___x_2351_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12(v___x_2144_, v___x_2053_, v___x_2334_, v_options_2139_, v___x_2336_, v___y_2338_, v___f_2333_, v___x_2350_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
v___y_2177_ = v___x_2351_;
goto v___jp_2176_;
}
v___jp_2352_:
{
lean_object* v___x_2357_; 
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 0, v_a_2355_);
v___x_2357_ = v___x_2074_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2355_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
v___y_2338_ = v___y_2353_;
v___y_2339_ = v___y_2354_;
v_a_2340_ = v___x_2357_;
goto v___jp_2337_;
}
}
v___jp_2359_:
{
if (lean_obj_tag(v___y_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
lean_del_object(v___x_2074_);
v_a_2363_ = lean_ctor_get(v___y_2362_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___y_2362_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___y_2362_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___y_2362_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
lean_ctor_set_tag(v___x_2365_, 1);
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
v___y_2338_ = v___y_2360_;
v___y_2339_ = v___y_2361_;
v_a_2340_ = v___x_2368_;
goto v___jp_2337_;
}
}
}
else
{
lean_object* v_a_2371_; 
v_a_2371_ = lean_ctor_get(v___y_2362_, 0);
lean_inc(v_a_2371_);
lean_dec_ref_known(v___y_2362_, 1);
v___y_2353_ = v___y_2360_;
v___y_2354_ = v___y_2361_;
v_a_2355_ = v_a_2371_;
goto v___jp_2352_;
}
}
v___jp_2372_:
{
lean_object* v___x_2376_; double v___x_2377_; double v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2376_ = lean_io_get_num_heartbeats();
v___x_2377_ = lean_float_of_nat(v___y_2374_);
v___x_2378_ = lean_float_of_nat(v___x_2376_);
v___x_2379_ = lean_box_float(v___x_2377_);
v___x_2380_ = lean_box_float(v___x_2378_);
v___x_2381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2379_);
lean_ctor_set(v___x_2381_, 1, v___x_2380_);
v___x_2382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2382_, 0, v_a_2375_);
lean_ctor_set(v___x_2382_, 1, v___x_2381_);
v___x_2383_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12(v___x_2144_, v___x_2053_, v___x_2334_, v_options_2139_, v___x_2336_, v___y_2373_, v___f_2333_, v___x_2382_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
v___y_2177_ = v___x_2383_;
goto v___jp_2176_;
}
v___jp_2384_:
{
lean_object* v___x_2388_; 
v___x_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2388_, 0, v_a_2387_);
v___y_2373_ = v___y_2385_;
v___y_2374_ = v___y_2386_;
v_a_2375_ = v___x_2388_;
goto v___jp_2372_;
}
v___jp_2389_:
{
if (lean_obj_tag(v___y_2392_) == 0)
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
v_a_2393_ = lean_ctor_get(v___y_2392_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___y_2392_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___y_2392_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___y_2392_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
lean_ctor_set_tag(v___x_2395_, 1);
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
v___y_2373_ = v___y_2390_;
v___y_2374_ = v___y_2391_;
v_a_2375_ = v___x_2398_;
goto v___jp_2372_;
}
}
}
else
{
lean_object* v_a_2401_; 
v_a_2401_ = lean_ctor_get(v___y_2392_, 0);
lean_inc(v_a_2401_);
lean_dec_ref_known(v___y_2392_, 1);
v___y_2385_ = v___y_2390_;
v___y_2386_ = v___y_2391_;
v_a_2387_ = v_a_2401_;
goto v___jp_2384_;
}
}
v___jp_2402_:
{
lean_object* v___x_2403_; lean_object* v_a_2404_; lean_object* v___x_2405_; uint8_t v___x_2406_; 
v___x_2403_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__10___redArg(v_a_2014_);
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_a_2404_);
lean_dec_ref(v___x_2403_);
v___x_2405_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2406_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__11(v_options_2139_, v___x_2405_);
if (v___x_2406_ == 0)
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = lean_io_mono_nanos_now();
lean_inc(v_a_2014_);
lean_inc_ref(v_a_2013_);
lean_inc(v_a_2012_);
lean_inc_ref(v_a_2011_);
lean_inc_ref(v___x_2186_);
v___x_2408_ = lean_infer_type(v___x_2186_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; uint8_t v___x_2410_; lean_object* v___x_2411_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_a_2409_);
lean_dec_ref_known(v___x_2408_, 1);
v___x_2410_ = 0;
v___x_2411_ = l_Lean_Meta_forallMetaTelescope(v_a_2409_, v___x_2410_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; lean_object* v_snd_2413_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2412_);
lean_dec_ref_known(v___x_2411_, 1);
v_snd_2413_ = lean_ctor_get(v_a_2412_, 1);
lean_inc(v_snd_2413_);
if (v___x_2336_ == 0)
{
lean_object* v_fst_2414_; lean_object* v_snd_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v_fst_2414_ = lean_ctor_get(v_a_2412_, 0);
lean_inc(v_fst_2414_);
lean_dec(v_a_2412_);
v_snd_2415_ = lean_ctor_get(v_snd_2413_, 1);
lean_inc(v_snd_2415_);
lean_dec(v_snd_2413_);
v___x_2416_ = lean_box(0);
lean_inc_ref(v_e_2010_);
lean_inc(v___x_2143_);
v___x_2417_ = l_Lean_Meta_rwMatcher___lam__2(v___x_2053_, v___x_2186_, v_fst_2414_, v___x_2143_, v_e_2010_, v___x_2051_, v_snd_2415_, v___x_2416_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
lean_dec(v_snd_2415_);
v___y_2360_ = v_a_2404_;
v___y_2361_ = v___x_2407_;
v___y_2362_ = v___x_2417_;
goto v___jp_2359_;
}
else
{
lean_object* v_fst_2418_; lean_object* v_snd_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2432_; 
v_fst_2418_ = lean_ctor_get(v_a_2412_, 0);
lean_inc(v_fst_2418_);
lean_dec(v_a_2412_);
v_snd_2419_ = lean_ctor_get(v_snd_2413_, 1);
v_isSharedCheck_2432_ = !lean_is_exclusive(v_snd_2413_);
if (v_isSharedCheck_2432_ == 0)
{
lean_object* v_unused_2433_; 
v_unused_2433_ = lean_ctor_get(v_snd_2413_, 0);
lean_dec(v_unused_2433_);
v___x_2421_ = v_snd_2413_;
v_isShared_2422_ = v_isSharedCheck_2432_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_snd_2419_);
lean_dec(v_snd_2413_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2432_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2426_; 
v___x_2423_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__27, &l_Lean_Meta_rwMatcher___closed__27_once, _init_l_Lean_Meta_rwMatcher___closed__27);
lean_inc(v_snd_2419_);
v___x_2424_ = l_Lean_indentExpr(v_snd_2419_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set_tag(v___x_2421_, 7);
lean_ctor_set(v___x_2421_, 1, v___x_2424_);
lean_ctor_set(v___x_2421_, 0, v___x_2423_);
v___x_2426_ = v___x_2421_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2423_);
lean_ctor_set(v_reuseFailAlloc_2431_, 1, v___x_2424_);
v___x_2426_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
lean_object* v___x_2427_; 
v___x_2427_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(v___x_2144_, v___x_2426_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v_a_2428_; lean_object* v___x_2429_; 
v_a_2428_ = lean_ctor_get(v___x_2427_, 0);
lean_inc(v_a_2428_);
lean_dec_ref_known(v___x_2427_, 1);
lean_inc_ref(v_e_2010_);
lean_inc(v___x_2143_);
v___x_2429_ = l_Lean_Meta_rwMatcher___lam__2(v___x_2053_, v___x_2186_, v_fst_2418_, v___x_2143_, v_e_2010_, v___x_2051_, v_snd_2419_, v_a_2428_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
lean_dec(v_snd_2419_);
v___y_2360_ = v_a_2404_;
v___y_2361_ = v___x_2407_;
v___y_2362_ = v___x_2429_;
goto v___jp_2359_;
}
else
{
lean_object* v_a_2430_; 
lean_dec(v_snd_2419_);
lean_dec(v_fst_2418_);
lean_dec_ref(v___x_2186_);
v_a_2430_ = lean_ctor_get(v___x_2427_, 0);
lean_inc(v_a_2430_);
lean_dec_ref_known(v___x_2427_, 1);
v___y_2353_ = v_a_2404_;
v___y_2354_ = v___x_2407_;
v_a_2355_ = v_a_2430_;
goto v___jp_2352_;
}
}
}
}
}
else
{
lean_object* v_a_2434_; 
lean_dec_ref(v___x_2186_);
v_a_2434_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2434_);
lean_dec_ref_known(v___x_2411_, 1);
v___y_2353_ = v_a_2404_;
v___y_2354_ = v___x_2407_;
v_a_2355_ = v_a_2434_;
goto v___jp_2352_;
}
}
else
{
lean_object* v_a_2435_; 
lean_dec_ref(v___x_2186_);
v_a_2435_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_a_2435_);
lean_dec_ref_known(v___x_2408_, 1);
v___y_2353_ = v_a_2404_;
v___y_2354_ = v___x_2407_;
v_a_2355_ = v_a_2435_;
goto v___jp_2352_;
}
}
else
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
lean_del_object(v___x_2074_);
v___x_2436_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2014_);
lean_inc_ref(v_a_2013_);
lean_inc(v_a_2012_);
lean_inc_ref(v_a_2011_);
lean_inc_ref(v___x_2186_);
v___x_2437_ = lean_infer_type(v___x_2186_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; uint8_t v___x_2439_; lean_object* v___x_2440_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref_known(v___x_2437_, 1);
v___x_2439_ = 0;
v___x_2440_ = l_Lean_Meta_forallMetaTelescope(v_a_2438_, v___x_2439_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; lean_object* v_snd_2442_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_a_2441_);
lean_dec_ref_known(v___x_2440_, 1);
v_snd_2442_ = lean_ctor_get(v_a_2441_, 1);
lean_inc(v_snd_2442_);
if (v___x_2336_ == 0)
{
lean_object* v_fst_2443_; lean_object* v_snd_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v_fst_2443_ = lean_ctor_get(v_a_2441_, 0);
lean_inc(v_fst_2443_);
lean_dec(v_a_2441_);
v_snd_2444_ = lean_ctor_get(v_snd_2442_, 1);
lean_inc(v_snd_2444_);
lean_dec(v_snd_2442_);
v___x_2445_ = lean_box(0);
lean_inc_ref(v_e_2010_);
lean_inc(v___x_2143_);
v___x_2446_ = l_Lean_Meta_rwMatcher___lam__3(v___x_2053_, v___x_2186_, v_fst_2443_, v___x_2143_, v_e_2010_, v___x_2051_, v_snd_2444_, v___x_2445_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
lean_dec(v_snd_2444_);
v___y_2390_ = v_a_2404_;
v___y_2391_ = v___x_2436_;
v___y_2392_ = v___x_2446_;
goto v___jp_2389_;
}
else
{
lean_object* v_fst_2447_; lean_object* v_snd_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2461_; 
v_fst_2447_ = lean_ctor_get(v_a_2441_, 0);
lean_inc(v_fst_2447_);
lean_dec(v_a_2441_);
v_snd_2448_ = lean_ctor_get(v_snd_2442_, 1);
v_isSharedCheck_2461_ = !lean_is_exclusive(v_snd_2442_);
if (v_isSharedCheck_2461_ == 0)
{
lean_object* v_unused_2462_; 
v_unused_2462_ = lean_ctor_get(v_snd_2442_, 0);
lean_dec(v_unused_2462_);
v___x_2450_ = v_snd_2442_;
v_isShared_2451_ = v_isSharedCheck_2461_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_snd_2448_);
lean_dec(v_snd_2442_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2461_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2455_; 
v___x_2452_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__27, &l_Lean_Meta_rwMatcher___closed__27_once, _init_l_Lean_Meta_rwMatcher___closed__27);
lean_inc(v_snd_2448_);
v___x_2453_ = l_Lean_indentExpr(v_snd_2448_);
if (v_isShared_2451_ == 0)
{
lean_ctor_set_tag(v___x_2450_, 7);
lean_ctor_set(v___x_2450_, 1, v___x_2453_);
lean_ctor_set(v___x_2450_, 0, v___x_2452_);
v___x_2455_ = v___x_2450_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2452_);
lean_ctor_set(v_reuseFailAlloc_2460_, 1, v___x_2453_);
v___x_2455_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
lean_object* v___x_2456_; 
v___x_2456_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(v___x_2144_, v___x_2455_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; lean_object* v___x_2458_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_a_2457_);
lean_dec_ref_known(v___x_2456_, 1);
lean_inc_ref(v_e_2010_);
lean_inc(v___x_2143_);
v___x_2458_ = l_Lean_Meta_rwMatcher___lam__3(v___x_2053_, v___x_2186_, v_fst_2447_, v___x_2143_, v_e_2010_, v___x_2051_, v_snd_2448_, v_a_2457_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
lean_dec(v_snd_2448_);
v___y_2390_ = v_a_2404_;
v___y_2391_ = v___x_2436_;
v___y_2392_ = v___x_2458_;
goto v___jp_2389_;
}
else
{
lean_object* v_a_2459_; 
lean_dec(v_snd_2448_);
lean_dec(v_fst_2447_);
lean_dec_ref(v___x_2186_);
v_a_2459_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_a_2459_);
lean_dec_ref_known(v___x_2456_, 1);
v___y_2385_ = v_a_2404_;
v___y_2386_ = v___x_2436_;
v_a_2387_ = v_a_2459_;
goto v___jp_2384_;
}
}
}
}
}
else
{
lean_object* v_a_2463_; 
lean_dec_ref(v___x_2186_);
v_a_2463_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_a_2463_);
lean_dec_ref_known(v___x_2440_, 1);
v___y_2385_ = v_a_2404_;
v___y_2386_ = v___x_2436_;
v_a_2387_ = v_a_2463_;
goto v___jp_2384_;
}
}
else
{
lean_object* v_a_2464_; 
lean_dec_ref(v___x_2186_);
v_a_2464_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2464_);
lean_dec_ref_known(v___x_2437_, 1);
v___y_2385_ = v_a_2404_;
v___y_2386_ = v___x_2436_;
v_a_2387_ = v_a_2464_;
goto v___jp_2384_;
}
}
}
}
v___jp_2145_:
{
uint8_t v___x_2147_; 
v___x_2147_ = l_Lean_Exception_isInterrupt(v_a_2146_);
if (v___x_2147_ == 0)
{
uint8_t v___x_2148_; 
lean_inc_ref(v_a_2146_);
v___x_2148_ = l_Lean_Exception_isRuntime(v_a_2146_);
if (v___x_2148_ == 0)
{
lean_del_object(v___x_2101_);
if (v_hasTrace_2141_ == 0)
{
lean_dec_ref(v_a_2146_);
lean_dec(v___x_2143_);
goto v___jp_2068_;
}
else
{
lean_object* v___x_2149_; uint8_t v___x_2150_; 
v___x_2149_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__11, &l_Lean_Meta_rwMatcher___closed__11_once, _init_l_Lean_Meta_rwMatcher___closed__11);
v___x_2150_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2140_, v_options_2139_, v___x_2149_);
if (v___x_2150_ == 0)
{
lean_dec_ref(v_a_2146_);
lean_dec(v___x_2143_);
goto v___jp_2068_;
}
else
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2151_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__21, &l_Lean_Meta_rwMatcher___closed__21_once, _init_l_Lean_Meta_rwMatcher___closed__21);
v___x_2152_ = l_Lean_MessageData_ofConstName(v___x_2143_, v___x_2051_);
v___x_2153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2151_);
lean_ctor_set(v___x_2153_, 1, v___x_2152_);
v___x_2154_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__23, &l_Lean_Meta_rwMatcher___closed__23_once, _init_l_Lean_Meta_rwMatcher___closed__23);
v___x_2155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2153_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
v___x_2156_ = l_Lean_Exception_toMessageData(v_a_2146_);
v___x_2157_ = l_Lean_indentD(v___x_2156_);
v___x_2158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2155_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
v___x_2159_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__3(v___x_2144_, v___x_2158_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; lean_object* v___x_2161_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2160_);
lean_dec_ref_known(v___x_2159_, 1);
v___x_2161_ = l_Lean_Meta_rwMatcher___lam__0(v_e_2010_, v___x_2053_, v_a_2160_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
v___y_2038_ = v___x_2161_;
goto v___jp_2037_;
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec_ref(v_e_2010_);
v_a_2162_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2159_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2159_);
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
}
else
{
lean_object* v___x_2171_; 
lean_dec(v___x_2143_);
lean_dec_ref(v_e_2010_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set_tag(v___x_2101_, 1);
lean_ctor_set(v___x_2101_, 0, v_a_2146_);
v___x_2171_ = v___x_2101_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2146_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
else
{
lean_object* v___x_2174_; 
lean_dec(v___x_2143_);
lean_dec_ref(v_e_2010_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set_tag(v___x_2101_, 1);
lean_ctor_set(v___x_2101_, 0, v_a_2146_);
v___x_2174_ = v___x_2101_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2146_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
v___jp_2176_:
{
if (lean_obj_tag(v___y_2177_) == 0)
{
lean_dec(v___x_2143_);
lean_del_object(v___x_2101_);
lean_dec_ref(v_e_2010_);
return v___y_2177_;
}
else
{
lean_object* v_a_2178_; 
v_a_2178_ = lean_ctor_get(v___y_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___y_2177_, 1);
v_a_2146_ = v_a_2178_;
goto v___jp_2145_;
}
}
}
}
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
lean_dec(v___x_2097_);
lean_dec_ref(v___x_2096_);
lean_del_object(v___x_2074_);
lean_dec_ref(v_e_2010_);
lean_dec(v_altIdx_2009_);
v_a_2496_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2098_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2098_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
}
}
else
{
lean_dec(v_altIdx_2009_);
goto v___jp_2016_;
}
}
else
{
lean_dec(v_altIdx_2009_);
goto v___jp_2016_;
}
v___jp_2016_:
{
uint8_t v___x_2017_; lean_object* v___x_2018_; 
v___x_2017_ = 1;
v___x_2018_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_e_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2028_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2021_ = v___x_2018_;
v_isShared_2022_ = v_isSharedCheck_2028_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_2018_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2028_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2023_ = lean_box(0);
v___x_2024_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2024_, 0, v_a_2019_);
lean_ctor_set(v___x_2024_, 1, v___x_2023_);
lean_ctor_set_uint8(v___x_2024_, sizeof(void*)*2, v___x_2017_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2024_);
v___x_2026_ = v___x_2021_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
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
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
v_a_2029_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2018_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2018_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
v___jp_2037_:
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2047_; 
v_a_2039_ = lean_ctor_get(v___y_2038_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___y_2038_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2041_ = v___y_2038_;
v_isShared_2042_ = v_isSharedCheck_2047_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___y_2038_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2047_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v_a_2043_; lean_object* v___x_2045_; 
v_a_2043_ = lean_ctor_get(v_a_2039_, 0);
lean_inc(v_a_2043_);
lean_dec(v_a_2039_);
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 0, v_a_2043_);
v___x_2045_ = v___x_2041_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2043_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___boxed(lean_object* v_altIdx_2505_, lean_object* v_e_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_Lean_Meta_rwMatcher(v_altIdx_2505_, v_e_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_);
lean_dec(v_a_2510_);
lean_dec_ref(v_a_2509_);
lean_dec(v_a_2508_);
lean_dec_ref(v_a_2507_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__0(lean_object* v_inst_2513_, lean_object* v_a_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v___x_2520_; 
v___x_2520_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_a_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__0___boxed(lean_object* v_inst_2521_, lean_object* v_a_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__0(v_inst_2521_, v_a_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1(lean_object* v_mvarId_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v___x_2535_; 
v___x_2535_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1___redArg(v_mvarId_2529_, v___y_2531_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1___boxed(lean_object* v_mvarId_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1(v_mvarId_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v_mvarId_2536_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6(lean_object* v_00_u03b1_2543_, lean_object* v_msg_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v___x_2550_; 
v___x_2550_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___redArg(v_msg_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6___boxed(lean_object* v_00_u03b1_2551_, lean_object* v_msg_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__6(v_00_u03b1_2551_, v_msg_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
lean_dec(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15(lean_object* v_00_u03b1_2559_, lean_object* v_x_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v___x_2566_; 
v___x_2566_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___redArg(v_x_2560_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15___boxed(lean_object* v_00_u03b1_2567_, lean_object* v_x_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__12_spec__15(v_00_u03b1_2567_, v_x_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
return v_res_2574_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1(lean_object* v_00_u03b2_2575_, lean_object* v_x_2576_, lean_object* v_x_2577_){
_start:
{
uint8_t v___x_2578_; 
v___x_2578_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1___redArg(v_x_2576_, v_x_2577_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2579_, lean_object* v_x_2580_, lean_object* v_x_2581_){
_start:
{
uint8_t v_res_2582_; lean_object* v_r_2583_; 
v_res_2582_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1(v_00_u03b2_2579_, v_x_2580_, v_x_2581_);
lean_dec(v_x_2581_);
lean_dec_ref(v_x_2580_);
v_r_2583_ = lean_box(v_res_2582_);
return v_r_2583_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6(lean_object* v_00_u03b2_2584_, lean_object* v_x_2585_, size_t v_x_2586_, lean_object* v_x_2587_){
_start:
{
uint8_t v___x_2588_; 
v___x_2588_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6___redArg(v_x_2585_, v_x_2586_, v_x_2587_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6___boxed(lean_object* v_00_u03b2_2589_, lean_object* v_x_2590_, lean_object* v_x_2591_, lean_object* v_x_2592_){
_start:
{
size_t v_x_89079__boxed_2593_; uint8_t v_res_2594_; lean_object* v_r_2595_; 
v_x_89079__boxed_2593_ = lean_unbox_usize(v_x_2591_);
lean_dec(v_x_2591_);
v_res_2594_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6(v_00_u03b2_2589_, v_x_2590_, v_x_89079__boxed_2593_, v_x_2592_);
lean_dec(v_x_2592_);
lean_dec_ref(v_x_2590_);
v_r_2595_ = lean_box(v_res_2594_);
return v_r_2595_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6_spec__18(lean_object* v_00_u03b2_2596_, lean_object* v_keys_2597_, lean_object* v_vals_2598_, lean_object* v_heq_2599_, lean_object* v_i_2600_, lean_object* v_k_2601_){
_start:
{
uint8_t v___x_2602_; 
v___x_2602_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6_spec__18___redArg(v_keys_2597_, v_i_2600_, v_k_2601_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6_spec__18___boxed(lean_object* v_00_u03b2_2603_, lean_object* v_keys_2604_, lean_object* v_vals_2605_, lean_object* v_heq_2606_, lean_object* v_i_2607_, lean_object* v_k_2608_){
_start:
{
uint8_t v_res_2609_; lean_object* v_r_2610_; 
v_res_2609_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__1_spec__1_spec__6_spec__18(v_00_u03b2_2603_, v_keys_2604_, v_vals_2605_, v_heq_2606_, v_i_2607_, v_k_2608_);
lean_dec(v_k_2608_);
lean_dec_ref(v_vals_2605_);
lean_dec_ref(v_keys_2604_);
v_r_2610_ = lean_box(v_res_2609_);
return v_r_2610_;
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
