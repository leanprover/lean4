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
uint8_t v___x_84069__boxed_538_; lean_object* v_res_539_; 
v___x_84069__boxed_538_ = lean_unbox(v___x_531_);
v_res_539_ = l_Lean_Meta_rwMatcher___lam__0(v_e_530_, v___x_84069__boxed_538_, v_____r_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
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
uint8_t v___y_84111__boxed_572_; lean_object* v_res_573_; 
v___y_84111__boxed_572_ = lean_unbox(v___y_564_);
v_res_573_ = l_Lean_Meta_rwMatcher___lam__1(v___x_563_, v___y_84111__boxed_572_, v_e_565_, v_x_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
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
lean_object* v___x_598_; lean_object* v_env_599_; lean_object* v___x_600_; lean_object* v_toCold_601_; lean_object* v_mctx_602_; lean_object* v_lctx_603_; lean_object* v_options_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_598_ = lean_st_ref_get(v___y_596_);
v_env_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc_ref(v_env_599_);
lean_dec(v___x_598_);
v___x_600_ = lean_st_ref_get(v___y_594_);
v_toCold_601_ = lean_ctor_get(v___y_595_, 0);
v_mctx_602_ = lean_ctor_get(v___x_600_, 0);
lean_inc_ref(v_mctx_602_);
lean_dec(v___x_600_);
v_lctx_603_ = lean_ctor_get(v___y_593_, 2);
v_options_604_ = lean_ctor_get(v_toCold_601_, 2);
lean_inc_ref(v_options_604_);
lean_inc_ref(v_lctx_603_);
v___x_605_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_605_, 0, v_env_599_);
lean_ctor_set(v___x_605_, 1, v_mctx_602_);
lean_ctor_set(v___x_605_, 2, v_lctx_603_);
lean_ctor_set(v___x_605_, 3, v_options_604_);
v___x_606_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
lean_ctor_set(v___x_606_, 1, v_msgData_592_);
v___x_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3___boxed(lean_object* v_msgData_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msgData_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(lean_object* v_msg_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_ref_621_; lean_object* v___x_622_; lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_631_; 
v_ref_621_ = lean_ctor_get(v___y_618_, 2);
v___x_622_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
v_a_623_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_631_ == 0)
{
v___x_625_ = v___x_622_;
v_isShared_626_ = v_isSharedCheck_631_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_631_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_629_; 
lean_inc(v_ref_621_);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v_ref_621_);
lean_ctor_set(v___x_627_, 1, v_a_623_);
if (v_isShared_626_ == 0)
{
lean_ctor_set_tag(v___x_625_, 1);
lean_ctor_set(v___x_625_, 0, v___x_627_);
v___x_629_ = v___x_625_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg___boxed(lean_object* v_msg_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v_msg_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
return v_res_638_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(lean_object* v_keys_639_, lean_object* v_i_640_, lean_object* v_k_641_){
_start:
{
lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_642_ = lean_array_get_size(v_keys_639_);
v___x_643_ = lean_nat_dec_lt(v_i_640_, v___x_642_);
if (v___x_643_ == 0)
{
lean_dec(v_i_640_);
return v___x_643_;
}
else
{
lean_object* v_k_x27_644_; uint8_t v___x_645_; 
v_k_x27_644_ = lean_array_fget_borrowed(v_keys_639_, v_i_640_);
v___x_645_ = l_Lean_instBEqMVarId_beq(v_k_641_, v_k_x27_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_unsigned_to_nat(1u);
v___x_647_ = lean_nat_add(v_i_640_, v___x_646_);
lean_dec(v_i_640_);
v_i_640_ = v___x_647_;
goto _start;
}
else
{
lean_dec(v_i_640_);
return v___x_643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg___boxed(lean_object* v_keys_649_, lean_object* v_i_650_, lean_object* v_k_651_){
_start:
{
uint8_t v_res_652_; lean_object* v_r_653_; 
v_res_652_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(v_keys_649_, v_i_650_, v_k_651_);
lean_dec(v_k_651_);
lean_dec_ref(v_keys_649_);
v_r_653_ = lean_box(v_res_652_);
return v_r_653_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(lean_object* v_x_654_, size_t v_x_655_, lean_object* v_x_656_){
_start:
{
if (lean_obj_tag(v_x_654_) == 0)
{
lean_object* v_es_657_; lean_object* v___x_658_; size_t v___x_659_; size_t v___x_660_; lean_object* v_j_661_; lean_object* v___x_662_; 
v_es_657_ = lean_ctor_get(v_x_654_, 0);
v___x_658_ = lean_box(2);
v___x_659_ = ((size_t)31ULL);
v___x_660_ = lean_usize_land(v_x_655_, v___x_659_);
v_j_661_ = lean_usize_to_nat(v___x_660_);
v___x_662_ = lean_array_get_borrowed(v___x_658_, v_es_657_, v_j_661_);
lean_dec(v_j_661_);
switch(lean_obj_tag(v___x_662_))
{
case 0:
{
lean_object* v_key_663_; uint8_t v___x_664_; 
v_key_663_ = lean_ctor_get(v___x_662_, 0);
v___x_664_ = l_Lean_instBEqMVarId_beq(v_x_656_, v_key_663_);
return v___x_664_;
}
case 1:
{
lean_object* v_node_665_; size_t v___x_666_; size_t v___x_667_; 
v_node_665_ = lean_ctor_get(v___x_662_, 0);
v___x_666_ = ((size_t)5ULL);
v___x_667_ = lean_usize_shift_right(v_x_655_, v___x_666_);
v_x_654_ = v_node_665_;
v_x_655_ = v___x_667_;
goto _start;
}
default: 
{
uint8_t v___x_669_; 
v___x_669_ = 0;
return v___x_669_;
}
}
}
else
{
lean_object* v_ks_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v_ks_670_ = lean_ctor_get(v_x_654_, 0);
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(v_ks_670_, v___x_671_, v_x_656_);
return v___x_672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_673_, lean_object* v_x_674_, lean_object* v_x_675_){
_start:
{
size_t v_x_84244__boxed_676_; uint8_t v_res_677_; lean_object* v_r_678_; 
v_x_84244__boxed_676_ = lean_unbox_usize(v_x_674_);
lean_dec(v_x_674_);
v_res_677_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_673_, v_x_84244__boxed_676_, v_x_675_);
lean_dec(v_x_675_);
lean_dec_ref(v_x_673_);
v_r_678_ = lean_box(v_res_677_);
return v_r_678_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
uint64_t v___x_681_; size_t v___x_682_; uint8_t v___x_683_; 
v___x_681_ = l_Lean_instHashableMVarId_hash(v_x_680_);
v___x_682_ = lean_uint64_to_usize(v___x_681_);
v___x_683_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_679_, v___x_682_, v_x_680_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg___boxed(lean_object* v_x_684_, lean_object* v_x_685_){
_start:
{
uint8_t v_res_686_; lean_object* v_r_687_; 
v_res_686_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_x_684_, v_x_685_);
lean_dec(v_x_685_);
lean_dec_ref(v_x_684_);
v_r_687_ = lean_box(v_res_686_);
return v_r_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(lean_object* v_mvarId_688_, lean_object* v___y_689_){
_start:
{
lean_object* v___x_691_; lean_object* v_mctx_692_; lean_object* v_eAssignment_693_; uint8_t v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_691_ = lean_st_ref_get(v___y_689_);
v_mctx_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc_ref(v_mctx_692_);
lean_dec(v___x_691_);
v_eAssignment_693_ = lean_ctor_get(v_mctx_692_, 8);
lean_inc_ref(v_eAssignment_693_);
lean_dec_ref(v_mctx_692_);
v___x_694_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_eAssignment_693_, v_mvarId_688_);
lean_dec_ref(v_eAssignment_693_);
v___x_695_ = lean_box(v___x_694_);
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg___boxed(lean_object* v_mvarId_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_mvarId_697_, v___y_698_);
lean_dec(v___y_698_);
lean_dec(v_mvarId_697_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(lean_object* v_as_701_, size_t v_i_702_, size_t v_stop_703_, lean_object* v_b_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_a_711_; uint8_t v___x_715_; 
v___x_715_ = lean_usize_dec_eq(v_i_702_, v_stop_703_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_719_; 
v___x_716_ = lean_array_uget_borrowed(v_as_701_, v_i_702_);
v___x_719_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v___x_716_, v___y_706_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; uint8_t v___x_721_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_720_);
lean_dec_ref_known(v___x_719_, 1);
v___x_721_ = lean_unbox(v_a_720_);
lean_dec(v_a_720_);
if (v___x_721_ == 0)
{
goto v___jp_717_;
}
else
{
v_a_711_ = v_b_704_;
goto v___jp_710_;
}
}
else
{
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_722_; uint8_t v___x_723_; 
v_a_722_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_722_);
lean_dec_ref_known(v___x_719_, 1);
v___x_723_ = lean_unbox(v_a_722_);
lean_dec(v_a_722_);
if (v___x_723_ == 0)
{
v_a_711_ = v_b_704_;
goto v___jp_710_;
}
else
{
goto v___jp_717_;
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec_ref(v_b_704_);
v_a_724_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_719_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_719_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
v___jp_717_:
{
lean_object* v___x_718_; 
lean_inc(v___x_716_);
v___x_718_ = lean_array_push(v_b_704_, v___x_716_);
v_a_711_ = v___x_718_;
goto v___jp_710_;
}
}
else
{
lean_object* v___x_732_; 
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v_b_704_);
return v___x_732_;
}
v___jp_710_:
{
size_t v___x_712_; size_t v___x_713_; 
v___x_712_ = ((size_t)1ULL);
v___x_713_ = lean_usize_add(v_i_702_, v___x_712_);
v_i_702_ = v___x_713_;
v_b_704_ = v_a_711_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8___boxed(lean_object* v_as_733_, lean_object* v_i_734_, lean_object* v_stop_735_, lean_object* v_b_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
size_t v_i_boxed_742_; size_t v_stop_boxed_743_; lean_object* v_res_744_; 
v_i_boxed_742_ = lean_unbox_usize(v_i_734_);
lean_dec(v_i_734_);
v_stop_boxed_743_ = lean_unbox_usize(v_stop_735_);
lean_dec(v_stop_735_);
v_res_744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v_as_733_, v_i_boxed_742_, v_stop_boxed_743_, v_b_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec_ref(v_as_733_);
return v_res_744_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__0));
v___x_747_ = l_Lean_stringToMessageData(v___x_746_);
return v___x_747_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__2));
v___x_750_ = l_Lean_stringToMessageData(v___x_749_);
return v___x_750_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__4));
v___x_753_ = l_Lean_stringToMessageData(v___x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(lean_object* v_as_754_, size_t v_sz_755_, size_t v_i_756_, lean_object* v_b_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v_a_764_; uint8_t v___x_768_; 
v___x_768_ = lean_usize_dec_lt(v_i_756_, v_sz_755_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; 
v___x_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_769_, 0, v_b_757_);
return v___x_769_;
}
else
{
lean_object* v___x_770_; lean_object* v___y_772_; lean_object* v___y_774_; lean_object* v___y_776_; lean_object* v_a_777_; lean_object* v___y_779_; lean_object* v___y_780_; uint8_t v___y_781_; lean_object* v___y_797_; lean_object* v___y_798_; uint8_t v___y_799_; lean_object* v___x_814_; 
v___x_770_ = lean_box(0);
v_a_777_ = lean_array_uget_borrowed(v_as_754_, v_i_756_);
v___x_814_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_a_777_, v___y_759_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; uint8_t v___x_816_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_815_);
lean_dec_ref_known(v___x_814_, 1);
v___x_816_ = lean_unbox(v_a_815_);
lean_dec(v_a_815_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; 
lean_inc(v_a_777_);
v___x_817_ = l_Lean_MVarId_getType(v_a_777_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; uint8_t v___x_819_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc_n(v_a_818_, 2);
lean_dec_ref_known(v___x_817_, 1);
v___x_819_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_a_818_);
if (v___x_819_ == 0)
{
uint8_t v___x_820_; 
v___x_820_ = l_Lean_Expr_isEq(v_a_818_);
if (v___x_820_ == 0)
{
uint8_t v___x_821_; 
v___x_821_ = l_Lean_Expr_isHEq(v_a_818_);
lean_dec(v_a_818_);
if (v___x_821_ == 0)
{
v_a_764_ = v___x_770_;
goto v___jp_763_;
}
else
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_Meta_saveState___redArg(v___y_759_, v___y_761_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_824_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_a_823_);
lean_dec_ref_known(v___x_822_, 1);
lean_inc(v_a_777_);
v___x_824_ = l_Lean_MVarId_assumption(v_a_777_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_dec(v_a_823_);
v___y_774_ = v___x_824_;
goto v___jp_773_;
}
else
{
lean_object* v_a_825_; uint8_t v___y_827_; uint8_t v___x_843_; 
v_a_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_a_825_);
v___x_843_ = l_Lean_Exception_isInterrupt(v_a_825_);
if (v___x_843_ == 0)
{
uint8_t v___x_844_; 
v___x_844_ = l_Lean_Exception_isRuntime(v_a_825_);
v___y_827_ = v___x_844_;
goto v___jp_826_;
}
else
{
lean_dec(v_a_825_);
v___y_827_ = v___x_843_;
goto v___jp_826_;
}
v___jp_826_:
{
if (v___y_827_ == 0)
{
lean_object* v___x_828_; 
lean_dec_ref_known(v___x_824_, 1);
v___x_828_ = l_Lean_Meta_SavedState_restore___redArg(v_a_823_, v___y_759_, v___y_761_);
lean_dec(v_a_823_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v___x_829_; 
lean_dec_ref_known(v___x_828_, 1);
v___x_829_ = l_Lean_Meta_saveState___redArg(v___y_759_, v___y_761_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; lean_object* v___x_831_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
lean_dec_ref_known(v___x_829_, 1);
lean_inc(v_a_777_);
v___x_831_ = l_Lean_MVarId_hrefl(v_a_777_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_dec(v_a_830_);
v___y_774_ = v___x_831_;
goto v___jp_773_;
}
else
{
lean_object* v_a_832_; uint8_t v___x_833_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_832_);
v___x_833_ = l_Lean_Exception_isInterrupt(v_a_832_);
if (v___x_833_ == 0)
{
uint8_t v___x_834_; 
v___x_834_ = l_Lean_Exception_isRuntime(v_a_832_);
v___y_797_ = v_a_830_;
v___y_798_ = v___x_831_;
v___y_799_ = v___x_834_;
goto v___jp_796_;
}
else
{
lean_dec(v_a_832_);
v___y_797_ = v_a_830_;
v___y_798_ = v___x_831_;
v___y_799_ = v___x_833_;
goto v___jp_796_;
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
v_a_835_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_829_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_829_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
else
{
v___y_774_ = v___x_828_;
goto v___jp_773_;
}
}
else
{
lean_dec(v_a_823_);
v___y_774_ = v___x_824_;
goto v___jp_773_;
}
}
}
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
v_a_845_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_822_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_822_);
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
}
else
{
lean_object* v___x_853_; 
lean_dec(v_a_818_);
v___x_853_ = l_Lean_Meta_saveState___redArg(v___y_759_, v___y_761_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_855_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_853_, 1);
lean_inc(v_a_777_);
v___x_855_ = l_Lean_MVarId_assumption(v_a_777_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_dec(v_a_854_);
v___y_776_ = v___x_855_;
goto v___jp_775_;
}
else
{
lean_object* v_a_856_; uint8_t v___y_858_; uint8_t v___x_874_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
v___x_874_ = l_Lean_Exception_isInterrupt(v_a_856_);
if (v___x_874_ == 0)
{
uint8_t v___x_875_; 
v___x_875_ = l_Lean_Exception_isRuntime(v_a_856_);
v___y_858_ = v___x_875_;
goto v___jp_857_;
}
else
{
lean_dec(v_a_856_);
v___y_858_ = v___x_874_;
goto v___jp_857_;
}
v___jp_857_:
{
if (v___y_858_ == 0)
{
lean_object* v___x_859_; 
lean_dec_ref_known(v___x_855_, 1);
v___x_859_ = l_Lean_Meta_SavedState_restore___redArg(v_a_854_, v___y_759_, v___y_761_);
lean_dec(v_a_854_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v___x_860_; 
lean_dec_ref_known(v___x_859_, 1);
v___x_860_ = l_Lean_Meta_saveState___redArg(v___y_759_, v___y_761_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_862_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref_known(v___x_860_, 1);
lean_inc(v_a_777_);
v___x_862_ = l_Lean_MVarId_refl(v_a_777_, v___x_768_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_dec(v_a_861_);
v___y_776_ = v___x_862_;
goto v___jp_775_;
}
else
{
lean_object* v_a_863_; uint8_t v___x_864_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
v___x_864_ = l_Lean_Exception_isInterrupt(v_a_863_);
if (v___x_864_ == 0)
{
uint8_t v___x_865_; 
v___x_865_ = l_Lean_Exception_isRuntime(v_a_863_);
v___y_779_ = v___x_862_;
v___y_780_ = v_a_861_;
v___y_781_ = v___x_865_;
goto v___jp_778_;
}
else
{
lean_dec(v_a_863_);
v___y_779_ = v___x_862_;
v___y_780_ = v_a_861_;
v___y_781_ = v___x_864_;
goto v___jp_778_;
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
v_a_866_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_860_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_860_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
else
{
v___y_776_ = v___x_859_;
goto v___jp_775_;
}
}
else
{
lean_dec(v_a_854_);
v___y_776_ = v___x_855_;
goto v___jp_775_;
}
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
v_a_876_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_853_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_853_);
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
}
else
{
lean_object* v___x_884_; 
lean_dec(v_a_818_);
v___x_884_ = l_Lean_Meta_saveState___redArg(v___y_759_, v___y_761_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v___x_886_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref_known(v___x_884_, 1);
lean_inc(v_a_777_);
v___x_886_ = l_Lean_MVarId_assumption(v_a_777_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_dec(v_a_885_);
v___y_772_ = v___x_886_;
goto v___jp_771_;
}
else
{
lean_object* v_a_887_; uint8_t v___y_889_; uint8_t v___x_904_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_887_);
v___x_904_ = l_Lean_Exception_isInterrupt(v_a_887_);
if (v___x_904_ == 0)
{
uint8_t v___x_905_; 
v___x_905_ = l_Lean_Exception_isRuntime(v_a_887_);
v___y_889_ = v___x_905_;
goto v___jp_888_;
}
else
{
lean_dec(v_a_887_);
v___y_889_ = v___x_904_;
goto v___jp_888_;
}
v___jp_888_:
{
if (v___y_889_ == 0)
{
lean_object* v___x_890_; 
lean_dec_ref_known(v___x_886_, 1);
v___x_890_ = l_Lean_Meta_SavedState_restore___redArg(v_a_885_, v___y_759_, v___y_761_);
lean_dec(v_a_885_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_902_; 
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; 
v_unused_903_ = lean_ctor_get(v___x_890_, 0);
lean_dec(v_unused_903_);
v___x_892_ = v___x_890_;
v_isShared_893_ = v_isSharedCheck_902_;
goto v_resetjp_891_;
}
else
{
lean_dec(v___x_890_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_902_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_894_; lean_object* v___x_896_; 
v___x_894_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5);
lean_inc(v_a_777_);
if (v_isShared_893_ == 0)
{
lean_ctor_set_tag(v___x_892_, 1);
lean_ctor_set(v___x_892_, 0, v_a_777_);
v___x_896_ = v___x_892_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_777_);
v___x_896_ = v_reuseFailAlloc_901_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_894_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_897_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_899_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
v___y_772_ = v___x_900_;
goto v___jp_771_;
}
}
}
else
{
v___y_772_ = v___x_890_;
goto v___jp_771_;
}
}
else
{
lean_dec(v_a_885_);
v___y_772_ = v___x_886_;
goto v___jp_771_;
}
}
}
}
else
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
v_a_906_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_913_ == 0)
{
v___x_908_ = v___x_884_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_884_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_a_906_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
v_a_914_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_817_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_817_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
else
{
v_a_764_ = v___x_770_;
goto v___jp_763_;
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
v_a_922_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_814_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_814_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
v___jp_771_:
{
if (lean_obj_tag(v___y_772_) == 0)
{
lean_dec_ref_known(v___y_772_, 1);
v_a_764_ = v___x_770_;
goto v___jp_763_;
}
else
{
return v___y_772_;
}
}
v___jp_773_:
{
if (lean_obj_tag(v___y_774_) == 0)
{
lean_dec_ref_known(v___y_774_, 1);
v_a_764_ = v___x_770_;
goto v___jp_763_;
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
v_a_764_ = v___x_770_;
goto v___jp_763_;
}
else
{
return v___y_776_;
}
}
v___jp_778_:
{
if (v___y_781_ == 0)
{
lean_object* v___x_782_; 
lean_dec_ref(v___y_779_);
v___x_782_ = l_Lean_Meta_SavedState_restore___redArg(v___y_780_, v___y_759_, v___y_761_);
lean_dec_ref(v___y_780_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_794_; 
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_794_ == 0)
{
lean_object* v_unused_795_; 
v_unused_795_ = lean_ctor_get(v___x_782_, 0);
lean_dec(v_unused_795_);
v___x_784_ = v___x_782_;
v_isShared_785_ = v_isSharedCheck_794_;
goto v_resetjp_783_;
}
else
{
lean_dec(v___x_782_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_794_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v___x_788_; 
v___x_786_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1);
lean_inc(v_a_777_);
if (v_isShared_785_ == 0)
{
lean_ctor_set_tag(v___x_784_, 1);
lean_ctor_set(v___x_784_, 0, v_a_777_);
v___x_788_ = v___x_784_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_777_);
v___x_788_ = v_reuseFailAlloc_793_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_786_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_789_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
v___x_792_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_791_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
v___y_776_ = v___x_792_;
goto v___jp_775_;
}
}
}
else
{
v___y_776_ = v___x_782_;
goto v___jp_775_;
}
}
else
{
lean_dec_ref(v___y_780_);
v___y_776_ = v___y_779_;
goto v___jp_775_;
}
}
v___jp_796_:
{
if (v___y_799_ == 0)
{
lean_object* v___x_800_; 
lean_dec_ref(v___y_798_);
v___x_800_ = l_Lean_Meta_SavedState_restore___redArg(v___y_797_, v___y_759_, v___y_761_);
lean_dec_ref(v___y_797_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_812_; 
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_812_ == 0)
{
lean_object* v_unused_813_; 
v_unused_813_ = lean_ctor_get(v___x_800_, 0);
lean_dec(v_unused_813_);
v___x_802_ = v___x_800_;
v_isShared_803_ = v_isSharedCheck_812_;
goto v_resetjp_801_;
}
else
{
lean_dec(v___x_800_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_812_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_804_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1);
lean_inc(v_a_777_);
if (v_isShared_803_ == 0)
{
lean_ctor_set_tag(v___x_802_, 1);
lean_ctor_set(v___x_802_, 0, v_a_777_);
v___x_806_ = v___x_802_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_777_);
v___x_806_ = v_reuseFailAlloc_811_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_804_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_807_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_809_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
v___y_774_ = v___x_810_;
goto v___jp_773_;
}
}
}
else
{
v___y_774_ = v___x_800_;
goto v___jp_773_;
}
}
else
{
lean_dec_ref(v___y_797_);
v___y_774_ = v___y_798_;
goto v___jp_773_;
}
}
}
v___jp_763_:
{
size_t v___x_765_; size_t v___x_766_; 
v___x_765_ = ((size_t)1ULL);
v___x_766_ = lean_usize_add(v_i_756_, v___x_765_);
v_i_756_ = v___x_766_;
v_b_757_ = v_a_764_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___boxed(lean_object* v_as_930_, lean_object* v_sz_931_, lean_object* v_i_932_, lean_object* v_b_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
size_t v_sz_boxed_939_; size_t v_i_boxed_940_; lean_object* v_res_941_; 
v_sz_boxed_939_ = lean_unbox_usize(v_sz_931_);
lean_dec(v_sz_931_);
v_i_boxed_940_ = lean_unbox_usize(v_i_932_);
lean_dec(v_i_932_);
v_res_941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v_as_930_, v_sz_boxed_939_, v_i_boxed_940_, v_b_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec_ref(v_as_930_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
if (lean_obj_tag(v_a_942_) == 0)
{
lean_object* v___x_944_; 
v___x_944_ = l_List_reverse___redArg(v_a_943_);
return v___x_944_;
}
else
{
lean_object* v_head_945_; lean_object* v_tail_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_955_; 
v_head_945_ = lean_ctor_get(v_a_942_, 0);
v_tail_946_ = lean_ctor_get(v_a_942_, 1);
v_isSharedCheck_955_ = !lean_is_exclusive(v_a_942_);
if (v_isSharedCheck_955_ == 0)
{
v___x_948_ = v_a_942_;
v_isShared_949_ = v_isSharedCheck_955_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_tail_946_);
lean_inc(v_head_945_);
lean_dec(v_a_942_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_955_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_950_, 0, v_head_945_);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v_a_943_);
lean_ctor_set(v___x_948_, 0, v___x_950_);
v___x_952_ = v___x_948_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_950_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_a_943_);
v___x_952_ = v_reuseFailAlloc_954_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
v_a_942_ = v_tail_946_;
v_a_943_ = v___x_952_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__1(void){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__0));
v___x_958_ = l_Lean_stringToMessageData(v___x_957_);
return v___x_958_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__3(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__2));
v___x_961_ = l_Lean_stringToMessageData(v___x_960_);
return v___x_961_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__5(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__4));
v___x_964_ = l_Lean_stringToMessageData(v___x_963_);
return v___x_964_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__7(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__6));
v___x_967_ = l_Lean_stringToMessageData(v___x_966_);
return v___x_967_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__9(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__8));
v___x_970_ = l_Lean_stringToMessageData(v___x_969_);
return v___x_970_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__12(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__11));
v___x_975_ = l_Lean_stringToMessageData(v___x_974_);
return v___x_975_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__14(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__13));
v___x_978_ = l_Lean_stringToMessageData(v___x_977_);
return v___x_978_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__16(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__15));
v___x_981_ = l_Lean_stringToMessageData(v___x_980_);
return v___x_981_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__22(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__21));
v___x_990_ = l_Lean_stringToMessageData(v___x_989_);
return v___x_990_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__24(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__23));
v___x_993_ = l_Lean_stringToMessageData(v___x_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2(uint8_t v___x_994_, lean_object* v___x_995_, lean_object* v_fst_996_, lean_object* v___x_997_, lean_object* v_e_998_, uint8_t v___y_999_, lean_object* v_snd_1000_, lean_object* v_____r_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___y_1008_; lean_object* v_proof_1009_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; uint8_t v___y_1034_; lean_object* v___x_1046_; lean_object* v___y_1048_; uint8_t v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; uint8_t v___y_1069_; lean_object* v_a_1070_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; uint8_t v___y_1099_; lean_object* v___y_1100_; size_t v_sz_1110_; size_t v___x_1111_; lean_object* v___x_1112_; lean_object* v___y_1114_; uint8_t v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1119_; uint8_t v_fst_1141_; lean_object* v_fst_1142_; lean_object* v_snd_1143_; lean_object* v___x_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1046_ = l_Lean_mkAppN(v___x_995_, v_fst_996_);
v_sz_1110_ = lean_array_size(v_fst_996_);
v___x_1111_ = ((size_t)0ULL);
v___x_1112_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_1110_, v___x_1111_, v_fst_996_);
v___x_1177_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1178_ = lean_unsigned_to_nat(4u);
v___x_1179_ = l_Lean_Expr_isAppOfArity(v_snd_1000_, v___x_1177_, v___x_1178_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1180_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1181_ = lean_unsigned_to_nat(3u);
v___x_1182_ = l_Lean_Expr_isAppOfArity(v_snd_1000_, v___x_1180_, v___x_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
lean_dec_ref(v___x_1112_);
lean_dec_ref(v___x_1046_);
lean_dec_ref(v_e_998_);
v___x_1183_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1184_ = l_Lean_MessageData_ofConstName(v___x_997_, v___y_999_);
v___x_1185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1183_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1185_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v___x_1188_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1187_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1188_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1188_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
else
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1197_ = l_Lean_Expr_appFn_x21(v_snd_1000_);
v___x_1198_ = l_Lean_Expr_appArg_x21(v___x_1197_);
lean_dec_ref(v___x_1197_);
v___x_1199_ = l_Lean_Expr_appArg_x21(v_snd_1000_);
v_fst_1141_ = v___y_999_;
v_fst_1142_ = v___x_1198_;
v_snd_1143_ = v___x_1199_;
goto v___jp_1140_;
}
}
else
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1200_ = l_Lean_Expr_appFn_x21(v_snd_1000_);
v___x_1201_ = l_Lean_Expr_appFn_x21(v___x_1200_);
lean_dec_ref(v___x_1200_);
v___x_1202_ = l_Lean_Expr_appArg_x21(v___x_1201_);
lean_dec_ref(v___x_1201_);
v___x_1203_ = l_Lean_Expr_appArg_x21(v_snd_1000_);
v_fst_1141_ = v___x_994_;
v_fst_1142_ = v___x_1202_;
v_snd_1143_ = v___x_1203_;
goto v___jp_1140_;
}
v___jp_1007_:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1010_, 0, v_proof_1009_);
v___x_1011_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1011_, 0, v___y_1008_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
lean_ctor_set_uint8(v___x_1011_, sizeof(void*)*2, v___x_994_);
v___x_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
return v___x_1012_;
}
v___jp_1013_:
{
if (lean_obj_tag(v___y_1015_) == 0)
{
lean_object* v_a_1016_; 
v_a_1016_ = lean_ctor_get(v___y_1015_, 0);
lean_inc(v_a_1016_);
lean_dec_ref_known(v___y_1015_, 1);
v___y_1008_ = v___y_1014_;
v_proof_1009_ = v_a_1016_;
goto v___jp_1007_;
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec_ref(v___y_1014_);
v_a_1017_ = lean_ctor_get(v___y_1015_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___y_1015_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___y_1015_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___y_1015_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
v___jp_1025_:
{
if (v___y_1034_ == 0)
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
lean_dec_ref(v___y_1031_);
v___x_1035_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1036_ = l_Lean_MessageData_ofExpr(v___y_1026_);
v___x_1037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1035_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1037_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = l_Lean_Exception_toMessageData(v___y_1033_);
v___x_1041_ = l_Lean_indentD(v___x_1040_);
v___x_1042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1039_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1042_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v___x_1045_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1044_, v___y_1029_, v___y_1032_, v___y_1028_, v___y_1030_);
v___y_1014_ = v___y_1027_;
v___y_1015_ = v___x_1045_;
goto v___jp_1013_;
}
else
{
lean_dec_ref(v___y_1033_);
lean_dec_ref(v___y_1026_);
v___y_1014_ = v___y_1027_;
v___y_1015_ = v___y_1031_;
goto v___jp_1013_;
}
}
v___jp_1047_:
{
lean_object* v___x_1054_; lean_object* v_a_1055_; lean_object* v___x_1056_; 
v___x_1054_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_1048_, v___y_1051_);
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1055_);
lean_dec_ref(v___x_1054_);
v___x_1056_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___x_1046_, v___y_1051_);
if (v___y_1049_ == 0)
{
lean_object* v_a_1057_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1057_);
lean_dec_ref(v___x_1056_);
v___y_1008_ = v_a_1055_;
v_proof_1009_ = v_a_1057_;
goto v___jp_1007_;
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1059_; 
v_a_1058_ = lean_ctor_get(v___x_1056_, 0);
lean_inc_n(v_a_1058_, 2);
lean_dec_ref(v___x_1056_);
v___x_1059_ = l_Lean_Meta_mkEqOfHEq(v_a_1058_, v___x_994_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_dec(v_a_1058_);
v___y_1014_ = v_a_1055_;
v___y_1015_ = v___x_1059_;
goto v___jp_1013_;
}
else
{
lean_object* v_a_1060_; uint8_t v___x_1061_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
v___x_1061_ = l_Lean_Exception_isInterrupt(v_a_1060_);
if (v___x_1061_ == 0)
{
uint8_t v___x_1062_; 
lean_inc(v_a_1060_);
v___x_1062_ = l_Lean_Exception_isRuntime(v_a_1060_);
v___y_1026_ = v_a_1058_;
v___y_1027_ = v_a_1055_;
v___y_1028_ = v___y_1052_;
v___y_1029_ = v___y_1050_;
v___y_1030_ = v___y_1053_;
v___y_1031_ = v___x_1059_;
v___y_1032_ = v___y_1051_;
v___y_1033_ = v_a_1060_;
v___y_1034_ = v___x_1062_;
goto v___jp_1025_;
}
else
{
v___y_1026_ = v_a_1058_;
v___y_1027_ = v_a_1055_;
v___y_1028_ = v___y_1052_;
v___y_1029_ = v___y_1050_;
v___y_1030_ = v___y_1053_;
v___y_1031_ = v___x_1059_;
v___y_1032_ = v___y_1051_;
v___y_1033_ = v_a_1060_;
v___y_1034_ = v___x_1061_;
goto v___jp_1025_;
}
}
}
}
v___jp_1063_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; 
v___x_1071_ = lean_array_get_size(v_a_1070_);
v___x_1072_ = lean_unsigned_to_nat(0u);
v___x_1073_ = lean_nat_dec_eq(v___x_1071_, v___x_1072_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_dec_ref(v___y_1068_);
lean_dec_ref(v___x_1046_);
v___x_1074_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1075_ = l_Lean_MessageData_ofConstName(v___x_997_, v___x_1073_);
v___x_1076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1076_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = lean_array_to_list(v_a_1070_);
v___x_1080_ = lean_box(0);
v___x_1081_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_1079_, v___x_1080_);
v___x_1082_ = l_Lean_MessageData_ofList(v___x_1081_);
v___x_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1078_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1083_, v___y_1065_, v___y_1064_, v___y_1067_, v___y_1066_);
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
else
{
lean_dec_ref(v_a_1070_);
lean_dec(v___x_997_);
v___y_1048_ = v___y_1068_;
v___y_1049_ = v___y_1069_;
v___y_1050_ = v___y_1065_;
v___y_1051_ = v___y_1064_;
v___y_1052_ = v___y_1067_;
v___y_1053_ = v___y_1066_;
goto v___jp_1047_;
}
}
v___jp_1093_:
{
if (lean_obj_tag(v___y_1100_) == 0)
{
lean_object* v_a_1101_; 
v_a_1101_ = lean_ctor_get(v___y_1100_, 0);
lean_inc(v_a_1101_);
lean_dec_ref_known(v___y_1100_, 1);
v___y_1064_ = v___y_1094_;
v___y_1065_ = v___y_1095_;
v___y_1066_ = v___y_1096_;
v___y_1067_ = v___y_1097_;
v___y_1068_ = v___y_1098_;
v___y_1069_ = v___y_1099_;
v_a_1070_ = v_a_1101_;
goto v___jp_1063_;
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec_ref(v___y_1098_);
lean_dec_ref(v___x_1046_);
lean_dec(v___x_997_);
v_a_1102_ = lean_ctor_get(v___y_1100_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___y_1100_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___y_1100_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___y_1100_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
v___jp_1113_:
{
lean_object* v___x_1120_; size_t v_sz_1121_; lean_object* v___x_1122_; 
v___x_1120_ = lean_box(0);
v_sz_1121_ = lean_array_size(v___x_1112_);
v___x_1122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1112_, v_sz_1121_, v___x_1111_, v___x_1120_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; 
lean_dec_ref_known(v___x_1122_, 1);
v___x_1123_ = lean_unsigned_to_nat(0u);
v___x_1124_ = lean_array_get_size(v___x_1112_);
v___x_1125_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1126_ = lean_nat_dec_lt(v___x_1123_, v___x_1124_);
if (v___x_1126_ == 0)
{
lean_dec_ref(v___x_1112_);
v___y_1064_ = v___y_1117_;
v___y_1065_ = v___y_1116_;
v___y_1066_ = v___y_1119_;
v___y_1067_ = v___y_1118_;
v___y_1068_ = v___y_1114_;
v___y_1069_ = v___y_1115_;
v_a_1070_ = v___x_1125_;
goto v___jp_1063_;
}
else
{
uint8_t v___x_1127_; 
v___x_1127_ = lean_nat_dec_le(v___x_1124_, v___x_1124_);
if (v___x_1127_ == 0)
{
if (v___x_1126_ == 0)
{
lean_dec_ref(v___x_1112_);
v___y_1064_ = v___y_1117_;
v___y_1065_ = v___y_1116_;
v___y_1066_ = v___y_1119_;
v___y_1067_ = v___y_1118_;
v___y_1068_ = v___y_1114_;
v___y_1069_ = v___y_1115_;
v_a_1070_ = v___x_1125_;
goto v___jp_1063_;
}
else
{
size_t v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_usize_of_nat(v___x_1124_);
v___x_1129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1112_, v___x_1111_, v___x_1128_, v___x_1125_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec_ref(v___x_1112_);
v___y_1094_ = v___y_1117_;
v___y_1095_ = v___y_1116_;
v___y_1096_ = v___y_1119_;
v___y_1097_ = v___y_1118_;
v___y_1098_ = v___y_1114_;
v___y_1099_ = v___y_1115_;
v___y_1100_ = v___x_1129_;
goto v___jp_1093_;
}
}
else
{
size_t v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_usize_of_nat(v___x_1124_);
v___x_1131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1112_, v___x_1111_, v___x_1130_, v___x_1125_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec_ref(v___x_1112_);
v___y_1094_ = v___y_1117_;
v___y_1095_ = v___y_1116_;
v___y_1096_ = v___y_1119_;
v___y_1097_ = v___y_1118_;
v___y_1098_ = v___y_1114_;
v___y_1099_ = v___y_1115_;
v___y_1100_ = v___x_1131_;
goto v___jp_1093_;
}
}
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec_ref(v___y_1114_);
lean_dec_ref(v___x_1112_);
lean_dec_ref(v___x_1046_);
lean_dec(v___x_997_);
v_a_1132_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1122_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1122_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
v___jp_1140_:
{
lean_object* v___x_1144_; 
lean_inc_ref(v_fst_1142_);
lean_inc_ref(v_e_998_);
v___x_1144_ = l_Lean_Meta_isExprDefEq(v_e_998_, v_fst_1142_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; uint8_t v___x_1146_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1145_);
lean_dec_ref_known(v___x_1144_, 1);
v___x_1146_ = lean_unbox(v_a_1145_);
lean_dec(v_a_1145_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
lean_dec_ref(v_snd_1143_);
lean_dec_ref(v___x_1112_);
lean_dec_ref(v___x_1046_);
v___x_1147_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1148_ = l_Lean_MessageData_ofExpr(v_fst_1142_);
v___x_1149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1147_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1149_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = l_Lean_MessageData_ofConstName(v___x_997_, v___y_999_);
v___x_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1151_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = l_Lean_MessageData_ofExpr(v_e_998_);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1159_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1160_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1160_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
else
{
lean_dec_ref(v_fst_1142_);
lean_dec_ref(v_e_998_);
v___y_1114_ = v_snd_1143_;
v___y_1115_ = v_fst_1141_;
v___y_1116_ = v___y_1002_;
v___y_1117_ = v___y_1003_;
v___y_1118_ = v___y_1004_;
v___y_1119_ = v___y_1005_;
goto v___jp_1113_;
}
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
lean_dec_ref(v_snd_1143_);
lean_dec_ref(v_fst_1142_);
lean_dec_ref(v___x_1112_);
lean_dec_ref(v___x_1046_);
lean_dec_ref(v_e_998_);
lean_dec(v___x_997_);
v_a_1169_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1144_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1144_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2___boxed(lean_object* v___x_1204_, lean_object* v___x_1205_, lean_object* v_fst_1206_, lean_object* v___x_1207_, lean_object* v_e_1208_, lean_object* v___y_1209_, lean_object* v_snd_1210_, lean_object* v_____r_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
uint8_t v___x_84882__boxed_1217_; uint8_t v___y_84886__boxed_1218_; lean_object* v_res_1219_; 
v___x_84882__boxed_1217_ = lean_unbox(v___x_1204_);
v___y_84886__boxed_1218_ = lean_unbox(v___y_1209_);
v_res_1219_ = l_Lean_Meta_rwMatcher___lam__2(v___x_84882__boxed_1217_, v___x_1205_, v_fst_1206_, v___x_1207_, v_e_1208_, v___y_84886__boxed_1218_, v_snd_1210_, v_____r_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v_snd_1210_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3(uint8_t v___x_1220_, lean_object* v___x_1221_, lean_object* v_fst_1222_, lean_object* v___x_1223_, lean_object* v_e_1224_, uint8_t v___y_1225_, lean_object* v_snd_1226_, lean_object* v_____r_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v___y_1234_; lean_object* v_proof_1235_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; uint8_t v___y_1260_; lean_object* v___x_1272_; lean_object* v___y_1274_; uint8_t v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; uint8_t v___y_1295_; lean_object* v_a_1296_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; uint8_t v___y_1325_; lean_object* v___y_1326_; size_t v_sz_1336_; size_t v___x_1337_; lean_object* v___x_1338_; lean_object* v___y_1340_; uint8_t v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; uint8_t v_fst_1367_; lean_object* v_fst_1368_; lean_object* v_snd_1369_; lean_object* v___x_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
v___x_1272_ = l_Lean_mkAppN(v___x_1221_, v_fst_1222_);
v_sz_1336_ = lean_array_size(v_fst_1222_);
v___x_1337_ = ((size_t)0ULL);
v___x_1338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_1336_, v___x_1337_, v_fst_1222_);
v___x_1403_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1404_ = lean_unsigned_to_nat(4u);
v___x_1405_ = l_Lean_Expr_isAppOfArity(v_snd_1226_, v___x_1403_, v___x_1404_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v___x_1406_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1407_ = lean_unsigned_to_nat(3u);
v___x_1408_ = l_Lean_Expr_isAppOfArity(v_snd_1226_, v___x_1406_, v___x_1407_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_dec_ref(v___x_1338_);
lean_dec_ref(v___x_1272_);
lean_dec_ref(v_e_1224_);
v___x_1409_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1410_ = l_Lean_MessageData_ofConstName(v___x_1223_, v___y_1225_);
v___x_1411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1409_);
lean_ctor_set(v___x_1411_, 1, v___x_1410_);
v___x_1412_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1411_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
v___x_1414_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1413_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1414_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1414_);
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
else
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1423_ = l_Lean_Expr_appFn_x21(v_snd_1226_);
v___x_1424_ = l_Lean_Expr_appArg_x21(v___x_1423_);
lean_dec_ref(v___x_1423_);
v___x_1425_ = l_Lean_Expr_appArg_x21(v_snd_1226_);
v_fst_1367_ = v___y_1225_;
v_fst_1368_ = v___x_1424_;
v_snd_1369_ = v___x_1425_;
goto v___jp_1366_;
}
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1426_ = l_Lean_Expr_appFn_x21(v_snd_1226_);
v___x_1427_ = l_Lean_Expr_appFn_x21(v___x_1426_);
lean_dec_ref(v___x_1426_);
v___x_1428_ = l_Lean_Expr_appArg_x21(v___x_1427_);
lean_dec_ref(v___x_1427_);
v___x_1429_ = l_Lean_Expr_appArg_x21(v_snd_1226_);
v_fst_1367_ = v___x_1220_;
v_fst_1368_ = v___x_1428_;
v_snd_1369_ = v___x_1429_;
goto v___jp_1366_;
}
v___jp_1233_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1236_, 0, v_proof_1235_);
v___x_1237_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1237_, 0, v___y_1234_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
lean_ctor_set_uint8(v___x_1237_, sizeof(void*)*2, v___x_1220_);
v___x_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
return v___x_1238_;
}
v___jp_1239_:
{
if (lean_obj_tag(v___y_1241_) == 0)
{
lean_object* v_a_1242_; 
v_a_1242_ = lean_ctor_get(v___y_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___y_1241_, 1);
v___y_1234_ = v___y_1240_;
v_proof_1235_ = v_a_1242_;
goto v___jp_1233_;
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
lean_dec_ref(v___y_1240_);
v_a_1243_ = lean_ctor_get(v___y_1241_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___y_1241_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___y_1241_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___y_1241_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
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
v___jp_1251_:
{
if (v___y_1260_ == 0)
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
lean_dec_ref(v___y_1256_);
v___x_1261_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1262_ = l_Lean_MessageData_ofExpr(v___y_1254_);
v___x_1263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1261_);
lean_ctor_set(v___x_1263_, 1, v___x_1262_);
v___x_1264_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1263_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
v___x_1266_ = l_Lean_Exception_toMessageData(v___y_1257_);
v___x_1267_ = l_Lean_indentD(v___x_1266_);
v___x_1268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1265_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
v___x_1269_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1268_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
v___x_1271_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1270_, v___y_1255_, v___y_1258_, v___y_1259_, v___y_1252_);
v___y_1240_ = v___y_1253_;
v___y_1241_ = v___x_1271_;
goto v___jp_1239_;
}
else
{
lean_dec_ref(v___y_1257_);
lean_dec_ref(v___y_1254_);
v___y_1240_ = v___y_1253_;
v___y_1241_ = v___y_1256_;
goto v___jp_1239_;
}
}
v___jp_1273_:
{
lean_object* v___x_1280_; lean_object* v_a_1281_; lean_object* v___x_1282_; 
v___x_1280_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_1274_, v___y_1277_);
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
lean_dec_ref(v___x_1280_);
v___x_1282_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___x_1272_, v___y_1277_);
if (v___y_1275_ == 0)
{
lean_object* v_a_1283_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
lean_dec_ref(v___x_1282_);
v___y_1234_ = v_a_1281_;
v_proof_1235_ = v_a_1283_;
goto v___jp_1233_;
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1285_; 
v_a_1284_ = lean_ctor_get(v___x_1282_, 0);
lean_inc_n(v_a_1284_, 2);
lean_dec_ref(v___x_1282_);
v___x_1285_ = l_Lean_Meta_mkEqOfHEq(v_a_1284_, v___x_1220_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_dec(v_a_1284_);
v___y_1240_ = v_a_1281_;
v___y_1241_ = v___x_1285_;
goto v___jp_1239_;
}
else
{
lean_object* v_a_1286_; uint8_t v___x_1287_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1286_);
v___x_1287_ = l_Lean_Exception_isInterrupt(v_a_1286_);
if (v___x_1287_ == 0)
{
uint8_t v___x_1288_; 
lean_inc(v_a_1286_);
v___x_1288_ = l_Lean_Exception_isRuntime(v_a_1286_);
v___y_1252_ = v___y_1279_;
v___y_1253_ = v_a_1281_;
v___y_1254_ = v_a_1284_;
v___y_1255_ = v___y_1276_;
v___y_1256_ = v___x_1285_;
v___y_1257_ = v_a_1286_;
v___y_1258_ = v___y_1277_;
v___y_1259_ = v___y_1278_;
v___y_1260_ = v___x_1288_;
goto v___jp_1251_;
}
else
{
v___y_1252_ = v___y_1279_;
v___y_1253_ = v_a_1281_;
v___y_1254_ = v_a_1284_;
v___y_1255_ = v___y_1276_;
v___y_1256_ = v___x_1285_;
v___y_1257_ = v_a_1286_;
v___y_1258_ = v___y_1277_;
v___y_1259_ = v___y_1278_;
v___y_1260_ = v___x_1287_;
goto v___jp_1251_;
}
}
}
}
v___jp_1289_:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; uint8_t v___x_1299_; 
v___x_1297_ = lean_array_get_size(v_a_1296_);
v___x_1298_ = lean_unsigned_to_nat(0u);
v___x_1299_ = lean_nat_dec_eq(v___x_1297_, v___x_1298_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_dec_ref(v___y_1291_);
lean_dec_ref(v___x_1272_);
v___x_1300_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1301_ = l_Lean_MessageData_ofConstName(v___x_1223_, v___x_1299_);
v___x_1302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1300_);
lean_ctor_set(v___x_1302_, 1, v___x_1301_);
v___x_1303_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1302_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
v___x_1305_ = lean_array_to_list(v_a_1296_);
v___x_1306_ = lean_box(0);
v___x_1307_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_1305_, v___x_1306_);
v___x_1308_ = l_Lean_MessageData_ofList(v___x_1307_);
v___x_1309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1304_);
lean_ctor_set(v___x_1309_, 1, v___x_1308_);
v___x_1310_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1309_, v___y_1292_, v___y_1290_, v___y_1294_, v___y_1293_);
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1310_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
else
{
lean_dec_ref(v_a_1296_);
lean_dec(v___x_1223_);
v___y_1274_ = v___y_1291_;
v___y_1275_ = v___y_1295_;
v___y_1276_ = v___y_1292_;
v___y_1277_ = v___y_1290_;
v___y_1278_ = v___y_1294_;
v___y_1279_ = v___y_1293_;
goto v___jp_1273_;
}
}
v___jp_1319_:
{
if (lean_obj_tag(v___y_1326_) == 0)
{
lean_object* v_a_1327_; 
v_a_1327_ = lean_ctor_get(v___y_1326_, 0);
lean_inc(v_a_1327_);
lean_dec_ref_known(v___y_1326_, 1);
v___y_1290_ = v___y_1320_;
v___y_1291_ = v___y_1321_;
v___y_1292_ = v___y_1322_;
v___y_1293_ = v___y_1323_;
v___y_1294_ = v___y_1324_;
v___y_1295_ = v___y_1325_;
v_a_1296_ = v_a_1327_;
goto v___jp_1289_;
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec_ref(v___y_1321_);
lean_dec_ref(v___x_1272_);
lean_dec(v___x_1223_);
v_a_1328_ = lean_ctor_get(v___y_1326_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___y_1326_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___y_1326_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___y_1326_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
v___jp_1339_:
{
lean_object* v___x_1346_; size_t v_sz_1347_; lean_object* v___x_1348_; 
v___x_1346_ = lean_box(0);
v_sz_1347_ = lean_array_size(v___x_1338_);
v___x_1348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1338_, v_sz_1347_, v___x_1337_, v___x_1346_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
lean_dec_ref_known(v___x_1348_, 1);
v___x_1349_ = lean_unsigned_to_nat(0u);
v___x_1350_ = lean_array_get_size(v___x_1338_);
v___x_1351_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1352_ = lean_nat_dec_lt(v___x_1349_, v___x_1350_);
if (v___x_1352_ == 0)
{
lean_dec_ref(v___x_1338_);
v___y_1290_ = v___y_1343_;
v___y_1291_ = v___y_1340_;
v___y_1292_ = v___y_1342_;
v___y_1293_ = v___y_1345_;
v___y_1294_ = v___y_1344_;
v___y_1295_ = v___y_1341_;
v_a_1296_ = v___x_1351_;
goto v___jp_1289_;
}
else
{
uint8_t v___x_1353_; 
v___x_1353_ = lean_nat_dec_le(v___x_1350_, v___x_1350_);
if (v___x_1353_ == 0)
{
if (v___x_1352_ == 0)
{
lean_dec_ref(v___x_1338_);
v___y_1290_ = v___y_1343_;
v___y_1291_ = v___y_1340_;
v___y_1292_ = v___y_1342_;
v___y_1293_ = v___y_1345_;
v___y_1294_ = v___y_1344_;
v___y_1295_ = v___y_1341_;
v_a_1296_ = v___x_1351_;
goto v___jp_1289_;
}
else
{
size_t v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = lean_usize_of_nat(v___x_1350_);
v___x_1355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1338_, v___x_1337_, v___x_1354_, v___x_1351_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
lean_dec_ref(v___x_1338_);
v___y_1320_ = v___y_1343_;
v___y_1321_ = v___y_1340_;
v___y_1322_ = v___y_1342_;
v___y_1323_ = v___y_1345_;
v___y_1324_ = v___y_1344_;
v___y_1325_ = v___y_1341_;
v___y_1326_ = v___x_1355_;
goto v___jp_1319_;
}
}
else
{
size_t v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_usize_of_nat(v___x_1350_);
v___x_1357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1338_, v___x_1337_, v___x_1356_, v___x_1351_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
lean_dec_ref(v___x_1338_);
v___y_1320_ = v___y_1343_;
v___y_1321_ = v___y_1340_;
v___y_1322_ = v___y_1342_;
v___y_1323_ = v___y_1345_;
v___y_1324_ = v___y_1344_;
v___y_1325_ = v___y_1341_;
v___y_1326_ = v___x_1357_;
goto v___jp_1319_;
}
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_dec_ref(v___y_1340_);
lean_dec_ref(v___x_1338_);
lean_dec_ref(v___x_1272_);
lean_dec(v___x_1223_);
v_a_1358_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1348_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1348_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
v___jp_1366_:
{
lean_object* v___x_1370_; 
lean_inc_ref(v_fst_1368_);
lean_inc_ref(v_e_1224_);
v___x_1370_ = l_Lean_Meta_isExprDefEq(v_e_1224_, v_fst_1368_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v_a_1371_; uint8_t v___x_1372_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc(v_a_1371_);
lean_dec_ref_known(v___x_1370_, 1);
v___x_1372_ = lean_unbox(v_a_1371_);
lean_dec(v_a_1371_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_dec_ref(v_snd_1369_);
lean_dec_ref(v___x_1338_);
lean_dec_ref(v___x_1272_);
v___x_1373_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1374_ = l_Lean_MessageData_ofExpr(v_fst_1368_);
v___x_1375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1373_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
v___x_1376_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1375_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
v___x_1378_ = l_Lean_MessageData_ofConstName(v___x_1223_, v___y_1225_);
v___x_1379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1377_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
v___x_1380_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1379_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = l_Lean_MessageData_ofExpr(v_e_1224_);
v___x_1383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1381_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
v___x_1384_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_1385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1383_);
lean_ctor_set(v___x_1385_, 1, v___x_1384_);
v___x_1386_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1385_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
else
{
lean_dec_ref(v_fst_1368_);
lean_dec_ref(v_e_1224_);
v___y_1340_ = v_snd_1369_;
v___y_1341_ = v_fst_1367_;
v___y_1342_ = v___y_1228_;
v___y_1343_ = v___y_1229_;
v___y_1344_ = v___y_1230_;
v___y_1345_ = v___y_1231_;
goto v___jp_1339_;
}
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
lean_dec_ref(v_snd_1369_);
lean_dec_ref(v_fst_1368_);
lean_dec_ref(v___x_1338_);
lean_dec_ref(v___x_1272_);
lean_dec_ref(v_e_1224_);
lean_dec(v___x_1223_);
v_a_1395_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___x_1370_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1370_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3___boxed(lean_object* v___x_1430_, lean_object* v___x_1431_, lean_object* v_fst_1432_, lean_object* v___x_1433_, lean_object* v_e_1434_, lean_object* v___y_1435_, lean_object* v_snd_1436_, lean_object* v_____r_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
uint8_t v___x_85392__boxed_1443_; uint8_t v___y_85396__boxed_1444_; lean_object* v_res_1445_; 
v___x_85392__boxed_1443_ = lean_unbox(v___x_1430_);
v___y_85396__boxed_1444_ = lean_unbox(v___y_1435_);
v_res_1445_ = l_Lean_Meta_rwMatcher___lam__3(v___x_85392__boxed_1443_, v___x_1431_, v_fst_1432_, v___x_1433_, v_e_1434_, v___y_85396__boxed_1444_, v_snd_1436_, v_____r_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec_ref(v_snd_1436_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4(uint8_t v___x_1446_, lean_object* v___x_1447_, lean_object* v_fst_1448_, lean_object* v___x_1449_, lean_object* v_e_1450_, uint8_t v___y_1451_, lean_object* v_snd_1452_, lean_object* v_____r_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v___y_1460_; lean_object* v_proof_1461_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; uint8_t v___y_1486_; lean_object* v___x_1498_; uint8_t v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1516_; lean_object* v___y_1517_; uint8_t v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v_a_1522_; lean_object* v___y_1546_; lean_object* v___y_1547_; uint8_t v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; size_t v_sz_1562_; size_t v___x_1563_; lean_object* v___x_1564_; uint8_t v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; uint8_t v_fst_1593_; lean_object* v_fst_1594_; lean_object* v_snd_1595_; lean_object* v___x_1629_; lean_object* v___x_1630_; uint8_t v___x_1631_; 
v___x_1498_ = l_Lean_mkAppN(v___x_1447_, v_fst_1448_);
v_sz_1562_ = lean_array_size(v_fst_1448_);
v___x_1563_ = ((size_t)0ULL);
v___x_1564_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_1562_, v___x_1563_, v_fst_1448_);
v___x_1629_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1630_ = lean_unsigned_to_nat(4u);
v___x_1631_ = l_Lean_Expr_isAppOfArity(v_snd_1452_, v___x_1629_, v___x_1630_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; lean_object* v___x_1633_; uint8_t v___x_1634_; 
v___x_1632_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1633_ = lean_unsigned_to_nat(3u);
v___x_1634_ = l_Lean_Expr_isAppOfArity(v_snd_1452_, v___x_1632_, v___x_1633_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_dec_ref(v___x_1564_);
lean_dec_ref(v___x_1498_);
lean_dec_ref(v_e_1450_);
v___x_1635_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1636_ = l_Lean_MessageData_ofConstName(v___x_1449_, v___y_1451_);
v___x_1637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1635_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
v___x_1638_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1637_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1639_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1640_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1640_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
else
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1649_ = l_Lean_Expr_appFn_x21(v_snd_1452_);
v___x_1650_ = l_Lean_Expr_appArg_x21(v___x_1649_);
lean_dec_ref(v___x_1649_);
v___x_1651_ = l_Lean_Expr_appArg_x21(v_snd_1452_);
v_fst_1593_ = v___y_1451_;
v_fst_1594_ = v___x_1650_;
v_snd_1595_ = v___x_1651_;
goto v___jp_1592_;
}
}
else
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1652_ = l_Lean_Expr_appFn_x21(v_snd_1452_);
v___x_1653_ = l_Lean_Expr_appFn_x21(v___x_1652_);
lean_dec_ref(v___x_1652_);
v___x_1654_ = l_Lean_Expr_appArg_x21(v___x_1653_);
lean_dec_ref(v___x_1653_);
v___x_1655_ = l_Lean_Expr_appArg_x21(v_snd_1452_);
v_fst_1593_ = v___x_1446_;
v_fst_1594_ = v___x_1654_;
v_snd_1595_ = v___x_1655_;
goto v___jp_1592_;
}
v___jp_1459_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1462_, 0, v_proof_1461_);
v___x_1463_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1463_, 0, v___y_1460_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
lean_ctor_set_uint8(v___x_1463_, sizeof(void*)*2, v___x_1446_);
v___x_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1463_);
return v___x_1464_;
}
v___jp_1465_:
{
if (lean_obj_tag(v___y_1467_) == 0)
{
lean_object* v_a_1468_; 
v_a_1468_ = lean_ctor_get(v___y_1467_, 0);
lean_inc(v_a_1468_);
lean_dec_ref_known(v___y_1467_, 1);
v___y_1460_ = v___y_1466_;
v_proof_1461_ = v_a_1468_;
goto v___jp_1459_;
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_dec_ref(v___y_1466_);
v_a_1469_ = lean_ctor_get(v___y_1467_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___y_1467_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___y_1467_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___y_1467_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
v___jp_1477_:
{
if (v___y_1486_ == 0)
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
lean_dec_ref(v___y_1481_);
v___x_1487_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1488_ = l_Lean_MessageData_ofExpr(v___y_1478_);
v___x_1489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1487_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1489_);
lean_ctor_set(v___x_1491_, 1, v___x_1490_);
v___x_1492_ = l_Lean_Exception_toMessageData(v___y_1485_);
v___x_1493_ = l_Lean_indentD(v___x_1492_);
v___x_1494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1491_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
v___x_1495_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1494_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
v___x_1497_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1496_, v___y_1480_, v___y_1484_, v___y_1483_, v___y_1482_);
v___y_1466_ = v___y_1479_;
v___y_1467_ = v___x_1497_;
goto v___jp_1465_;
}
else
{
lean_dec_ref(v___y_1485_);
lean_dec_ref(v___y_1478_);
v___y_1466_ = v___y_1479_;
v___y_1467_ = v___y_1481_;
goto v___jp_1465_;
}
}
v___jp_1499_:
{
lean_object* v___x_1506_; lean_object* v_a_1507_; lean_object* v___x_1508_; 
v___x_1506_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_1501_, v___y_1503_);
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_a_1507_);
lean_dec_ref(v___x_1506_);
v___x_1508_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___x_1498_, v___y_1503_);
if (v___y_1500_ == 0)
{
lean_object* v_a_1509_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_a_1509_);
lean_dec_ref(v___x_1508_);
v___y_1460_ = v_a_1507_;
v_proof_1461_ = v_a_1509_;
goto v___jp_1459_;
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1511_; 
v_a_1510_ = lean_ctor_get(v___x_1508_, 0);
lean_inc_n(v_a_1510_, 2);
lean_dec_ref(v___x_1508_);
v___x_1511_ = l_Lean_Meta_mkEqOfHEq(v_a_1510_, v___x_1446_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_dec(v_a_1510_);
v___y_1466_ = v_a_1507_;
v___y_1467_ = v___x_1511_;
goto v___jp_1465_;
}
else
{
lean_object* v_a_1512_; uint8_t v___x_1513_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_a_1512_);
v___x_1513_ = l_Lean_Exception_isInterrupt(v_a_1512_);
if (v___x_1513_ == 0)
{
uint8_t v___x_1514_; 
lean_inc(v_a_1512_);
v___x_1514_ = l_Lean_Exception_isRuntime(v_a_1512_);
v___y_1478_ = v_a_1510_;
v___y_1479_ = v_a_1507_;
v___y_1480_ = v___y_1502_;
v___y_1481_ = v___x_1511_;
v___y_1482_ = v___y_1505_;
v___y_1483_ = v___y_1504_;
v___y_1484_ = v___y_1503_;
v___y_1485_ = v_a_1512_;
v___y_1486_ = v___x_1514_;
goto v___jp_1477_;
}
else
{
v___y_1478_ = v_a_1510_;
v___y_1479_ = v_a_1507_;
v___y_1480_ = v___y_1502_;
v___y_1481_ = v___x_1511_;
v___y_1482_ = v___y_1505_;
v___y_1483_ = v___y_1504_;
v___y_1484_ = v___y_1503_;
v___y_1485_ = v_a_1512_;
v___y_1486_ = v___x_1513_;
goto v___jp_1477_;
}
}
}
}
v___jp_1515_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; 
v___x_1523_ = lean_array_get_size(v_a_1522_);
v___x_1524_ = lean_unsigned_to_nat(0u);
v___x_1525_ = lean_nat_dec_eq(v___x_1523_, v___x_1524_);
if (v___x_1525_ == 0)
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
lean_dec_ref(v___y_1519_);
lean_dec_ref(v___x_1498_);
v___x_1526_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1527_ = l_Lean_MessageData_ofConstName(v___x_1449_, v___x_1525_);
v___x_1528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1526_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
v___x_1529_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1528_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
v___x_1531_ = lean_array_to_list(v_a_1522_);
v___x_1532_ = lean_box(0);
v___x_1533_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_1531_, v___x_1532_);
v___x_1534_ = l_Lean_MessageData_ofList(v___x_1533_);
v___x_1535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1530_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
v___x_1536_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1535_, v___y_1516_, v___y_1520_, v___y_1521_, v___y_1517_);
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1536_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
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
else
{
lean_dec_ref(v_a_1522_);
lean_dec(v___x_1449_);
v___y_1500_ = v___y_1518_;
v___y_1501_ = v___y_1519_;
v___y_1502_ = v___y_1516_;
v___y_1503_ = v___y_1520_;
v___y_1504_ = v___y_1521_;
v___y_1505_ = v___y_1517_;
goto v___jp_1499_;
}
}
v___jp_1545_:
{
if (lean_obj_tag(v___y_1552_) == 0)
{
lean_object* v_a_1553_; 
v_a_1553_ = lean_ctor_get(v___y_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref_known(v___y_1552_, 1);
v___y_1516_ = v___y_1546_;
v___y_1517_ = v___y_1547_;
v___y_1518_ = v___y_1548_;
v___y_1519_ = v___y_1549_;
v___y_1520_ = v___y_1550_;
v___y_1521_ = v___y_1551_;
v_a_1522_ = v_a_1553_;
goto v___jp_1515_;
}
else
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
lean_dec_ref(v___y_1549_);
lean_dec_ref(v___x_1498_);
lean_dec(v___x_1449_);
v_a_1554_ = lean_ctor_get(v___y_1552_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___y_1552_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___y_1552_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___y_1552_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
v___jp_1565_:
{
lean_object* v___x_1572_; size_t v_sz_1573_; lean_object* v___x_1574_; 
v___x_1572_ = lean_box(0);
v_sz_1573_ = lean_array_size(v___x_1564_);
v___x_1574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1564_, v_sz_1573_, v___x_1563_, v___x_1572_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; uint8_t v___x_1578_; 
lean_dec_ref_known(v___x_1574_, 1);
v___x_1575_ = lean_unsigned_to_nat(0u);
v___x_1576_ = lean_array_get_size(v___x_1564_);
v___x_1577_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1578_ = lean_nat_dec_lt(v___x_1575_, v___x_1576_);
if (v___x_1578_ == 0)
{
lean_dec_ref(v___x_1564_);
v___y_1516_ = v___y_1568_;
v___y_1517_ = v___y_1571_;
v___y_1518_ = v___y_1566_;
v___y_1519_ = v___y_1567_;
v___y_1520_ = v___y_1569_;
v___y_1521_ = v___y_1570_;
v_a_1522_ = v___x_1577_;
goto v___jp_1515_;
}
else
{
uint8_t v___x_1579_; 
v___x_1579_ = lean_nat_dec_le(v___x_1576_, v___x_1576_);
if (v___x_1579_ == 0)
{
if (v___x_1578_ == 0)
{
lean_dec_ref(v___x_1564_);
v___y_1516_ = v___y_1568_;
v___y_1517_ = v___y_1571_;
v___y_1518_ = v___y_1566_;
v___y_1519_ = v___y_1567_;
v___y_1520_ = v___y_1569_;
v___y_1521_ = v___y_1570_;
v_a_1522_ = v___x_1577_;
goto v___jp_1515_;
}
else
{
size_t v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = lean_usize_of_nat(v___x_1576_);
v___x_1581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1564_, v___x_1563_, v___x_1580_, v___x_1577_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
lean_dec_ref(v___x_1564_);
v___y_1546_ = v___y_1568_;
v___y_1547_ = v___y_1571_;
v___y_1548_ = v___y_1566_;
v___y_1549_ = v___y_1567_;
v___y_1550_ = v___y_1569_;
v___y_1551_ = v___y_1570_;
v___y_1552_ = v___x_1581_;
goto v___jp_1545_;
}
}
else
{
size_t v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = lean_usize_of_nat(v___x_1576_);
v___x_1583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1564_, v___x_1563_, v___x_1582_, v___x_1577_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
lean_dec_ref(v___x_1564_);
v___y_1546_ = v___y_1568_;
v___y_1547_ = v___y_1571_;
v___y_1548_ = v___y_1566_;
v___y_1549_ = v___y_1567_;
v___y_1550_ = v___y_1569_;
v___y_1551_ = v___y_1570_;
v___y_1552_ = v___x_1583_;
goto v___jp_1545_;
}
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_dec_ref(v___y_1567_);
lean_dec_ref(v___x_1564_);
lean_dec_ref(v___x_1498_);
lean_dec(v___x_1449_);
v_a_1584_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1574_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1574_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
v___jp_1592_:
{
lean_object* v___x_1596_; 
lean_inc_ref(v_fst_1594_);
lean_inc_ref(v_e_1450_);
v___x_1596_ = l_Lean_Meta_isExprDefEq(v_e_1450_, v_fst_1594_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_a_1597_; uint8_t v___x_1598_; 
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_a_1597_);
lean_dec_ref_known(v___x_1596_, 1);
v___x_1598_ = lean_unbox(v_a_1597_);
lean_dec(v_a_1597_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec_ref(v_snd_1595_);
lean_dec_ref(v___x_1564_);
lean_dec_ref(v___x_1498_);
v___x_1599_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1600_ = l_Lean_MessageData_ofExpr(v_fst_1594_);
v___x_1601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1599_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
v___x_1602_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1601_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
v___x_1604_ = l_Lean_MessageData_ofConstName(v___x_1449_, v___y_1451_);
v___x_1605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1603_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
v___x_1606_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1605_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
v___x_1608_ = l_Lean_MessageData_ofExpr(v_e_1450_);
v___x_1609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1607_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
v___x_1610_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_1611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1609_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
v___x_1612_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1611_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1612_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1612_);
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
else
{
lean_dec_ref(v_fst_1594_);
lean_dec_ref(v_e_1450_);
v___y_1566_ = v_fst_1593_;
v___y_1567_ = v_snd_1595_;
v___y_1568_ = v___y_1454_;
v___y_1569_ = v___y_1455_;
v___y_1570_ = v___y_1456_;
v___y_1571_ = v___y_1457_;
goto v___jp_1565_;
}
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec_ref(v_snd_1595_);
lean_dec_ref(v_fst_1594_);
lean_dec_ref(v___x_1564_);
lean_dec_ref(v___x_1498_);
lean_dec_ref(v_e_1450_);
lean_dec(v___x_1449_);
v_a_1621_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1596_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1596_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4___boxed(lean_object* v___x_1656_, lean_object* v___x_1657_, lean_object* v_fst_1658_, lean_object* v___x_1659_, lean_object* v_e_1660_, lean_object* v___y_1661_, lean_object* v_snd_1662_, lean_object* v_____r_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
uint8_t v___x_85877__boxed_1669_; uint8_t v___y_85881__boxed_1670_; lean_object* v_res_1671_; 
v___x_85877__boxed_1669_ = lean_unbox(v___x_1656_);
v___y_85881__boxed_1670_ = lean_unbox(v___y_1661_);
v_res_1671_ = l_Lean_Meta_rwMatcher___lam__4(v___x_85877__boxed_1669_, v___x_1657_, v_fst_1658_, v___x_1659_, v_e_1660_, v___y_85881__boxed_1670_, v_snd_1662_, v_____r_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec_ref(v_snd_1662_);
return v_res_1671_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1672_; double v___x_1673_; 
v___x_1672_ = lean_unsigned_to_nat(0u);
v___x_1673_ = lean_float_of_nat(v___x_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(lean_object* v_cls_1677_, lean_object* v_msg_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_ref_1684_; lean_object* v___x_1685_; lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1731_; 
v_ref_1684_ = lean_ctor_get(v___y_1681_, 2);
v___x_1685_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1688_ = v___x_1685_;
v_isShared_1689_ = v_isSharedCheck_1731_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1685_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1731_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1690_; lean_object* v_traceState_1691_; lean_object* v_env_1692_; lean_object* v_nextMacroScope_1693_; lean_object* v_ngen_1694_; lean_object* v_auxDeclNGen_1695_; lean_object* v_cache_1696_; lean_object* v_recordedDeps_1697_; lean_object* v_messages_1698_; lean_object* v_infoState_1699_; lean_object* v_snapshotTasks_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1730_; 
v___x_1690_ = lean_st_ref_take(v___y_1682_);
v_traceState_1691_ = lean_ctor_get(v___x_1690_, 4);
v_env_1692_ = lean_ctor_get(v___x_1690_, 0);
v_nextMacroScope_1693_ = lean_ctor_get(v___x_1690_, 1);
v_ngen_1694_ = lean_ctor_get(v___x_1690_, 2);
v_auxDeclNGen_1695_ = lean_ctor_get(v___x_1690_, 3);
v_cache_1696_ = lean_ctor_get(v___x_1690_, 5);
v_recordedDeps_1697_ = lean_ctor_get(v___x_1690_, 6);
v_messages_1698_ = lean_ctor_get(v___x_1690_, 7);
v_infoState_1699_ = lean_ctor_get(v___x_1690_, 8);
v_snapshotTasks_1700_ = lean_ctor_get(v___x_1690_, 9);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1702_ = v___x_1690_;
v_isShared_1703_ = v_isSharedCheck_1730_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_snapshotTasks_1700_);
lean_inc(v_infoState_1699_);
lean_inc(v_messages_1698_);
lean_inc(v_recordedDeps_1697_);
lean_inc(v_cache_1696_);
lean_inc(v_traceState_1691_);
lean_inc(v_auxDeclNGen_1695_);
lean_inc(v_ngen_1694_);
lean_inc(v_nextMacroScope_1693_);
lean_inc(v_env_1692_);
lean_dec(v___x_1690_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1730_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
uint64_t v_tid_1704_; lean_object* v_traces_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1729_; 
v_tid_1704_ = lean_ctor_get_uint64(v_traceState_1691_, sizeof(void*)*1);
v_traces_1705_ = lean_ctor_get(v_traceState_1691_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v_traceState_1691_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1707_ = v_traceState_1691_;
v_isShared_1708_ = v_isSharedCheck_1729_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_traces_1705_);
lean_dec(v_traceState_1691_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1729_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; double v___x_1711_; uint8_t v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1720_; 
v___x_1709_ = lean_box(0);
v___x_1710_ = lean_box(0);
v___x_1711_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0);
v___x_1712_ = 0;
v___x_1713_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1));
v___x_1714_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1714_, 0, v_cls_1677_);
lean_ctor_set(v___x_1714_, 1, v___x_1710_);
lean_ctor_set(v___x_1714_, 2, v___x_1713_);
lean_ctor_set_float(v___x_1714_, sizeof(void*)*3, v___x_1711_);
lean_ctor_set_float(v___x_1714_, sizeof(void*)*3 + 8, v___x_1711_);
lean_ctor_set_uint8(v___x_1714_, sizeof(void*)*3 + 16, v___x_1712_);
v___x_1715_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__2));
v___x_1716_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1714_);
lean_ctor_set(v___x_1716_, 1, v_a_1686_);
lean_ctor_set(v___x_1716_, 2, v___x_1715_);
lean_inc(v_ref_1684_);
v___x_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1717_, 0, v_ref_1684_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v___x_1718_ = l_Lean_PersistentArray_push___redArg(v_traces_1705_, v___x_1717_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1718_);
v___x_1720_ = v___x_1707_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1718_);
lean_ctor_set_uint64(v_reuseFailAlloc_1728_, sizeof(void*)*1, v_tid_1704_);
v___x_1720_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_object* v___x_1722_; 
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 4, v___x_1720_);
v___x_1722_ = v___x_1702_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_env_1692_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v_nextMacroScope_1693_);
lean_ctor_set(v_reuseFailAlloc_1727_, 2, v_ngen_1694_);
lean_ctor_set(v_reuseFailAlloc_1727_, 3, v_auxDeclNGen_1695_);
lean_ctor_set(v_reuseFailAlloc_1727_, 4, v___x_1720_);
lean_ctor_set(v_reuseFailAlloc_1727_, 5, v_cache_1696_);
lean_ctor_set(v_reuseFailAlloc_1727_, 6, v_recordedDeps_1697_);
lean_ctor_set(v_reuseFailAlloc_1727_, 7, v_messages_1698_);
lean_ctor_set(v_reuseFailAlloc_1727_, 8, v_infoState_1699_);
lean_ctor_set(v_reuseFailAlloc_1727_, 9, v_snapshotTasks_1700_);
v___x_1722_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
lean_object* v___x_1723_; lean_object* v___x_1725_; 
v___x_1723_ = lean_st_ref_put(v___y_1682_, v___x_1722_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 0, v___x_1709_);
v___x_1725_ = v___x_1688_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1709_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___boxed(lean_object* v_cls_1732_, lean_object* v_msg_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v_cls_1732_, v_msg_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(lean_object* v_a_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Lean_Meta_reduceRecMatcher_x3f(v_a_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1760_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1749_ = v___x_1746_;
v_isShared_1750_ = v_isSharedCheck_1760_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1746_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1760_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
if (lean_obj_tag(v_a_1747_) == 1)
{
lean_object* v_val_1751_; lean_object* v___x_1752_; 
lean_del_object(v___x_1749_);
lean_dec_ref(v_a_1740_);
v_val_1751_ = lean_ctor_get(v_a_1747_, 0);
lean_inc(v_val_1751_);
lean_dec_ref_known(v_a_1747_, 1);
v___x_1752_ = l_Lean_Expr_headBeta(v_val_1751_);
v_a_1740_ = v___x_1752_;
goto _start;
}
else
{
lean_object* v___x_1754_; uint8_t v___x_1755_; 
lean_dec(v_a_1747_);
lean_inc_ref(v_a_1740_);
v___x_1754_ = l_Lean_Expr_headBeta(v_a_1740_);
v___x_1755_ = lean_expr_eqv(v_a_1740_, v___x_1754_);
if (v___x_1755_ == 0)
{
lean_del_object(v___x_1749_);
lean_dec_ref(v_a_1740_);
v_a_1740_ = v___x_1754_;
goto _start;
}
else
{
lean_object* v___x_1758_; 
lean_dec_ref(v___x_1754_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v_a_1740_);
v___x_1758_ = v___x_1749_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1740_);
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
lean_dec_ref(v_a_1740_);
v_a_1761_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1746_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1746_);
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
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg___boxed(lean_object* v_a_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(v_a_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(lean_object* v_opts_1776_, lean_object* v_opt_1777_){
_start:
{
lean_object* v_name_1778_; lean_object* v_defValue_1779_; lean_object* v_map_1780_; lean_object* v___x_1781_; 
v_name_1778_ = lean_ctor_get(v_opt_1777_, 0);
v_defValue_1779_ = lean_ctor_get(v_opt_1777_, 1);
v_map_1780_ = lean_ctor_get(v_opts_1776_, 0);
v___x_1781_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1780_, v_name_1778_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_inc(v_defValue_1779_);
return v_defValue_1779_;
}
else
{
lean_object* v_val_1782_; 
v_val_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_val_1782_);
lean_dec_ref_known(v___x_1781_, 1);
if (lean_obj_tag(v_val_1782_) == 3)
{
lean_object* v_v_1783_; 
v_v_1783_ = lean_ctor_get(v_val_1782_, 0);
lean_inc(v_v_1783_);
lean_dec_ref_known(v_val_1782_, 1);
return v_v_1783_;
}
else
{
lean_dec(v_val_1782_);
lean_inc(v_defValue_1779_);
return v_defValue_1779_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16___boxed(lean_object* v_opts_1784_, lean_object* v_opt_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_1784_, v_opt_1785_);
lean_dec_ref(v_opt_1785_);
lean_dec_ref(v_opts_1784_);
return v_res_1786_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(lean_object* v_e_1787_){
_start:
{
if (lean_obj_tag(v_e_1787_) == 0)
{
uint8_t v___x_1788_; 
v___x_1788_ = 2;
return v___x_1788_;
}
else
{
uint8_t v___x_1789_; 
v___x_1789_ = 0;
return v___x_1789_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___boxed(lean_object* v_e_1790_){
_start:
{
uint8_t v_res_1791_; lean_object* v_r_1792_; 
v_res_1791_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(v_e_1790_);
lean_dec_ref(v_e_1790_);
v_r_1792_ = lean_box(v_res_1791_);
return v_r_1792_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(lean_object* v_x_1793_){
_start:
{
if (lean_obj_tag(v_x_1793_) == 0)
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
v_a_1795_ = lean_ctor_get(v_x_1793_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_x_1793_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v_x_1793_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v_x_1793_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
lean_ctor_set_tag(v___x_1797_, 1);
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
v_a_1803_ = lean_ctor_get(v_x_1793_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v_x_1793_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v_x_1793_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v_x_1793_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
lean_ctor_set_tag(v___x_1805_, 0);
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1803_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg___boxed(lean_object* v_x_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(v_x_1811_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15(size_t v_sz_1814_, size_t v_i_1815_, lean_object* v_bs_1816_){
_start:
{
uint8_t v___x_1817_; 
v___x_1817_ = lean_usize_dec_lt(v_i_1815_, v_sz_1814_);
if (v___x_1817_ == 0)
{
return v_bs_1816_;
}
else
{
lean_object* v_v_1818_; lean_object* v_msg_1819_; lean_object* v___x_1820_; lean_object* v_bs_x27_1821_; size_t v___x_1822_; size_t v___x_1823_; lean_object* v___x_1824_; 
v_v_1818_ = lean_array_uget_borrowed(v_bs_1816_, v_i_1815_);
v_msg_1819_ = lean_ctor_get(v_v_1818_, 1);
lean_inc_ref(v_msg_1819_);
v___x_1820_ = lean_unsigned_to_nat(0u);
v_bs_x27_1821_ = lean_array_uset(v_bs_1816_, v_i_1815_, v___x_1820_);
v___x_1822_ = ((size_t)1ULL);
v___x_1823_ = lean_usize_add(v_i_1815_, v___x_1822_);
v___x_1824_ = lean_array_uset(v_bs_x27_1821_, v_i_1815_, v_msg_1819_);
v_i_1815_ = v___x_1823_;
v_bs_1816_ = v___x_1824_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15___boxed(lean_object* v_sz_1826_, lean_object* v_i_1827_, lean_object* v_bs_1828_){
_start:
{
size_t v_sz_boxed_1829_; size_t v_i_boxed_1830_; lean_object* v_res_1831_; 
v_sz_boxed_1829_ = lean_unbox_usize(v_sz_1826_);
lean_dec(v_sz_1826_);
v_i_boxed_1830_ = lean_unbox_usize(v_i_1827_);
lean_dec(v_i_1827_);
v_res_1831_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15(v_sz_boxed_1829_, v_i_boxed_1830_, v_bs_1828_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(lean_object* v_oldTraces_1832_, lean_object* v_data_1833_, lean_object* v_ref_1834_, lean_object* v_msg_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v_toCold_1841_; lean_object* v_currRecDepth_1842_; lean_object* v_ref_1843_; uint16_t v_optionFlags_1844_; uint8_t v_suppressElabErrors_1845_; uint8_t v_isRecordingDeps_1846_; lean_object* v_ref_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v_traceState_1850_; lean_object* v_traces_1851_; lean_object* v___x_1852_; size_t v_sz_1853_; size_t v___x_1854_; lean_object* v___x_1855_; lean_object* v_msg_1856_; lean_object* v___x_1857_; lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1896_; 
v_toCold_1841_ = lean_ctor_get(v___y_1838_, 0);
v_currRecDepth_1842_ = lean_ctor_get(v___y_1838_, 1);
v_ref_1843_ = lean_ctor_get(v___y_1838_, 2);
v_optionFlags_1844_ = lean_ctor_get_uint16(v___y_1838_, sizeof(void*)*3);
v_suppressElabErrors_1845_ = lean_ctor_get_uint8(v___y_1838_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1846_ = lean_ctor_get_uint8(v___y_1838_, sizeof(void*)*3 + 3);
v_ref_1847_ = l_Lean_replaceRef(v_ref_1834_, v_ref_1843_);
lean_inc(v_currRecDepth_1842_);
lean_inc_ref(v_toCold_1841_);
v___x_1848_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1848_, 0, v_toCold_1841_);
lean_ctor_set(v___x_1848_, 1, v_currRecDepth_1842_);
lean_ctor_set(v___x_1848_, 2, v_ref_1847_);
lean_ctor_set_uint16(v___x_1848_, sizeof(void*)*3, v_optionFlags_1844_);
lean_ctor_set_uint8(v___x_1848_, sizeof(void*)*3 + 2, v_suppressElabErrors_1845_);
lean_ctor_set_uint8(v___x_1848_, sizeof(void*)*3 + 3, v_isRecordingDeps_1846_);
v___x_1849_ = lean_st_ref_get(v___y_1839_);
v_traceState_1850_ = lean_ctor_get(v___x_1849_, 4);
lean_inc_ref(v_traceState_1850_);
lean_dec(v___x_1849_);
v_traces_1851_ = lean_ctor_get(v_traceState_1850_, 0);
lean_inc_ref(v_traces_1851_);
lean_dec_ref(v_traceState_1850_);
v___x_1852_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1851_);
lean_dec_ref(v_traces_1851_);
v_sz_1853_ = lean_array_size(v___x_1852_);
v___x_1854_ = ((size_t)0ULL);
v___x_1855_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15(v_sz_1853_, v___x_1854_, v___x_1852_);
v_msg_1856_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1856_, 0, v_data_1833_);
lean_ctor_set(v_msg_1856_, 1, v_msg_1835_);
lean_ctor_set(v_msg_1856_, 2, v___x_1855_);
v___x_1857_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_1856_, v___y_1836_, v___y_1837_, v___x_1848_, v___y_1839_);
lean_dec_ref_known(v___x_1848_, 3);
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1860_ = v___x_1857_;
v_isShared_1861_ = v_isSharedCheck_1896_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1857_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1896_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1862_; lean_object* v_traceState_1863_; lean_object* v_env_1864_; lean_object* v_nextMacroScope_1865_; lean_object* v_ngen_1866_; lean_object* v_auxDeclNGen_1867_; lean_object* v_cache_1868_; lean_object* v_recordedDeps_1869_; lean_object* v_messages_1870_; lean_object* v_infoState_1871_; lean_object* v_snapshotTasks_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1895_; 
v___x_1862_ = lean_st_ref_take(v___y_1839_);
v_traceState_1863_ = lean_ctor_get(v___x_1862_, 4);
v_env_1864_ = lean_ctor_get(v___x_1862_, 0);
v_nextMacroScope_1865_ = lean_ctor_get(v___x_1862_, 1);
v_ngen_1866_ = lean_ctor_get(v___x_1862_, 2);
v_auxDeclNGen_1867_ = lean_ctor_get(v___x_1862_, 3);
v_cache_1868_ = lean_ctor_get(v___x_1862_, 5);
v_recordedDeps_1869_ = lean_ctor_get(v___x_1862_, 6);
v_messages_1870_ = lean_ctor_get(v___x_1862_, 7);
v_infoState_1871_ = lean_ctor_get(v___x_1862_, 8);
v_snapshotTasks_1872_ = lean_ctor_get(v___x_1862_, 9);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1874_ = v___x_1862_;
v_isShared_1875_ = v_isSharedCheck_1895_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_snapshotTasks_1872_);
lean_inc(v_infoState_1871_);
lean_inc(v_messages_1870_);
lean_inc(v_recordedDeps_1869_);
lean_inc(v_cache_1868_);
lean_inc(v_traceState_1863_);
lean_inc(v_auxDeclNGen_1867_);
lean_inc(v_ngen_1866_);
lean_inc(v_nextMacroScope_1865_);
lean_inc(v_env_1864_);
lean_dec(v___x_1862_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1895_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
uint64_t v_tid_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1893_; 
v_tid_1876_ = lean_ctor_get_uint64(v_traceState_1863_, sizeof(void*)*1);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_traceState_1863_);
if (v_isSharedCheck_1893_ == 0)
{
lean_object* v_unused_1894_; 
v_unused_1894_ = lean_ctor_get(v_traceState_1863_, 0);
lean_dec(v_unused_1894_);
v___x_1878_ = v_traceState_1863_;
v_isShared_1879_ = v_isSharedCheck_1893_;
goto v_resetjp_1877_;
}
else
{
lean_dec(v_traceState_1863_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1893_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1884_; 
v___x_1880_ = lean_box(0);
v___x_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1881_, 0, v_ref_1834_);
lean_ctor_set(v___x_1881_, 1, v_a_1858_);
v___x_1882_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1832_, v___x_1881_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v___x_1882_);
v___x_1884_ = v___x_1878_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1882_);
lean_ctor_set_uint64(v_reuseFailAlloc_1892_, sizeof(void*)*1, v_tid_1876_);
v___x_1884_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
lean_object* v___x_1886_; 
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 4, v___x_1884_);
v___x_1886_ = v___x_1874_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_env_1864_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_nextMacroScope_1865_);
lean_ctor_set(v_reuseFailAlloc_1891_, 2, v_ngen_1866_);
lean_ctor_set(v_reuseFailAlloc_1891_, 3, v_auxDeclNGen_1867_);
lean_ctor_set(v_reuseFailAlloc_1891_, 4, v___x_1884_);
lean_ctor_set(v_reuseFailAlloc_1891_, 5, v_cache_1868_);
lean_ctor_set(v_reuseFailAlloc_1891_, 6, v_recordedDeps_1869_);
lean_ctor_set(v_reuseFailAlloc_1891_, 7, v_messages_1870_);
lean_ctor_set(v_reuseFailAlloc_1891_, 8, v_infoState_1871_);
lean_ctor_set(v_reuseFailAlloc_1891_, 9, v_snapshotTasks_1872_);
v___x_1886_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1887_ = lean_st_ref_put(v___y_1839_, v___x_1886_);
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 0, v___x_1880_);
v___x_1889_ = v___x_1860_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v___x_1880_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13___boxed(lean_object* v_oldTraces_1897_, lean_object* v_data_1898_, lean_object* v_ref_1899_, lean_object* v_msg_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(v_oldTraces_1897_, v_data_1898_, v_ref_1899_, v_msg_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
return v_res_1906_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1(void){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__0));
v___x_1909_ = l_Lean_stringToMessageData(v___x_1908_);
return v___x_1909_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2(void){
_start:
{
lean_object* v___x_1910_; double v___x_1911_; 
v___x_1910_ = lean_unsigned_to_nat(1000u);
v___x_1911_ = lean_float_of_nat(v___x_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(lean_object* v_cls_1912_, uint8_t v_collapsed_1913_, lean_object* v_tag_1914_, lean_object* v_opts_1915_, uint8_t v_clsEnabled_1916_, lean_object* v_oldTraces_1917_, lean_object* v_msg_1918_, lean_object* v_resStartStop_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v_fst_1925_; lean_object* v_snd_1926_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v_data_1930_; lean_object* v_fst_1941_; lean_object* v_snd_1942_; lean_object* v___x_1943_; uint8_t v___x_1944_; lean_object* v___y_1946_; lean_object* v_a_1947_; uint8_t v___y_1962_; double v___y_1994_; 
v_fst_1925_ = lean_ctor_get(v_resStartStop_1919_, 0);
lean_inc(v_fst_1925_);
v_snd_1926_ = lean_ctor_get(v_resStartStop_1919_, 1);
lean_inc(v_snd_1926_);
lean_dec_ref(v_resStartStop_1919_);
v_fst_1941_ = lean_ctor_get(v_snd_1926_, 0);
lean_inc(v_fst_1941_);
v_snd_1942_ = lean_ctor_get(v_snd_1926_, 1);
lean_inc(v_snd_1942_);
lean_dec(v_snd_1926_);
v___x_1943_ = l_Lean_trace_profiler;
v___x_1944_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_opts_1915_, v___x_1943_);
if (v___x_1944_ == 0)
{
v___y_1962_ = v___x_1944_;
goto v___jp_1961_;
}
else
{
lean_object* v___x_1999_; uint8_t v___x_2000_; 
v___x_1999_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2000_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_opts_1915_, v___x_1999_);
if (v___x_2000_ == 0)
{
lean_object* v___x_2001_; lean_object* v___x_2002_; double v___x_2003_; double v___x_2004_; double v___x_2005_; 
v___x_2001_ = l_Lean_trace_profiler_threshold;
v___x_2002_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_1915_, v___x_2001_);
v___x_2003_ = lean_float_of_nat(v___x_2002_);
v___x_2004_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2);
v___x_2005_ = lean_float_div(v___x_2003_, v___x_2004_);
v___y_1994_ = v___x_2005_;
goto v___jp_1993_;
}
else
{
lean_object* v___x_2006_; lean_object* v___x_2007_; double v___x_2008_; 
v___x_2006_ = l_Lean_trace_profiler_threshold;
v___x_2007_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_1915_, v___x_2006_);
v___x_2008_ = lean_float_of_nat(v___x_2007_);
v___y_1994_ = v___x_2008_;
goto v___jp_1993_;
}
}
v___jp_1927_:
{
lean_object* v___x_1931_; 
lean_inc(v___y_1929_);
v___x_1931_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(v_oldTraces_1917_, v_data_1930_, v___y_1929_, v___y_1928_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v___x_1932_; 
lean_dec_ref_known(v___x_1931_, 1);
v___x_1932_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(v_fst_1925_);
return v___x_1932_;
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec(v_fst_1925_);
v_a_1933_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1931_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1931_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
v___jp_1945_:
{
uint8_t v_result_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; double v___x_1951_; lean_object* v_data_1952_; 
v_result_1948_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(v_fst_1925_);
v___x_1949_ = lean_box(v_result_1948_);
v___x_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
v___x_1951_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0);
lean_inc_ref(v_tag_1914_);
lean_inc_ref(v___x_1950_);
lean_inc(v_cls_1912_);
v_data_1952_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1952_, 0, v_cls_1912_);
lean_ctor_set(v_data_1952_, 1, v___x_1950_);
lean_ctor_set(v_data_1952_, 2, v_tag_1914_);
lean_ctor_set_float(v_data_1952_, sizeof(void*)*3, v___x_1951_);
lean_ctor_set_float(v_data_1952_, sizeof(void*)*3 + 8, v___x_1951_);
lean_ctor_set_uint8(v_data_1952_, sizeof(void*)*3 + 16, v_collapsed_1913_);
if (v___x_1944_ == 0)
{
lean_dec_ref_known(v___x_1950_, 1);
lean_dec(v_snd_1942_);
lean_dec(v_fst_1941_);
lean_dec_ref(v_tag_1914_);
lean_dec(v_cls_1912_);
v___y_1928_ = v_a_1947_;
v___y_1929_ = v___y_1946_;
v_data_1930_ = v_data_1952_;
goto v___jp_1927_;
}
else
{
lean_object* v_data_1953_; double v___x_1954_; double v___x_1955_; 
lean_dec_ref_known(v_data_1952_, 3);
v_data_1953_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1953_, 0, v_cls_1912_);
lean_ctor_set(v_data_1953_, 1, v___x_1950_);
lean_ctor_set(v_data_1953_, 2, v_tag_1914_);
v___x_1954_ = lean_unbox_float(v_fst_1941_);
lean_dec(v_fst_1941_);
lean_ctor_set_float(v_data_1953_, sizeof(void*)*3, v___x_1954_);
v___x_1955_ = lean_unbox_float(v_snd_1942_);
lean_dec(v_snd_1942_);
lean_ctor_set_float(v_data_1953_, sizeof(void*)*3 + 8, v___x_1955_);
lean_ctor_set_uint8(v_data_1953_, sizeof(void*)*3 + 16, v_collapsed_1913_);
v___y_1928_ = v_a_1947_;
v___y_1929_ = v___y_1946_;
v_data_1930_ = v_data_1953_;
goto v___jp_1927_;
}
}
v___jp_1956_:
{
lean_object* v_ref_1957_; lean_object* v___x_1958_; 
v_ref_1957_ = lean_ctor_get(v___y_1922_, 2);
lean_inc(v___y_1923_);
lean_inc_ref(v___y_1922_);
lean_inc(v___y_1921_);
lean_inc_ref(v___y_1920_);
lean_inc(v_fst_1925_);
v___x_1958_ = lean_apply_6(v_msg_1918_, v_fst_1925_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, lean_box(0));
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1959_);
lean_dec_ref_known(v___x_1958_, 1);
v___y_1946_ = v_ref_1957_;
v_a_1947_ = v_a_1959_;
goto v___jp_1945_;
}
else
{
lean_object* v___x_1960_; 
lean_dec_ref_known(v___x_1958_, 1);
v___x_1960_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1);
v___y_1946_ = v_ref_1957_;
v_a_1947_ = v___x_1960_;
goto v___jp_1945_;
}
}
v___jp_1961_:
{
if (v_clsEnabled_1916_ == 0)
{
if (v___y_1962_ == 0)
{
lean_object* v___x_1963_; lean_object* v_traceState_1964_; lean_object* v_env_1965_; lean_object* v_nextMacroScope_1966_; lean_object* v_ngen_1967_; lean_object* v_auxDeclNGen_1968_; lean_object* v_cache_1969_; lean_object* v_recordedDeps_1970_; lean_object* v_messages_1971_; lean_object* v_infoState_1972_; lean_object* v_snapshotTasks_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1992_; 
lean_dec(v_snd_1942_);
lean_dec(v_fst_1941_);
lean_dec_ref(v_msg_1918_);
lean_dec_ref(v_tag_1914_);
lean_dec(v_cls_1912_);
v___x_1963_ = lean_st_ref_take(v___y_1923_);
v_traceState_1964_ = lean_ctor_get(v___x_1963_, 4);
v_env_1965_ = lean_ctor_get(v___x_1963_, 0);
v_nextMacroScope_1966_ = lean_ctor_get(v___x_1963_, 1);
v_ngen_1967_ = lean_ctor_get(v___x_1963_, 2);
v_auxDeclNGen_1968_ = lean_ctor_get(v___x_1963_, 3);
v_cache_1969_ = lean_ctor_get(v___x_1963_, 5);
v_recordedDeps_1970_ = lean_ctor_get(v___x_1963_, 6);
v_messages_1971_ = lean_ctor_get(v___x_1963_, 7);
v_infoState_1972_ = lean_ctor_get(v___x_1963_, 8);
v_snapshotTasks_1973_ = lean_ctor_get(v___x_1963_, 9);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1975_ = v___x_1963_;
v_isShared_1976_ = v_isSharedCheck_1992_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_snapshotTasks_1973_);
lean_inc(v_infoState_1972_);
lean_inc(v_messages_1971_);
lean_inc(v_recordedDeps_1970_);
lean_inc(v_cache_1969_);
lean_inc(v_traceState_1964_);
lean_inc(v_auxDeclNGen_1968_);
lean_inc(v_ngen_1967_);
lean_inc(v_nextMacroScope_1966_);
lean_inc(v_env_1965_);
lean_dec(v___x_1963_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1992_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
uint64_t v_tid_1977_; lean_object* v_traces_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1991_; 
v_tid_1977_ = lean_ctor_get_uint64(v_traceState_1964_, sizeof(void*)*1);
v_traces_1978_ = lean_ctor_get(v_traceState_1964_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v_traceState_1964_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1980_ = v_traceState_1964_;
v_isShared_1981_ = v_isSharedCheck_1991_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_traces_1978_);
lean_dec(v_traceState_1964_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1991_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1982_; lean_object* v___x_1984_; 
v___x_1982_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1917_, v_traces_1978_);
lean_dec_ref(v_traces_1978_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_1982_);
v___x_1984_ = v___x_1980_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1982_);
lean_ctor_set_uint64(v_reuseFailAlloc_1990_, sizeof(void*)*1, v_tid_1977_);
v___x_1984_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1986_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 4, v___x_1984_);
v___x_1986_ = v___x_1975_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_env_1965_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v_nextMacroScope_1966_);
lean_ctor_set(v_reuseFailAlloc_1989_, 2, v_ngen_1967_);
lean_ctor_set(v_reuseFailAlloc_1989_, 3, v_auxDeclNGen_1968_);
lean_ctor_set(v_reuseFailAlloc_1989_, 4, v___x_1984_);
lean_ctor_set(v_reuseFailAlloc_1989_, 5, v_cache_1969_);
lean_ctor_set(v_reuseFailAlloc_1989_, 6, v_recordedDeps_1970_);
lean_ctor_set(v_reuseFailAlloc_1989_, 7, v_messages_1971_);
lean_ctor_set(v_reuseFailAlloc_1989_, 8, v_infoState_1972_);
lean_ctor_set(v_reuseFailAlloc_1989_, 9, v_snapshotTasks_1973_);
v___x_1986_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = lean_st_ref_put(v___y_1923_, v___x_1986_);
v___x_1988_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(v_fst_1925_);
return v___x_1988_;
}
}
}
}
}
else
{
goto v___jp_1956_;
}
}
else
{
goto v___jp_1956_;
}
}
v___jp_1993_:
{
double v___x_1995_; double v___x_1996_; double v___x_1997_; uint8_t v___x_1998_; 
v___x_1995_ = lean_unbox_float(v_snd_1942_);
v___x_1996_ = lean_unbox_float(v_fst_1941_);
v___x_1997_ = lean_float_sub(v___x_1995_, v___x_1996_);
v___x_1998_ = lean_float_decLt(v___y_1994_, v___x_1997_);
v___y_1962_ = v___x_1998_;
goto v___jp_1961_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___boxed(lean_object* v_cls_2009_, lean_object* v_collapsed_2010_, lean_object* v_tag_2011_, lean_object* v_opts_2012_, lean_object* v_clsEnabled_2013_, lean_object* v_oldTraces_2014_, lean_object* v_msg_2015_, lean_object* v_resStartStop_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
uint8_t v_collapsed_boxed_2022_; uint8_t v_clsEnabled_boxed_2023_; lean_object* v_res_2024_; 
v_collapsed_boxed_2022_ = lean_unbox(v_collapsed_2010_);
v_clsEnabled_boxed_2023_ = lean_unbox(v_clsEnabled_2013_);
v_res_2024_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v_cls_2009_, v_collapsed_boxed_2022_, v_tag_2011_, v_opts_2012_, v_clsEnabled_boxed_2023_, v_oldTraces_2014_, v_msg_2015_, v_resStartStop_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec_ref(v_opts_2012_);
return v_res_2024_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__3(void){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__2));
v___x_2030_ = l_Lean_stringToMessageData(v___x_2029_);
return v___x_2030_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__5(void){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__4));
v___x_2033_ = l_Lean_stringToMessageData(v___x_2032_);
return v___x_2033_;
}
}
static double _init_l_Lean_Meta_rwMatcher___closed__6(void){
_start:
{
lean_object* v___x_2034_; double v___x_2035_; 
v___x_2034_ = lean_unsigned_to_nat(1000000000u);
v___x_2035_ = lean_float_of_nat(v___x_2034_);
return v___x_2035_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__8(void){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__7));
v___x_2038_ = l_Lean_stringToMessageData(v___x_2037_);
return v___x_2038_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__13(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2046_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2047_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
v___x_2048_ = l_Lean_Name_append(v___x_2047_, v___x_2046_);
return v___x_2048_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__15(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__14));
v___x_2051_ = l_Lean_stringToMessageData(v___x_2050_);
return v___x_2051_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__17(void){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__16));
v___x_2054_ = l_Lean_stringToMessageData(v___x_2053_);
return v___x_2054_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__19(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__18));
v___x_2057_ = l_Lean_stringToMessageData(v___x_2056_);
return v___x_2057_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__21(void){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__20));
v___x_2060_ = l_Lean_stringToMessageData(v___x_2059_);
return v___x_2060_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__22(void){
_start:
{
lean_object* v___x_2061_; lean_object* v_dummy_2062_; 
v___x_2061_ = lean_box(0);
v_dummy_2062_ = l_Lean_Expr_sort___override(v___x_2061_);
return v_dummy_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher(lean_object* v_altIdx_2072_, lean_object* v_e_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_){
_start:
{
lean_object* v___y_2080_; lean_object* v___y_2099_; uint8_t v___y_2103_; lean_object* v___y_2104_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; uint8_t v___y_2108_; uint8_t v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v_a_2141_; uint8_t v___y_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; uint8_t v___y_2152_; lean_object* v___y_2153_; uint8_t v___y_2154_; lean_object* v___y_2155_; uint8_t v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v_a_2163_; uint8_t v___y_2173_; lean_object* v___y_2174_; uint8_t v___y_2175_; lean_object* v___y_2176_; uint8_t v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v___y_2182_; lean_object* v___y_2183_; lean_object* v_a_2184_; uint8_t v___y_2187_; lean_object* v___y_2188_; uint8_t v___y_2189_; lean_object* v___y_2190_; uint8_t v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v___y_2194_; lean_object* v___y_2195_; lean_object* v___y_2196_; lean_object* v___y_2197_; lean_object* v___y_2198_; lean_object* v___y_2209_; uint8_t v___y_2210_; lean_object* v___y_2211_; uint8_t v___y_2212_; lean_object* v___y_2213_; uint8_t v___y_2214_; lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v_a_2220_; lean_object* v___y_2233_; uint8_t v___y_2234_; lean_object* v___y_2235_; uint8_t v___y_2236_; lean_object* v___y_2237_; uint8_t v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v_a_2244_; lean_object* v___y_2247_; uint8_t v___y_2248_; lean_object* v___y_2249_; uint8_t v___y_2250_; lean_object* v___y_2251_; uint8_t v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; uint8_t v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; uint8_t v___y_2272_; lean_object* v___y_2273_; uint8_t v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; uint8_t v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; uint8_t v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; uint8_t v___y_2349_; uint8_t v___y_2354_; uint8_t v___y_2359_; lean_object* v___y_2360_; lean_object* v_proof_2361_; uint8_t v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2368_; uint8_t v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2376_; uint8_t v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; uint8_t v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; uint8_t v___y_2389_; uint8_t v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; uint8_t v___y_2407_; lean_object* v___y_2408_; uint8_t v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; uint8_t v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; uint8_t v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2432_; uint8_t v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v_a_2436_; uint8_t v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; uint8_t v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; uint8_t v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2469_; uint8_t v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; uint8_t v___y_2475_; size_t v___y_2476_; lean_object* v___y_2477_; uint8_t v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2497_; uint8_t v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; uint8_t v___y_2502_; size_t v___y_2503_; lean_object* v___y_2504_; uint8_t v_fst_2505_; lean_object* v_fst_2506_; lean_object* v_snd_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___x_2531_; uint8_t v___y_2533_; lean_object* v___x_2726_; uint8_t v___x_2727_; 
v___x_2531_ = lean_box(0);
v___x_2726_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__25));
v___x_2727_ = l_Lean_Expr_isAppOf(v_e_2073_, v___x_2726_);
if (v___x_2727_ == 0)
{
lean_object* v___x_2728_; uint8_t v___x_2729_; 
v___x_2728_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__27));
v___x_2729_ = l_Lean_Expr_isAppOf(v_e_2073_, v___x_2728_);
v___y_2533_ = v___x_2729_;
goto v___jp_2532_;
}
else
{
v___y_2533_ = v___x_2727_;
goto v___jp_2532_;
}
v___jp_2079_:
{
if (lean_obj_tag(v___y_2080_) == 0)
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2089_; 
v_a_2081_ = lean_ctor_get(v___y_2080_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___y_2080_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2083_ = v___y_2080_;
v_isShared_2084_ = v_isSharedCheck_2089_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___y_2080_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2089_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v_a_2085_; lean_object* v___x_2087_; 
v_a_2085_ = lean_ctor_get(v_a_2081_, 0);
lean_inc(v_a_2085_);
lean_dec(v_a_2081_);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 0, v_a_2085_);
v___x_2087_ = v___x_2083_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2085_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
v_a_2090_ = lean_ctor_get(v___y_2080_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___y_2080_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___y_2080_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___y_2080_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
v___jp_2098_:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = lean_box(0);
lean_inc(v_a_2077_);
lean_inc_ref(v_a_2076_);
lean_inc(v_a_2075_);
lean_inc_ref(v_a_2074_);
v___x_2101_ = lean_apply_6(v___y_2099_, v___x_2100_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, lean_box(0));
v___y_2080_ = v___x_2101_;
goto v___jp_2079_;
}
v___jp_2102_:
{
if (v___y_2108_ == 0)
{
lean_object* v_toCold_2109_; lean_object* v_options_2110_; uint8_t v_hasTrace_2111_; 
v_toCold_2109_ = lean_ctor_get(v_a_2076_, 0);
v_options_2110_ = lean_ctor_get(v_toCold_2109_, 2);
v_hasTrace_2111_ = lean_ctor_get_uint8(v_options_2110_, sizeof(void*)*1);
if (v_hasTrace_2111_ == 0)
{
lean_dec(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
v___y_2099_ = v___y_2107_;
goto v___jp_2098_;
}
else
{
lean_object* v_inheritedTraceOptions_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; uint8_t v___x_2115_; 
v_inheritedTraceOptions_2112_ = lean_ctor_get(v_toCold_2109_, 11);
v___x_2113_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2105_);
v___x_2114_ = l_Lean_Name_append(v___x_2113_, v___y_2105_);
v___x_2115_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2112_, v_options_2110_, v___x_2114_);
lean_dec(v___x_2114_);
if (v___x_2115_ == 0)
{
lean_dec(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
v___y_2099_ = v___y_2107_;
goto v___jp_2098_;
}
else
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2116_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__3, &l_Lean_Meta_rwMatcher___closed__3_once, _init_l_Lean_Meta_rwMatcher___closed__3);
v___x_2117_ = l_Lean_MessageData_ofConstName(v___y_2106_, v___y_2103_);
v___x_2118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2116_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
v___x_2119_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__5, &l_Lean_Meta_rwMatcher___closed__5_once, _init_l_Lean_Meta_rwMatcher___closed__5);
v___x_2120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2118_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
v___x_2121_ = l_Lean_Exception_toMessageData(v___y_2104_);
v___x_2122_ = l_Lean_indentD(v___x_2121_);
v___x_2123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2120_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
v___x_2124_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2105_, v___x_2123_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2126_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2125_);
lean_dec_ref_known(v___x_2124_, 1);
lean_inc(v_a_2077_);
lean_inc_ref(v_a_2076_);
lean_inc(v_a_2075_);
lean_inc_ref(v_a_2074_);
v___x_2126_ = lean_apply_6(v___y_2107_, v_a_2125_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, lean_box(0));
v___y_2080_ = v___x_2126_;
goto v___jp_2079_;
}
else
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_dec_ref(v___y_2107_);
v_a_2127_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2124_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2124_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
}
}
else
{
lean_object* v___x_2135_; 
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec(v___y_2105_);
v___x_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2135_, 0, v___y_2104_);
return v___x_2135_;
}
}
v___jp_2136_:
{
uint8_t v___x_2142_; 
v___x_2142_ = l_Lean_Exception_isInterrupt(v_a_2141_);
if (v___x_2142_ == 0)
{
uint8_t v___x_2143_; 
lean_inc_ref(v_a_2141_);
v___x_2143_ = l_Lean_Exception_isRuntime(v_a_2141_);
v___y_2103_ = v___y_2137_;
v___y_2104_ = v_a_2141_;
v___y_2105_ = v___y_2138_;
v___y_2106_ = v___y_2139_;
v___y_2107_ = v___y_2140_;
v___y_2108_ = v___x_2143_;
goto v___jp_2102_;
}
else
{
v___y_2103_ = v___y_2137_;
v___y_2104_ = v_a_2141_;
v___y_2105_ = v___y_2138_;
v___y_2106_ = v___y_2139_;
v___y_2107_ = v___y_2140_;
v___y_2108_ = v___x_2142_;
goto v___jp_2102_;
}
}
v___jp_2144_:
{
if (lean_obj_tag(v___y_2149_) == 0)
{
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec(v___y_2146_);
return v___y_2149_;
}
else
{
lean_object* v_a_2150_; 
v_a_2150_ = lean_ctor_get(v___y_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___y_2149_, 1);
v___y_2137_ = v___y_2145_;
v___y_2138_ = v___y_2146_;
v___y_2139_ = v___y_2147_;
v___y_2140_ = v___y_2148_;
v_a_2141_ = v_a_2150_;
goto v___jp_2136_;
}
}
v___jp_2151_:
{
lean_object* v___x_2164_; double v___x_2165_; double v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2164_ = lean_io_get_num_heartbeats();
v___x_2165_ = lean_float_of_nat(v___y_2162_);
v___x_2166_ = lean_float_of_nat(v___x_2164_);
v___x_2167_ = lean_box_float(v___x_2165_);
v___x_2168_ = lean_box_float(v___x_2166_);
v___x_2169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2167_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
v___x_2170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2170_, 0, v_a_2163_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
lean_inc_ref(v___y_2157_);
lean_inc(v___y_2153_);
v___x_2171_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v___y_2153_, v___y_2156_, v___y_2157_, v___y_2159_, v___y_2154_, v___y_2161_, v___y_2160_, v___x_2170_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
v___y_2145_ = v___y_2152_;
v___y_2146_ = v___y_2153_;
v___y_2147_ = v___y_2155_;
v___y_2148_ = v___y_2158_;
v___y_2149_ = v___x_2171_;
goto v___jp_2144_;
}
v___jp_2172_:
{
lean_object* v___x_2185_; 
v___x_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2185_, 0, v_a_2184_);
v___y_2152_ = v___y_2173_;
v___y_2153_ = v___y_2174_;
v___y_2154_ = v___y_2175_;
v___y_2155_ = v___y_2176_;
v___y_2156_ = v___y_2177_;
v___y_2157_ = v___y_2178_;
v___y_2158_ = v___y_2179_;
v___y_2159_ = v___y_2180_;
v___y_2160_ = v___y_2181_;
v___y_2161_ = v___y_2182_;
v___y_2162_ = v___y_2183_;
v_a_2163_ = v___x_2185_;
goto v___jp_2151_;
}
v___jp_2186_:
{
if (lean_obj_tag(v___y_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
v_a_2199_ = lean_ctor_get(v___y_2198_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___y_2198_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___y_2198_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___y_2198_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
lean_ctor_set_tag(v___x_2201_, 1);
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
v___y_2152_ = v___y_2187_;
v___y_2153_ = v___y_2188_;
v___y_2154_ = v___y_2189_;
v___y_2155_ = v___y_2190_;
v___y_2156_ = v___y_2191_;
v___y_2157_ = v___y_2192_;
v___y_2158_ = v___y_2193_;
v___y_2159_ = v___y_2194_;
v___y_2160_ = v___y_2195_;
v___y_2161_ = v___y_2196_;
v___y_2162_ = v___y_2197_;
v_a_2163_ = v___x_2204_;
goto v___jp_2151_;
}
}
}
else
{
lean_object* v_a_2207_; 
v_a_2207_ = lean_ctor_get(v___y_2198_, 0);
lean_inc(v_a_2207_);
lean_dec_ref_known(v___y_2198_, 1);
v___y_2173_ = v___y_2187_;
v___y_2174_ = v___y_2188_;
v___y_2175_ = v___y_2189_;
v___y_2176_ = v___y_2190_;
v___y_2177_ = v___y_2191_;
v___y_2178_ = v___y_2192_;
v___y_2179_ = v___y_2193_;
v___y_2180_ = v___y_2194_;
v___y_2181_ = v___y_2195_;
v___y_2182_ = v___y_2196_;
v___y_2183_ = v___y_2197_;
v_a_2184_ = v_a_2207_;
goto v___jp_2172_;
}
}
v___jp_2208_:
{
lean_object* v___x_2221_; double v___x_2222_; double v___x_2223_; double v___x_2224_; double v___x_2225_; double v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2221_ = lean_io_mono_nanos_now();
v___x_2222_ = lean_float_of_nat(v___y_2209_);
v___x_2223_ = lean_float_once(&l_Lean_Meta_rwMatcher___closed__6, &l_Lean_Meta_rwMatcher___closed__6_once, _init_l_Lean_Meta_rwMatcher___closed__6);
v___x_2224_ = lean_float_div(v___x_2222_, v___x_2223_);
v___x_2225_ = lean_float_of_nat(v___x_2221_);
v___x_2226_ = lean_float_div(v___x_2225_, v___x_2223_);
v___x_2227_ = lean_box_float(v___x_2224_);
v___x_2228_ = lean_box_float(v___x_2226_);
v___x_2229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2227_);
lean_ctor_set(v___x_2229_, 1, v___x_2228_);
v___x_2230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2230_, 0, v_a_2220_);
lean_ctor_set(v___x_2230_, 1, v___x_2229_);
lean_inc_ref(v___y_2215_);
lean_inc(v___y_2211_);
v___x_2231_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v___y_2211_, v___y_2214_, v___y_2215_, v___y_2217_, v___y_2212_, v___y_2219_, v___y_2218_, v___x_2230_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
v___y_2145_ = v___y_2210_;
v___y_2146_ = v___y_2211_;
v___y_2147_ = v___y_2213_;
v___y_2148_ = v___y_2216_;
v___y_2149_ = v___x_2231_;
goto v___jp_2144_;
}
v___jp_2232_:
{
lean_object* v___x_2245_; 
v___x_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2245_, 0, v_a_2244_);
v___y_2209_ = v___y_2233_;
v___y_2210_ = v___y_2234_;
v___y_2211_ = v___y_2235_;
v___y_2212_ = v___y_2236_;
v___y_2213_ = v___y_2237_;
v___y_2214_ = v___y_2238_;
v___y_2215_ = v___y_2239_;
v___y_2216_ = v___y_2240_;
v___y_2217_ = v___y_2241_;
v___y_2218_ = v___y_2242_;
v___y_2219_ = v___y_2243_;
v_a_2220_ = v___x_2245_;
goto v___jp_2208_;
}
v___jp_2246_:
{
if (lean_obj_tag(v___y_2258_) == 0)
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
v_a_2259_ = lean_ctor_get(v___y_2258_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___y_2258_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___y_2258_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___y_2258_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
lean_ctor_set_tag(v___x_2261_, 1);
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
v___y_2209_ = v___y_2247_;
v___y_2210_ = v___y_2248_;
v___y_2211_ = v___y_2249_;
v___y_2212_ = v___y_2250_;
v___y_2213_ = v___y_2251_;
v___y_2214_ = v___y_2252_;
v___y_2215_ = v___y_2253_;
v___y_2216_ = v___y_2254_;
v___y_2217_ = v___y_2255_;
v___y_2218_ = v___y_2256_;
v___y_2219_ = v___y_2257_;
v_a_2220_ = v___x_2264_;
goto v___jp_2208_;
}
}
}
else
{
lean_object* v_a_2267_; 
v_a_2267_ = lean_ctor_get(v___y_2258_, 0);
lean_inc(v_a_2267_);
lean_dec_ref_known(v___y_2258_, 1);
v___y_2233_ = v___y_2247_;
v___y_2234_ = v___y_2248_;
v___y_2235_ = v___y_2249_;
v___y_2236_ = v___y_2250_;
v___y_2237_ = v___y_2251_;
v___y_2238_ = v___y_2252_;
v___y_2239_ = v___y_2253_;
v___y_2240_ = v___y_2254_;
v___y_2241_ = v___y_2255_;
v___y_2242_ = v___y_2256_;
v___y_2243_ = v___y_2257_;
v_a_2244_ = v_a_2267_;
goto v___jp_2232_;
}
}
v___jp_2268_:
{
lean_object* v___x_2284_; lean_object* v_a_2285_; lean_object* v___x_2286_; uint8_t v___x_2287_; 
v___x_2284_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg(v_a_2077_);
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2285_);
lean_dec_ref(v___x_2284_);
v___x_2286_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2287_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v___y_2283_, v___x_2286_);
if (v___x_2287_ == 0)
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = lean_io_mono_nanos_now();
lean_inc(v_a_2077_);
lean_inc_ref(v_a_2076_);
lean_inc(v_a_2075_);
lean_inc_ref(v_a_2074_);
v___x_2289_ = lean_infer_type(v___y_2276_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; uint8_t v___x_2291_; lean_object* v___x_2292_; 
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2290_);
lean_dec_ref_known(v___x_2289_, 1);
v___x_2291_ = 0;
v___x_2292_ = l_Lean_Meta_forallMetaTelescope(v_a_2290_, v___x_2291_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v_snd_2294_; lean_object* v_fst_2295_; lean_object* v_snd_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2314_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2293_);
lean_dec_ref_known(v___x_2292_, 1);
v_snd_2294_ = lean_ctor_get(v_a_2293_, 1);
lean_inc(v_snd_2294_);
v_fst_2295_ = lean_ctor_get(v_a_2293_, 0);
lean_inc(v_fst_2295_);
lean_dec(v_a_2293_);
v_snd_2296_ = lean_ctor_get(v_snd_2294_, 1);
v_isSharedCheck_2314_ = !lean_is_exclusive(v_snd_2294_);
if (v_isSharedCheck_2314_ == 0)
{
lean_object* v_unused_2315_; 
v_unused_2315_ = lean_ctor_get(v_snd_2294_, 0);
lean_dec(v_unused_2315_);
v___x_2298_ = v_snd_2294_;
v_isShared_2299_ = v_isSharedCheck_2314_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_snd_2296_);
lean_dec(v_snd_2294_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2314_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; uint8_t v___x_2302_; 
v___x_2300_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2275_);
v___x_2301_ = l_Lean_Name_append(v___x_2300_, v___y_2275_);
v___x_2302_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2278_, v___y_2283_, v___x_2301_);
lean_dec(v___x_2301_);
if (v___x_2302_ == 0)
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
lean_del_object(v___x_2298_);
v___x_2303_ = lean_box(0);
v___x_2304_ = l_Lean_Meta_rwMatcher___lam__2(v___y_2272_, v___y_2270_, v_fst_2295_, v___y_2271_, v_e_2073_, v___y_2269_, v_snd_2296_, v___x_2303_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
lean_dec(v_snd_2296_);
v___y_2247_ = v___x_2288_;
v___y_2248_ = v___y_2274_;
v___y_2249_ = v___y_2275_;
v___y_2250_ = v___y_2277_;
v___y_2251_ = v___y_2279_;
v___y_2252_ = v___y_2280_;
v___y_2253_ = v___y_2281_;
v___y_2254_ = v___y_2282_;
v___y_2255_ = v___y_2283_;
v___y_2256_ = v___y_2273_;
v___y_2257_ = v_a_2285_;
v___y_2258_ = v___x_2304_;
goto v___jp_2246_;
}
else
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2308_; 
v___x_2305_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2296_);
v___x_2306_ = l_Lean_indentExpr(v_snd_2296_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set_tag(v___x_2298_, 7);
lean_ctor_set(v___x_2298_, 1, v___x_2306_);
lean_ctor_set(v___x_2298_, 0, v___x_2305_);
v___x_2308_ = v___x_2298_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2305_);
lean_ctor_set(v_reuseFailAlloc_2313_, 1, v___x_2306_);
v___x_2308_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
lean_object* v___x_2309_; 
lean_inc(v___y_2275_);
v___x_2309_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2275_, v___x_2308_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v___x_2311_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2310_);
lean_dec_ref_known(v___x_2309_, 1);
v___x_2311_ = l_Lean_Meta_rwMatcher___lam__2(v___y_2272_, v___y_2270_, v_fst_2295_, v___y_2271_, v_e_2073_, v___y_2269_, v_snd_2296_, v_a_2310_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
lean_dec(v_snd_2296_);
v___y_2247_ = v___x_2288_;
v___y_2248_ = v___y_2274_;
v___y_2249_ = v___y_2275_;
v___y_2250_ = v___y_2277_;
v___y_2251_ = v___y_2279_;
v___y_2252_ = v___y_2280_;
v___y_2253_ = v___y_2281_;
v___y_2254_ = v___y_2282_;
v___y_2255_ = v___y_2283_;
v___y_2256_ = v___y_2273_;
v___y_2257_ = v_a_2285_;
v___y_2258_ = v___x_2311_;
goto v___jp_2246_;
}
else
{
lean_object* v_a_2312_; 
lean_dec(v_snd_2296_);
lean_dec(v_fst_2295_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec_ref(v_e_2073_);
v_a_2312_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2312_);
lean_dec_ref_known(v___x_2309_, 1);
v___y_2233_ = v___x_2288_;
v___y_2234_ = v___y_2274_;
v___y_2235_ = v___y_2275_;
v___y_2236_ = v___y_2277_;
v___y_2237_ = v___y_2279_;
v___y_2238_ = v___y_2280_;
v___y_2239_ = v___y_2281_;
v___y_2240_ = v___y_2282_;
v___y_2241_ = v___y_2283_;
v___y_2242_ = v___y_2273_;
v___y_2243_ = v_a_2285_;
v_a_2244_ = v_a_2312_;
goto v___jp_2232_;
}
}
}
}
}
else
{
lean_object* v_a_2316_; 
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec_ref(v_e_2073_);
v_a_2316_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2292_, 1);
v___y_2233_ = v___x_2288_;
v___y_2234_ = v___y_2274_;
v___y_2235_ = v___y_2275_;
v___y_2236_ = v___y_2277_;
v___y_2237_ = v___y_2279_;
v___y_2238_ = v___y_2280_;
v___y_2239_ = v___y_2281_;
v___y_2240_ = v___y_2282_;
v___y_2241_ = v___y_2283_;
v___y_2242_ = v___y_2273_;
v___y_2243_ = v_a_2285_;
v_a_2244_ = v_a_2316_;
goto v___jp_2232_;
}
}
else
{
lean_object* v_a_2317_; 
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec_ref(v_e_2073_);
v_a_2317_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2317_);
lean_dec_ref_known(v___x_2289_, 1);
v___y_2233_ = v___x_2288_;
v___y_2234_ = v___y_2274_;
v___y_2235_ = v___y_2275_;
v___y_2236_ = v___y_2277_;
v___y_2237_ = v___y_2279_;
v___y_2238_ = v___y_2280_;
v___y_2239_ = v___y_2281_;
v___y_2240_ = v___y_2282_;
v___y_2241_ = v___y_2283_;
v___y_2242_ = v___y_2273_;
v___y_2243_ = v_a_2285_;
v_a_2244_ = v_a_2317_;
goto v___jp_2232_;
}
}
else
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2077_);
lean_inc_ref(v_a_2076_);
lean_inc(v_a_2075_);
lean_inc_ref(v_a_2074_);
v___x_2319_ = lean_infer_type(v___y_2276_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; uint8_t v___x_2321_; lean_object* v___x_2322_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2320_);
lean_dec_ref_known(v___x_2319_, 1);
v___x_2321_ = 0;
v___x_2322_ = l_Lean_Meta_forallMetaTelescope(v_a_2320_, v___x_2321_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; lean_object* v_snd_2324_; lean_object* v_fst_2325_; lean_object* v_snd_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2344_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_a_2323_);
lean_dec_ref_known(v___x_2322_, 1);
v_snd_2324_ = lean_ctor_get(v_a_2323_, 1);
lean_inc(v_snd_2324_);
v_fst_2325_ = lean_ctor_get(v_a_2323_, 0);
lean_inc(v_fst_2325_);
lean_dec(v_a_2323_);
v_snd_2326_ = lean_ctor_get(v_snd_2324_, 1);
v_isSharedCheck_2344_ = !lean_is_exclusive(v_snd_2324_);
if (v_isSharedCheck_2344_ == 0)
{
lean_object* v_unused_2345_; 
v_unused_2345_ = lean_ctor_get(v_snd_2324_, 0);
lean_dec(v_unused_2345_);
v___x_2328_ = v_snd_2324_;
v_isShared_2329_ = v_isSharedCheck_2344_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_snd_2326_);
lean_dec(v_snd_2324_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2344_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; uint8_t v___x_2332_; 
v___x_2330_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2275_);
v___x_2331_ = l_Lean_Name_append(v___x_2330_, v___y_2275_);
v___x_2332_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2278_, v___y_2283_, v___x_2331_);
lean_dec(v___x_2331_);
if (v___x_2332_ == 0)
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
lean_del_object(v___x_2328_);
v___x_2333_ = lean_box(0);
v___x_2334_ = l_Lean_Meta_rwMatcher___lam__3(v___y_2272_, v___y_2270_, v_fst_2325_, v___y_2271_, v_e_2073_, v___y_2269_, v_snd_2326_, v___x_2333_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
lean_dec(v_snd_2326_);
v___y_2187_ = v___y_2274_;
v___y_2188_ = v___y_2275_;
v___y_2189_ = v___y_2277_;
v___y_2190_ = v___y_2279_;
v___y_2191_ = v___y_2280_;
v___y_2192_ = v___y_2281_;
v___y_2193_ = v___y_2282_;
v___y_2194_ = v___y_2283_;
v___y_2195_ = v___y_2273_;
v___y_2196_ = v_a_2285_;
v___y_2197_ = v___x_2318_;
v___y_2198_ = v___x_2334_;
goto v___jp_2186_;
}
else
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2338_; 
v___x_2335_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2326_);
v___x_2336_ = l_Lean_indentExpr(v_snd_2326_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set_tag(v___x_2328_, 7);
lean_ctor_set(v___x_2328_, 1, v___x_2336_);
lean_ctor_set(v___x_2328_, 0, v___x_2335_);
v___x_2338_ = v___x_2328_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2335_);
lean_ctor_set(v_reuseFailAlloc_2343_, 1, v___x_2336_);
v___x_2338_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
lean_object* v___x_2339_; 
lean_inc(v___y_2275_);
v___x_2339_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2275_, v___x_2338_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2341_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref_known(v___x_2339_, 1);
v___x_2341_ = l_Lean_Meta_rwMatcher___lam__3(v___y_2272_, v___y_2270_, v_fst_2325_, v___y_2271_, v_e_2073_, v___y_2269_, v_snd_2326_, v_a_2340_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
lean_dec(v_snd_2326_);
v___y_2187_ = v___y_2274_;
v___y_2188_ = v___y_2275_;
v___y_2189_ = v___y_2277_;
v___y_2190_ = v___y_2279_;
v___y_2191_ = v___y_2280_;
v___y_2192_ = v___y_2281_;
v___y_2193_ = v___y_2282_;
v___y_2194_ = v___y_2283_;
v___y_2195_ = v___y_2273_;
v___y_2196_ = v_a_2285_;
v___y_2197_ = v___x_2318_;
v___y_2198_ = v___x_2341_;
goto v___jp_2186_;
}
else
{
lean_object* v_a_2342_; 
lean_dec(v_snd_2326_);
lean_dec(v_fst_2325_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec_ref(v_e_2073_);
v_a_2342_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2342_);
lean_dec_ref_known(v___x_2339_, 1);
v___y_2173_ = v___y_2274_;
v___y_2174_ = v___y_2275_;
v___y_2175_ = v___y_2277_;
v___y_2176_ = v___y_2279_;
v___y_2177_ = v___y_2280_;
v___y_2178_ = v___y_2281_;
v___y_2179_ = v___y_2282_;
v___y_2180_ = v___y_2283_;
v___y_2181_ = v___y_2273_;
v___y_2182_ = v_a_2285_;
v___y_2183_ = v___x_2318_;
v_a_2184_ = v_a_2342_;
goto v___jp_2172_;
}
}
}
}
}
else
{
lean_object* v_a_2346_; 
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec_ref(v_e_2073_);
v_a_2346_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_a_2346_);
lean_dec_ref_known(v___x_2322_, 1);
v___y_2173_ = v___y_2274_;
v___y_2174_ = v___y_2275_;
v___y_2175_ = v___y_2277_;
v___y_2176_ = v___y_2279_;
v___y_2177_ = v___y_2280_;
v___y_2178_ = v___y_2281_;
v___y_2179_ = v___y_2282_;
v___y_2180_ = v___y_2283_;
v___y_2181_ = v___y_2273_;
v___y_2182_ = v_a_2285_;
v___y_2183_ = v___x_2318_;
v_a_2184_ = v_a_2346_;
goto v___jp_2172_;
}
}
else
{
lean_object* v_a_2347_; 
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec_ref(v_e_2073_);
v_a_2347_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2347_);
lean_dec_ref_known(v___x_2319_, 1);
v___y_2173_ = v___y_2274_;
v___y_2174_ = v___y_2275_;
v___y_2175_ = v___y_2277_;
v___y_2176_ = v___y_2279_;
v___y_2177_ = v___y_2280_;
v___y_2178_ = v___y_2281_;
v___y_2179_ = v___y_2282_;
v___y_2180_ = v___y_2283_;
v___y_2181_ = v___y_2273_;
v___y_2182_ = v_a_2285_;
v___y_2183_ = v___x_2318_;
v_a_2184_ = v_a_2347_;
goto v___jp_2172_;
}
}
}
v___jp_2348_:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2350_ = lean_box(0);
v___x_2351_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2351_, 0, v_e_2073_);
lean_ctor_set(v___x_2351_, 1, v___x_2350_);
lean_ctor_set_uint8(v___x_2351_, sizeof(void*)*2, v___y_2349_);
v___x_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
return v___x_2352_;
}
v___jp_2353_:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2355_ = lean_box(0);
v___x_2356_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2356_, 0, v_e_2073_);
lean_ctor_set(v___x_2356_, 1, v___x_2355_);
lean_ctor_set_uint8(v___x_2356_, sizeof(void*)*2, v___y_2354_);
v___x_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
return v___x_2357_;
}
v___jp_2358_:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2362_, 0, v_proof_2361_);
v___x_2363_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2363_, 0, v___y_2360_);
lean_ctor_set(v___x_2363_, 1, v___x_2362_);
lean_ctor_set_uint8(v___x_2363_, sizeof(void*)*2, v___y_2359_);
v___x_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2363_);
return v___x_2364_;
}
v___jp_2365_:
{
if (lean_obj_tag(v___y_2372_) == 0)
{
lean_object* v_a_2373_; 
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2368_);
lean_dec(v___y_2367_);
v_a_2373_ = lean_ctor_get(v___y_2372_, 0);
lean_inc(v_a_2373_);
lean_dec_ref_known(v___y_2372_, 1);
v___y_2359_ = v___y_2369_;
v___y_2360_ = v___y_2371_;
v_proof_2361_ = v_a_2373_;
goto v___jp_2358_;
}
else
{
lean_object* v_a_2374_; 
lean_dec_ref(v___y_2371_);
v_a_2374_ = lean_ctor_get(v___y_2372_, 0);
lean_inc(v_a_2374_);
lean_dec_ref_known(v___y_2372_, 1);
v___y_2137_ = v___y_2366_;
v___y_2138_ = v___y_2367_;
v___y_2139_ = v___y_2368_;
v___y_2140_ = v___y_2370_;
v_a_2141_ = v_a_2374_;
goto v___jp_2136_;
}
}
v___jp_2375_:
{
if (v___y_2389_ == 0)
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
lean_dec_ref(v___y_2376_);
v___x_2390_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_2391_ = l_Lean_MessageData_ofExpr(v___y_2380_);
v___x_2392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2390_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
v___x_2393_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_2394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2392_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
v___x_2395_ = l_Lean_Exception_toMessageData(v___y_2382_);
v___x_2396_ = l_Lean_indentD(v___x_2395_);
v___x_2397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2394_);
lean_ctor_set(v___x_2397_, 1, v___x_2396_);
v___x_2398_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_2399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2397_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
v___x_2400_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2399_, v___y_2383_, v___y_2379_, v___y_2381_, v___y_2378_);
v___y_2366_ = v___y_2377_;
v___y_2367_ = v___y_2384_;
v___y_2368_ = v___y_2385_;
v___y_2369_ = v___y_2386_;
v___y_2370_ = v___y_2387_;
v___y_2371_ = v___y_2388_;
v___y_2372_ = v___x_2400_;
goto v___jp_2365_;
}
else
{
lean_dec_ref(v___y_2382_);
lean_dec_ref(v___y_2380_);
v___y_2366_ = v___y_2377_;
v___y_2367_ = v___y_2384_;
v___y_2368_ = v___y_2385_;
v___y_2369_ = v___y_2386_;
v___y_2370_ = v___y_2387_;
v___y_2371_ = v___y_2388_;
v___y_2372_ = v___y_2376_;
goto v___jp_2365_;
}
}
v___jp_2401_:
{
lean_object* v___x_2414_; lean_object* v_a_2415_; lean_object* v___x_2416_; 
v___x_2414_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_2403_, v___y_2411_);
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_a_2415_);
lean_dec_ref(v___x_2414_);
v___x_2416_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_2404_, v___y_2411_);
if (v___y_2409_ == 0)
{
lean_object* v_a_2417_; 
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2406_);
lean_dec(v___y_2405_);
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
lean_inc(v_a_2417_);
lean_dec_ref(v___x_2416_);
v___y_2359_ = v___y_2407_;
v___y_2360_ = v_a_2415_;
v_proof_2361_ = v_a_2417_;
goto v___jp_2358_;
}
else
{
lean_object* v_a_2418_; lean_object* v___x_2419_; 
v_a_2418_ = lean_ctor_get(v___x_2416_, 0);
lean_inc_n(v_a_2418_, 2);
lean_dec_ref(v___x_2416_);
v___x_2419_ = l_Lean_Meta_mkEqOfHEq(v_a_2418_, v___y_2407_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_dec(v_a_2418_);
v___y_2366_ = v___y_2402_;
v___y_2367_ = v___y_2405_;
v___y_2368_ = v___y_2406_;
v___y_2369_ = v___y_2407_;
v___y_2370_ = v___y_2408_;
v___y_2371_ = v_a_2415_;
v___y_2372_ = v___x_2419_;
goto v___jp_2365_;
}
else
{
lean_object* v_a_2420_; uint8_t v___x_2421_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
lean_inc(v_a_2420_);
v___x_2421_ = l_Lean_Exception_isInterrupt(v_a_2420_);
if (v___x_2421_ == 0)
{
uint8_t v___x_2422_; 
lean_inc(v_a_2420_);
v___x_2422_ = l_Lean_Exception_isRuntime(v_a_2420_);
v___y_2376_ = v___x_2419_;
v___y_2377_ = v___y_2402_;
v___y_2378_ = v___y_2413_;
v___y_2379_ = v___y_2411_;
v___y_2380_ = v_a_2418_;
v___y_2381_ = v___y_2412_;
v___y_2382_ = v_a_2420_;
v___y_2383_ = v___y_2410_;
v___y_2384_ = v___y_2405_;
v___y_2385_ = v___y_2406_;
v___y_2386_ = v___y_2407_;
v___y_2387_ = v___y_2408_;
v___y_2388_ = v_a_2415_;
v___y_2389_ = v___x_2422_;
goto v___jp_2375_;
}
else
{
v___y_2376_ = v___x_2419_;
v___y_2377_ = v___y_2402_;
v___y_2378_ = v___y_2413_;
v___y_2379_ = v___y_2411_;
v___y_2380_ = v_a_2418_;
v___y_2381_ = v___y_2412_;
v___y_2382_ = v_a_2420_;
v___y_2383_ = v___y_2410_;
v___y_2384_ = v___y_2405_;
v___y_2385_ = v___y_2406_;
v___y_2386_ = v___y_2407_;
v___y_2387_ = v___y_2408_;
v___y_2388_ = v_a_2415_;
v___y_2389_ = v___x_2421_;
goto v___jp_2375_;
}
}
}
}
v___jp_2423_:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; uint8_t v___x_2439_; 
v___x_2437_ = lean_array_get_size(v_a_2436_);
v___x_2438_ = lean_unsigned_to_nat(0u);
v___x_2439_ = lean_nat_dec_eq(v___x_2437_, v___x_2438_);
if (v___x_2439_ == 0)
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v_a_2451_; 
lean_dec_ref(v___y_2427_);
lean_dec_ref(v___y_2425_);
v___x_2440_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
lean_inc(v___y_2429_);
v___x_2441_ = l_Lean_MessageData_ofConstName(v___y_2429_, v___x_2439_);
v___x_2442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2440_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
v___x_2443_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_2444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2442_);
lean_ctor_set(v___x_2444_, 1, v___x_2443_);
v___x_2445_ = lean_array_to_list(v_a_2436_);
v___x_2446_ = lean_box(0);
v___x_2447_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_2445_, v___x_2446_);
v___x_2448_ = l_Lean_MessageData_ofList(v___x_2447_);
v___x_2449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2444_);
lean_ctor_set(v___x_2449_, 1, v___x_2448_);
v___x_2450_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2449_, v___y_2428_, v___y_2435_, v___y_2434_, v___y_2432_);
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_a_2451_);
lean_dec_ref(v___x_2450_);
v___y_2137_ = v___y_2424_;
v___y_2138_ = v___y_2426_;
v___y_2139_ = v___y_2429_;
v___y_2140_ = v___y_2431_;
v_a_2141_ = v_a_2451_;
goto v___jp_2136_;
}
else
{
lean_dec_ref(v_a_2436_);
v___y_2402_ = v___y_2424_;
v___y_2403_ = v___y_2425_;
v___y_2404_ = v___y_2427_;
v___y_2405_ = v___y_2426_;
v___y_2406_ = v___y_2429_;
v___y_2407_ = v___y_2430_;
v___y_2408_ = v___y_2431_;
v___y_2409_ = v___y_2433_;
v___y_2410_ = v___y_2428_;
v___y_2411_ = v___y_2435_;
v___y_2412_ = v___y_2434_;
v___y_2413_ = v___y_2432_;
goto v___jp_2401_;
}
}
v___jp_2452_:
{
if (lean_obj_tag(v___y_2465_) == 0)
{
lean_object* v_a_2466_; 
v_a_2466_ = lean_ctor_get(v___y_2465_, 0);
lean_inc(v_a_2466_);
lean_dec_ref_known(v___y_2465_, 1);
v___y_2424_ = v___y_2453_;
v___y_2425_ = v___y_2454_;
v___y_2426_ = v___y_2456_;
v___y_2427_ = v___y_2455_;
v___y_2428_ = v___y_2458_;
v___y_2429_ = v___y_2457_;
v___y_2430_ = v___y_2459_;
v___y_2431_ = v___y_2461_;
v___y_2432_ = v___y_2460_;
v___y_2433_ = v___y_2462_;
v___y_2434_ = v___y_2464_;
v___y_2435_ = v___y_2463_;
v_a_2436_ = v_a_2466_;
goto v___jp_2423_;
}
else
{
lean_object* v_a_2467_; 
lean_dec_ref(v___y_2455_);
lean_dec_ref(v___y_2454_);
v_a_2467_ = lean_ctor_get(v___y_2465_, 0);
lean_inc(v_a_2467_);
lean_dec_ref_known(v___y_2465_, 1);
v___y_2137_ = v___y_2453_;
v___y_2138_ = v___y_2456_;
v___y_2139_ = v___y_2457_;
v___y_2140_ = v___y_2461_;
v_a_2141_ = v_a_2467_;
goto v___jp_2136_;
}
}
v___jp_2468_:
{
lean_object* v___x_2483_; size_t v_sz_2484_; lean_object* v___x_2485_; 
v___x_2483_ = lean_box(0);
v_sz_2484_ = lean_array_size(v___y_2469_);
v___x_2485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___y_2469_, v_sz_2484_, v___y_2476_, v___x_2483_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; uint8_t v___x_2489_; 
lean_dec_ref_known(v___x_2485_, 1);
v___x_2486_ = lean_unsigned_to_nat(0u);
v___x_2487_ = lean_array_get_size(v___y_2469_);
v___x_2488_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_2489_ = lean_nat_dec_lt(v___x_2486_, v___x_2487_);
if (v___x_2489_ == 0)
{
lean_dec_ref(v___y_2469_);
v___y_2424_ = v___y_2470_;
v___y_2425_ = v___y_2471_;
v___y_2426_ = v___y_2473_;
v___y_2427_ = v___y_2472_;
v___y_2428_ = v___y_2479_;
v___y_2429_ = v___y_2474_;
v___y_2430_ = v___y_2475_;
v___y_2431_ = v___y_2477_;
v___y_2432_ = v___y_2482_;
v___y_2433_ = v___y_2478_;
v___y_2434_ = v___y_2481_;
v___y_2435_ = v___y_2480_;
v_a_2436_ = v___x_2488_;
goto v___jp_2423_;
}
else
{
uint8_t v___x_2490_; 
v___x_2490_ = lean_nat_dec_le(v___x_2487_, v___x_2487_);
if (v___x_2490_ == 0)
{
if (v___x_2489_ == 0)
{
lean_dec_ref(v___y_2469_);
v___y_2424_ = v___y_2470_;
v___y_2425_ = v___y_2471_;
v___y_2426_ = v___y_2473_;
v___y_2427_ = v___y_2472_;
v___y_2428_ = v___y_2479_;
v___y_2429_ = v___y_2474_;
v___y_2430_ = v___y_2475_;
v___y_2431_ = v___y_2477_;
v___y_2432_ = v___y_2482_;
v___y_2433_ = v___y_2478_;
v___y_2434_ = v___y_2481_;
v___y_2435_ = v___y_2480_;
v_a_2436_ = v___x_2488_;
goto v___jp_2423_;
}
else
{
size_t v___x_2491_; lean_object* v___x_2492_; 
v___x_2491_ = lean_usize_of_nat(v___x_2487_);
v___x_2492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___y_2469_, v___y_2476_, v___x_2491_, v___x_2488_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
lean_dec_ref(v___y_2469_);
v___y_2453_ = v___y_2470_;
v___y_2454_ = v___y_2471_;
v___y_2455_ = v___y_2472_;
v___y_2456_ = v___y_2473_;
v___y_2457_ = v___y_2474_;
v___y_2458_ = v___y_2479_;
v___y_2459_ = v___y_2475_;
v___y_2460_ = v___y_2482_;
v___y_2461_ = v___y_2477_;
v___y_2462_ = v___y_2478_;
v___y_2463_ = v___y_2480_;
v___y_2464_ = v___y_2481_;
v___y_2465_ = v___x_2492_;
goto v___jp_2452_;
}
}
else
{
size_t v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = lean_usize_of_nat(v___x_2487_);
v___x_2494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___y_2469_, v___y_2476_, v___x_2493_, v___x_2488_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
lean_dec_ref(v___y_2469_);
v___y_2453_ = v___y_2470_;
v___y_2454_ = v___y_2471_;
v___y_2455_ = v___y_2472_;
v___y_2456_ = v___y_2473_;
v___y_2457_ = v___y_2474_;
v___y_2458_ = v___y_2479_;
v___y_2459_ = v___y_2475_;
v___y_2460_ = v___y_2482_;
v___y_2461_ = v___y_2477_;
v___y_2462_ = v___y_2478_;
v___y_2463_ = v___y_2480_;
v___y_2464_ = v___y_2481_;
v___y_2465_ = v___x_2494_;
goto v___jp_2452_;
}
}
}
else
{
lean_object* v_a_2495_; 
lean_dec_ref(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec_ref(v___y_2469_);
v_a_2495_ = lean_ctor_get(v___x_2485_, 0);
lean_inc(v_a_2495_);
lean_dec_ref_known(v___x_2485_, 1);
v___y_2137_ = v___y_2470_;
v___y_2138_ = v___y_2473_;
v___y_2139_ = v___y_2474_;
v___y_2140_ = v___y_2477_;
v_a_2141_ = v_a_2495_;
goto v___jp_2136_;
}
}
v___jp_2496_:
{
lean_object* v___x_2512_; 
lean_inc_ref(v_fst_2506_);
lean_inc_ref(v_e_2073_);
v___x_2512_ = l_Lean_Meta_isExprDefEq(v_e_2073_, v_fst_2506_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v_a_2513_; uint8_t v___x_2514_; 
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_a_2513_);
lean_dec_ref_known(v___x_2512_, 1);
v___x_2514_ = lean_unbox(v_a_2513_);
lean_dec(v_a_2513_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v_a_2529_; 
lean_dec_ref(v_snd_2507_);
lean_dec_ref(v___y_2500_);
lean_dec_ref(v___y_2497_);
v___x_2515_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_2516_ = l_Lean_MessageData_ofExpr(v_fst_2506_);
v___x_2517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2515_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
v___x_2518_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_2519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2517_);
lean_ctor_set(v___x_2519_, 1, v___x_2518_);
lean_inc(v___y_2501_);
v___x_2520_ = l_Lean_MessageData_ofConstName(v___y_2501_, v___y_2498_);
v___x_2521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2519_);
lean_ctor_set(v___x_2521_, 1, v___x_2520_);
v___x_2522_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_2523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2521_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
v___x_2524_ = l_Lean_MessageData_ofExpr(v_e_2073_);
v___x_2525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2523_);
lean_ctor_set(v___x_2525_, 1, v___x_2524_);
v___x_2526_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_2527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2525_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
v___x_2528_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2527_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2529_);
lean_dec_ref(v___x_2528_);
v___y_2137_ = v___y_2498_;
v___y_2138_ = v___y_2499_;
v___y_2139_ = v___y_2501_;
v___y_2140_ = v___y_2504_;
v_a_2141_ = v_a_2529_;
goto v___jp_2136_;
}
else
{
lean_dec_ref(v_fst_2506_);
lean_dec_ref(v_e_2073_);
v___y_2469_ = v___y_2497_;
v___y_2470_ = v___y_2498_;
v___y_2471_ = v_snd_2507_;
v___y_2472_ = v___y_2500_;
v___y_2473_ = v___y_2499_;
v___y_2474_ = v___y_2501_;
v___y_2475_ = v___y_2502_;
v___y_2476_ = v___y_2503_;
v___y_2477_ = v___y_2504_;
v___y_2478_ = v_fst_2505_;
v___y_2479_ = v___y_2508_;
v___y_2480_ = v___y_2509_;
v___y_2481_ = v___y_2510_;
v___y_2482_ = v___y_2511_;
goto v___jp_2468_;
}
}
else
{
lean_object* v_a_2530_; 
lean_dec_ref(v_snd_2507_);
lean_dec_ref(v_fst_2506_);
lean_dec_ref(v___y_2500_);
lean_dec_ref(v___y_2497_);
lean_dec_ref(v_e_2073_);
v_a_2530_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_a_2530_);
lean_dec_ref_known(v___x_2512_, 1);
v___y_2137_ = v___y_2498_;
v___y_2138_ = v___y_2499_;
v___y_2139_ = v___y_2501_;
v___y_2140_ = v___y_2504_;
v_a_2141_ = v_a_2530_;
goto v___jp_2136_;
}
}
v___jp_2532_:
{
uint8_t v___x_2534_; 
v___x_2534_ = 1;
if (v___y_2533_ == 0)
{
lean_object* v___x_2535_; lean_object* v___f_2536_; lean_object* v___x_2537_; lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2706_; 
v___x_2535_ = lean_box(v___x_2534_);
lean_inc_ref(v_e_2073_);
v___f_2536_ = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2536_, 0, v_e_2073_);
lean_closure_set(v___f_2536_, 1, v___x_2535_);
v___x_2537_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(v_e_2073_, v_a_2077_);
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2540_ = v___x_2537_;
v_isShared_2541_ = v_isSharedCheck_2706_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2537_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2706_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
uint8_t v___x_2542_; 
v___x_2542_ = lean_unbox(v_a_2538_);
lean_dec(v_a_2538_);
if (v___x_2542_ == 0)
{
lean_object* v_toCold_2543_; lean_object* v_options_2544_; uint8_t v_hasTrace_2545_; 
lean_del_object(v___x_2540_);
lean_dec_ref(v___f_2536_);
lean_dec(v_altIdx_2072_);
v_toCold_2543_ = lean_ctor_get(v_a_2076_, 0);
v_options_2544_ = lean_ctor_get(v_toCold_2543_, 2);
v_hasTrace_2545_ = lean_ctor_get_uint8(v_options_2544_, sizeof(void*)*1);
if (v_hasTrace_2545_ == 0)
{
v___y_2354_ = v___x_2534_;
goto v___jp_2353_;
}
else
{
lean_object* v_inheritedTraceOptions_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; uint8_t v___x_2549_; 
v_inheritedTraceOptions_2546_ = lean_ctor_get(v_toCold_2543_, 11);
v___x_2547_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2548_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2549_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2546_, v_options_2544_, v___x_2548_);
if (v___x_2549_ == 0)
{
v___y_2354_ = v___x_2534_;
goto v___jp_2353_;
}
else
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2550_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__15, &l_Lean_Meta_rwMatcher___closed__15_once, _init_l_Lean_Meta_rwMatcher___closed__15);
lean_inc_ref(v_e_2073_);
v___x_2551_ = l_Lean_indentExpr(v_e_2073_);
v___x_2552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2550_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
v___x_2553_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2547_, v___x_2552_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_dec_ref_known(v___x_2553_, 1);
v___y_2354_ = v___x_2534_;
goto v___jp_2353_;
}
else
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
lean_dec_ref(v_e_2073_);
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v___x_2553_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2553_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2554_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
}
}
else
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2562_ = l_Lean_Expr_getAppFn(v_e_2073_);
v___x_2563_ = l_Lean_Expr_constName_x21(v___x_2562_);
lean_inc(v_a_2077_);
lean_inc_ref(v_a_2076_);
lean_inc(v_a_2075_);
lean_inc_ref(v_a_2074_);
lean_inc(v___x_2563_);
v___x_2564_ = lean_get_congr_match_equations_for(v___x_2563_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_a_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; 
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
lean_inc(v_a_2565_);
lean_dec_ref_known(v___x_2564_, 1);
v___x_2566_ = lean_array_get_size(v_a_2565_);
v___x_2567_ = lean_nat_dec_lt(v_altIdx_2072_, v___x_2566_);
if (v___x_2567_ == 0)
{
lean_object* v_toCold_2568_; lean_object* v_options_2569_; uint8_t v_hasTrace_2570_; 
lean_dec(v_a_2565_);
lean_dec_ref(v___x_2562_);
lean_dec_ref(v___f_2536_);
v_toCold_2568_ = lean_ctor_get(v_a_2076_, 0);
v_options_2569_ = lean_ctor_get(v_toCold_2568_, 2);
v_hasTrace_2570_ = lean_ctor_get_uint8(v_options_2569_, sizeof(void*)*1);
if (v_hasTrace_2570_ == 0)
{
lean_dec(v___x_2563_);
lean_del_object(v___x_2540_);
lean_dec(v_altIdx_2072_);
v___y_2349_ = v___x_2534_;
goto v___jp_2348_;
}
else
{
lean_object* v_inheritedTraceOptions_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; uint8_t v___x_2574_; 
v_inheritedTraceOptions_2571_ = lean_ctor_get(v_toCold_2568_, 11);
v___x_2572_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2573_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2574_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2571_, v_options_2569_, v___x_2573_);
if (v___x_2574_ == 0)
{
lean_dec(v___x_2563_);
lean_del_object(v___x_2540_);
lean_dec(v_altIdx_2072_);
v___y_2349_ = v___x_2534_;
goto v___jp_2348_;
}
else
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2578_; 
v___x_2575_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__17, &l_Lean_Meta_rwMatcher___closed__17_once, _init_l_Lean_Meta_rwMatcher___closed__17);
v___x_2576_ = l_Nat_reprFast(v_altIdx_2072_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set_tag(v___x_2540_, 3);
lean_ctor_set(v___x_2540_, 0, v___x_2576_);
v___x_2578_ = v___x_2540_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2579_ = l_Lean_MessageData_ofFormat(v___x_2578_);
v___x_2580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2575_);
lean_ctor_set(v___x_2580_, 1, v___x_2579_);
v___x_2581_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__19, &l_Lean_Meta_rwMatcher___closed__19_once, _init_l_Lean_Meta_rwMatcher___closed__19);
v___x_2582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2580_);
lean_ctor_set(v___x_2582_, 1, v___x_2581_);
v___x_2583_ = l_Nat_reprFast(v___x_2566_);
v___x_2584_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
v___x_2585_ = l_Lean_MessageData_ofFormat(v___x_2584_);
v___x_2586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2582_);
lean_ctor_set(v___x_2586_, 1, v___x_2585_);
v___x_2587_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__21, &l_Lean_Meta_rwMatcher___closed__21_once, _init_l_Lean_Meta_rwMatcher___closed__21);
v___x_2588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2586_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
v___x_2589_ = l_Lean_MessageData_ofConstName(v___x_2563_, v___x_2567_);
v___x_2590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2588_);
lean_ctor_set(v___x_2590_, 1, v___x_2589_);
v___x_2591_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2572_, v___x_2590_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_dec_ref_known(v___x_2591_, 1);
v___y_2349_ = v___x_2534_;
goto v___jp_2348_;
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec_ref(v_e_2073_);
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2591_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2591_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
}
}
}
else
{
lean_object* v_toCold_2601_; lean_object* v_options_2602_; lean_object* v_inheritedTraceOptions_2603_; uint8_t v_hasTrace_2604_; lean_object* v_nargs_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v_dummy_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
lean_dec(v___x_2563_);
lean_del_object(v___x_2540_);
v_toCold_2601_ = lean_ctor_get(v_a_2076_, 0);
v_options_2602_ = lean_ctor_get(v_toCold_2601_, 2);
v_inheritedTraceOptions_2603_ = lean_ctor_get(v_toCold_2601_, 11);
v_hasTrace_2604_ = lean_ctor_get_uint8(v_options_2602_, sizeof(void*)*1);
v_nargs_2605_ = l_Lean_Expr_getAppNumArgs(v_e_2073_);
v___x_2606_ = lean_array_get(v___x_2531_, v_a_2565_, v_altIdx_2072_);
lean_dec(v_altIdx_2072_);
lean_dec(v_a_2565_);
v___x_2607_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2608_ = l_Lean_Expr_constLevels_x21(v___x_2562_);
lean_dec_ref(v___x_2562_);
lean_inc(v___x_2606_);
v___x_2609_ = l_Lean_mkConst(v___x_2606_, v___x_2608_);
v_dummy_2610_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__22, &l_Lean_Meta_rwMatcher___closed__22_once, _init_l_Lean_Meta_rwMatcher___closed__22);
lean_inc(v_nargs_2605_);
v___x_2611_ = lean_mk_array(v_nargs_2605_, v_dummy_2610_);
v___x_2612_ = lean_unsigned_to_nat(1u);
v___x_2613_ = lean_nat_sub(v_nargs_2605_, v___x_2612_);
lean_dec(v_nargs_2605_);
lean_inc_ref(v_e_2073_);
v___x_2614_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2073_, v___x_2611_, v___x_2613_);
v___x_2615_ = l_Lean_mkAppN(v___x_2609_, v___x_2614_);
lean_dec_ref(v___x_2614_);
if (v_hasTrace_2604_ == 0)
{
lean_object* v___x_2616_; 
lean_inc(v_a_2077_);
lean_inc_ref(v_a_2076_);
lean_inc(v_a_2075_);
lean_inc_ref(v_a_2074_);
lean_inc_ref(v___x_2615_);
v___x_2616_ = lean_infer_type(v___x_2615_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; uint8_t v___x_2618_; lean_object* v___x_2619_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v___x_2616_, 1);
v___x_2618_ = 0;
v___x_2619_ = l_Lean_Meta_forallMetaTelescope(v_a_2617_, v___x_2618_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; lean_object* v_snd_2621_; lean_object* v_fst_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2660_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_a_2620_);
lean_dec_ref_known(v___x_2619_, 1);
v_snd_2621_ = lean_ctor_get(v_a_2620_, 1);
v_fst_2622_ = lean_ctor_get(v_a_2620_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v_a_2620_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2624_ = v_a_2620_;
v_isShared_2625_ = v_isSharedCheck_2660_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_snd_2621_);
lean_inc(v_fst_2622_);
lean_dec(v_a_2620_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2660_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v_snd_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2658_; 
v_snd_2626_ = lean_ctor_get(v_snd_2621_, 1);
v_isSharedCheck_2658_ = !lean_is_exclusive(v_snd_2621_);
if (v_isSharedCheck_2658_ == 0)
{
lean_object* v_unused_2659_; 
v_unused_2659_ = lean_ctor_get(v_snd_2621_, 0);
lean_dec(v_unused_2659_);
v___x_2628_ = v_snd_2621_;
v_isShared_2629_ = v_isSharedCheck_2658_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_snd_2626_);
lean_dec(v_snd_2621_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2658_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2630_; size_t v_sz_2631_; size_t v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; uint8_t v___x_2636_; 
v___x_2630_ = l_Lean_mkAppN(v___x_2615_, v_fst_2622_);
v_sz_2631_ = lean_array_size(v_fst_2622_);
v___x_2632_ = ((size_t)0ULL);
v___x_2633_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_2631_, v___x_2632_, v_fst_2622_);
v___x_2634_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_2635_ = lean_unsigned_to_nat(4u);
v___x_2636_ = l_Lean_Expr_isAppOfArity(v_snd_2626_, v___x_2634_, v___x_2635_);
if (v___x_2636_ == 0)
{
lean_object* v___x_2637_; lean_object* v___x_2638_; uint8_t v___x_2639_; 
v___x_2637_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_2638_ = lean_unsigned_to_nat(3u);
v___x_2639_ = l_Lean_Expr_isAppOfArity(v_snd_2626_, v___x_2637_, v___x_2638_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2643_; 
lean_dec_ref(v___x_2633_);
lean_dec_ref(v___x_2630_);
lean_dec(v_snd_2626_);
lean_dec_ref(v_e_2073_);
v___x_2640_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
lean_inc(v___x_2606_);
v___x_2641_ = l_Lean_MessageData_ofConstName(v___x_2606_, v___y_2533_);
if (v_isShared_2629_ == 0)
{
lean_ctor_set_tag(v___x_2628_, 7);
lean_ctor_set(v___x_2628_, 1, v___x_2641_);
lean_ctor_set(v___x_2628_, 0, v___x_2640_);
v___x_2643_ = v___x_2628_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2640_);
lean_ctor_set(v_reuseFailAlloc_2650_, 1, v___x_2641_);
v___x_2643_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
lean_object* v___x_2644_; lean_object* v___x_2646_; 
v___x_2644_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
if (v_isShared_2625_ == 0)
{
lean_ctor_set_tag(v___x_2624_, 7);
lean_ctor_set(v___x_2624_, 1, v___x_2644_);
lean_ctor_set(v___x_2624_, 0, v___x_2643_);
v___x_2646_ = v___x_2624_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2643_);
lean_ctor_set(v_reuseFailAlloc_2649_, 1, v___x_2644_);
v___x_2646_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
lean_object* v___x_2647_; lean_object* v_a_2648_; 
v___x_2647_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2646_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_a_2648_);
lean_dec_ref(v___x_2647_);
v___y_2137_ = v___y_2533_;
v___y_2138_ = v___x_2607_;
v___y_2139_ = v___x_2606_;
v___y_2140_ = v___f_2536_;
v_a_2141_ = v_a_2648_;
goto v___jp_2136_;
}
}
}
else
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
lean_del_object(v___x_2628_);
lean_del_object(v___x_2624_);
v___x_2651_ = l_Lean_Expr_appFn_x21(v_snd_2626_);
v___x_2652_ = l_Lean_Expr_appArg_x21(v___x_2651_);
lean_dec_ref(v___x_2651_);
v___x_2653_ = l_Lean_Expr_appArg_x21(v_snd_2626_);
lean_dec(v_snd_2626_);
v___y_2497_ = v___x_2633_;
v___y_2498_ = v___y_2533_;
v___y_2499_ = v___x_2607_;
v___y_2500_ = v___x_2630_;
v___y_2501_ = v___x_2606_;
v___y_2502_ = v___x_2534_;
v___y_2503_ = v___x_2632_;
v___y_2504_ = v___f_2536_;
v_fst_2505_ = v___y_2533_;
v_fst_2506_ = v___x_2652_;
v_snd_2507_ = v___x_2653_;
v___y_2508_ = v_a_2074_;
v___y_2509_ = v_a_2075_;
v___y_2510_ = v_a_2076_;
v___y_2511_ = v_a_2077_;
goto v___jp_2496_;
}
}
else
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
lean_del_object(v___x_2628_);
lean_del_object(v___x_2624_);
v___x_2654_ = l_Lean_Expr_appFn_x21(v_snd_2626_);
v___x_2655_ = l_Lean_Expr_appFn_x21(v___x_2654_);
lean_dec_ref(v___x_2654_);
v___x_2656_ = l_Lean_Expr_appArg_x21(v___x_2655_);
lean_dec_ref(v___x_2655_);
v___x_2657_ = l_Lean_Expr_appArg_x21(v_snd_2626_);
lean_dec(v_snd_2626_);
v___y_2497_ = v___x_2633_;
v___y_2498_ = v___y_2533_;
v___y_2499_ = v___x_2607_;
v___y_2500_ = v___x_2630_;
v___y_2501_ = v___x_2606_;
v___y_2502_ = v___x_2534_;
v___y_2503_ = v___x_2632_;
v___y_2504_ = v___f_2536_;
v_fst_2505_ = v___x_2534_;
v_fst_2506_ = v___x_2656_;
v_snd_2507_ = v___x_2657_;
v___y_2508_ = v_a_2074_;
v___y_2509_ = v_a_2075_;
v___y_2510_ = v_a_2076_;
v___y_2511_ = v_a_2077_;
goto v___jp_2496_;
}
}
}
}
else
{
lean_object* v_a_2661_; 
lean_dec_ref(v___x_2615_);
lean_dec_ref(v_e_2073_);
v_a_2661_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_a_2661_);
lean_dec_ref_known(v___x_2619_, 1);
v___y_2137_ = v___y_2533_;
v___y_2138_ = v___x_2607_;
v___y_2139_ = v___x_2606_;
v___y_2140_ = v___f_2536_;
v_a_2141_ = v_a_2661_;
goto v___jp_2136_;
}
}
else
{
lean_object* v_a_2662_; 
lean_dec_ref(v___x_2615_);
lean_dec_ref(v_e_2073_);
v_a_2662_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2662_);
lean_dec_ref_known(v___x_2616_, 1);
v___y_2137_ = v___y_2533_;
v___y_2138_ = v___x_2607_;
v___y_2139_ = v___x_2606_;
v___y_2140_ = v___f_2536_;
v_a_2141_ = v_a_2662_;
goto v___jp_2136_;
}
}
else
{
lean_object* v___x_2663_; lean_object* v___f_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; uint8_t v___x_2667_; 
v___x_2663_ = lean_box(v___y_2533_);
lean_inc_ref(v_e_2073_);
lean_inc(v___x_2606_);
v___f_2664_ = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__1___boxed), 9, 3);
lean_closure_set(v___f_2664_, 0, v___x_2606_);
lean_closure_set(v___f_2664_, 1, v___x_2663_);
lean_closure_set(v___f_2664_, 2, v_e_2073_);
v___x_2665_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1));
v___x_2666_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2667_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2603_, v_options_2602_, v___x_2666_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; uint8_t v___x_2669_; 
v___x_2668_ = l_Lean_trace_profiler;
v___x_2669_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_options_2602_, v___x_2668_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2670_; 
lean_dec_ref(v___f_2664_);
lean_inc(v_a_2077_);
lean_inc_ref(v_a_2076_);
lean_inc(v_a_2075_);
lean_inc_ref(v_a_2074_);
lean_inc_ref(v___x_2615_);
v___x_2670_ = lean_infer_type(v___x_2615_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; uint8_t v___x_2672_; lean_object* v___x_2673_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2671_);
lean_dec_ref_known(v___x_2670_, 1);
v___x_2672_ = 0;
v___x_2673_ = l_Lean_Meta_forallMetaTelescope(v_a_2671_, v___x_2672_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; lean_object* v_snd_2675_; 
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2674_);
lean_dec_ref_known(v___x_2673_, 1);
v_snd_2675_ = lean_ctor_get(v_a_2674_, 1);
lean_inc(v_snd_2675_);
if (v___x_2667_ == 0)
{
lean_object* v_fst_2676_; lean_object* v_snd_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v_fst_2676_ = lean_ctor_get(v_a_2674_, 0);
lean_inc(v_fst_2676_);
lean_dec(v_a_2674_);
v_snd_2677_ = lean_ctor_get(v_snd_2675_, 1);
lean_inc(v_snd_2677_);
lean_dec(v_snd_2675_);
v___x_2678_ = lean_box(0);
lean_inc(v___x_2606_);
v___x_2679_ = l_Lean_Meta_rwMatcher___lam__4(v___x_2534_, v___x_2615_, v_fst_2676_, v___x_2606_, v_e_2073_, v___y_2533_, v_snd_2677_, v___x_2678_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
lean_dec(v_snd_2677_);
v___y_2145_ = v___y_2533_;
v___y_2146_ = v___x_2607_;
v___y_2147_ = v___x_2606_;
v___y_2148_ = v___f_2536_;
v___y_2149_ = v___x_2679_;
goto v___jp_2144_;
}
else
{
lean_object* v_fst_2680_; lean_object* v_snd_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2694_; 
v_fst_2680_ = lean_ctor_get(v_a_2674_, 0);
lean_inc(v_fst_2680_);
lean_dec(v_a_2674_);
v_snd_2681_ = lean_ctor_get(v_snd_2675_, 1);
v_isSharedCheck_2694_ = !lean_is_exclusive(v_snd_2675_);
if (v_isSharedCheck_2694_ == 0)
{
lean_object* v_unused_2695_; 
v_unused_2695_ = lean_ctor_get(v_snd_2675_, 0);
lean_dec(v_unused_2695_);
v___x_2683_ = v_snd_2675_;
v_isShared_2684_ = v_isSharedCheck_2694_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_snd_2681_);
lean_dec(v_snd_2675_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2694_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2688_; 
v___x_2685_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2681_);
v___x_2686_ = l_Lean_indentExpr(v_snd_2681_);
if (v_isShared_2684_ == 0)
{
lean_ctor_set_tag(v___x_2683_, 7);
lean_ctor_set(v___x_2683_, 1, v___x_2686_);
lean_ctor_set(v___x_2683_, 0, v___x_2685_);
v___x_2688_ = v___x_2683_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2685_);
lean_ctor_set(v_reuseFailAlloc_2693_, 1, v___x_2686_);
v___x_2688_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
lean_object* v___x_2689_; 
v___x_2689_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2607_, v___x_2688_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; lean_object* v___x_2691_; 
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2690_);
lean_dec_ref_known(v___x_2689_, 1);
lean_inc(v___x_2606_);
v___x_2691_ = l_Lean_Meta_rwMatcher___lam__4(v___x_2534_, v___x_2615_, v_fst_2680_, v___x_2606_, v_e_2073_, v___y_2533_, v_snd_2681_, v_a_2690_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
lean_dec(v_snd_2681_);
v___y_2145_ = v___y_2533_;
v___y_2146_ = v___x_2607_;
v___y_2147_ = v___x_2606_;
v___y_2148_ = v___f_2536_;
v___y_2149_ = v___x_2691_;
goto v___jp_2144_;
}
else
{
lean_object* v_a_2692_; 
lean_dec(v_snd_2681_);
lean_dec(v_fst_2680_);
lean_dec_ref(v___x_2615_);
lean_dec_ref(v_e_2073_);
v_a_2692_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2692_);
lean_dec_ref_known(v___x_2689_, 1);
v___y_2137_ = v___y_2533_;
v___y_2138_ = v___x_2607_;
v___y_2139_ = v___x_2606_;
v___y_2140_ = v___f_2536_;
v_a_2141_ = v_a_2692_;
goto v___jp_2136_;
}
}
}
}
}
else
{
lean_object* v_a_2696_; 
lean_dec_ref(v___x_2615_);
lean_dec_ref(v_e_2073_);
v_a_2696_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2696_);
lean_dec_ref_known(v___x_2673_, 1);
v___y_2137_ = v___y_2533_;
v___y_2138_ = v___x_2607_;
v___y_2139_ = v___x_2606_;
v___y_2140_ = v___f_2536_;
v_a_2141_ = v_a_2696_;
goto v___jp_2136_;
}
}
else
{
lean_object* v_a_2697_; 
lean_dec_ref(v___x_2615_);
lean_dec_ref(v_e_2073_);
v_a_2697_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2697_);
lean_dec_ref_known(v___x_2670_, 1);
v___y_2137_ = v___y_2533_;
v___y_2138_ = v___x_2607_;
v___y_2139_ = v___x_2606_;
v___y_2140_ = v___f_2536_;
v_a_2141_ = v_a_2697_;
goto v___jp_2136_;
}
}
else
{
lean_inc(v___x_2606_);
lean_inc_ref(v___x_2615_);
v___y_2269_ = v___y_2533_;
v___y_2270_ = v___x_2615_;
v___y_2271_ = v___x_2606_;
v___y_2272_ = v___x_2534_;
v___y_2273_ = v___f_2664_;
v___y_2274_ = v___y_2533_;
v___y_2275_ = v___x_2607_;
v___y_2276_ = v___x_2615_;
v___y_2277_ = v___x_2667_;
v___y_2278_ = v_inheritedTraceOptions_2603_;
v___y_2279_ = v___x_2606_;
v___y_2280_ = v___x_2534_;
v___y_2281_ = v___x_2665_;
v___y_2282_ = v___f_2536_;
v___y_2283_ = v_options_2602_;
goto v___jp_2268_;
}
}
else
{
lean_inc(v___x_2606_);
lean_inc_ref(v___x_2615_);
v___y_2269_ = v___y_2533_;
v___y_2270_ = v___x_2615_;
v___y_2271_ = v___x_2606_;
v___y_2272_ = v___x_2534_;
v___y_2273_ = v___f_2664_;
v___y_2274_ = v___y_2533_;
v___y_2275_ = v___x_2607_;
v___y_2276_ = v___x_2615_;
v___y_2277_ = v___x_2667_;
v___y_2278_ = v_inheritedTraceOptions_2603_;
v___y_2279_ = v___x_2606_;
v___y_2280_ = v___x_2534_;
v___y_2281_ = v___x_2665_;
v___y_2282_ = v___f_2536_;
v___y_2283_ = v_options_2602_;
goto v___jp_2268_;
}
}
}
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
lean_dec(v___x_2563_);
lean_dec_ref(v___x_2562_);
lean_del_object(v___x_2540_);
lean_dec_ref(v___f_2536_);
lean_dec_ref(v_e_2073_);
lean_dec(v_altIdx_2072_);
v_a_2698_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2564_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2564_);
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
lean_object* v___x_2707_; 
lean_dec(v_altIdx_2072_);
v___x_2707_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(v_e_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2717_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2710_ = v___x_2707_;
v_isShared_2711_ = v_isSharedCheck_2717_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2707_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2717_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2715_; 
v___x_2712_ = lean_box(0);
v___x_2713_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2713_, 0, v_a_2708_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
lean_ctor_set_uint8(v___x_2713_, sizeof(void*)*2, v___x_2534_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 0, v___x_2713_);
v___x_2715_ = v___x_2710_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v___x_2713_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
else
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
v_a_2718_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2720_ = v___x_2707_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2707_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2718_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___boxed(lean_object* v_altIdx_2730_, lean_object* v_e_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Lean_Meta_rwMatcher(v_altIdx_2730_, v_e_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_);
lean_dec(v_a_2735_);
lean_dec_ref(v_a_2734_);
lean_dec(v_a_2733_);
lean_dec_ref(v_a_2732_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(lean_object* v_mvarId_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v___x_2744_; 
v___x_2744_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_mvarId_2738_, v___y_2740_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___boxed(lean_object* v_mvarId_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(v_mvarId_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v_mvarId_2745_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5(lean_object* v_00_u03b1_2752_, lean_object* v_msg_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v___x_2759_; 
v___x_2759_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v_msg_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___boxed(lean_object* v_00_u03b1_2760_, lean_object* v_msg_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5(v_00_u03b1_2760_, v_msg_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14(lean_object* v_00_u03b1_2768_, lean_object* v_x_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v___x_2775_; 
v___x_2775_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(v_x_2769_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___boxed(lean_object* v_00_u03b1_2776_, lean_object* v_x_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v_res_2783_; 
v_res_2783_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14(v_00_u03b1_2776_, v_x_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12(lean_object* v_inst_2784_, lean_object* v_a_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
lean_object* v___x_2791_; 
v___x_2791_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(v_a_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___boxed(lean_object* v_inst_2792_, lean_object* v_a_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12(v_inst_2792_, v_a_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
return v_res_2799_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(lean_object* v_00_u03b2_2800_, lean_object* v_x_2801_, lean_object* v_x_2802_){
_start:
{
uint8_t v___x_2803_; 
v___x_2803_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_x_2801_, v_x_2802_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2804_, lean_object* v_x_2805_, lean_object* v_x_2806_){
_start:
{
uint8_t v_res_2807_; lean_object* v_r_2808_; 
v_res_2807_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(v_00_u03b2_2804_, v_x_2805_, v_x_2806_);
lean_dec(v_x_2806_);
lean_dec_ref(v_x_2805_);
v_r_2808_ = lean_box(v_res_2807_);
return v_r_2808_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5(lean_object* v_00_u03b2_2809_, lean_object* v_x_2810_, size_t v_x_2811_, lean_object* v_x_2812_){
_start:
{
uint8_t v___x_2813_; 
v___x_2813_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_2810_, v_x_2811_, v_x_2812_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b2_2814_, lean_object* v_x_2815_, lean_object* v_x_2816_, lean_object* v_x_2817_){
_start:
{
size_t v_x_88386__boxed_2818_; uint8_t v_res_2819_; lean_object* v_r_2820_; 
v_x_88386__boxed_2818_ = lean_unbox_usize(v_x_2816_);
lean_dec(v_x_2816_);
v_res_2819_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5(v_00_u03b2_2814_, v_x_2815_, v_x_88386__boxed_2818_, v_x_2817_);
lean_dec(v_x_2817_);
lean_dec_ref(v_x_2815_);
v_r_2820_ = lean_box(v_res_2819_);
return v_r_2820_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18(lean_object* v_00_u03b2_2821_, lean_object* v_keys_2822_, lean_object* v_vals_2823_, lean_object* v_heq_2824_, lean_object* v_i_2825_, lean_object* v_k_2826_){
_start:
{
uint8_t v___x_2827_; 
v___x_2827_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(v_keys_2822_, v_i_2825_, v_k_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___boxed(lean_object* v_00_u03b2_2828_, lean_object* v_keys_2829_, lean_object* v_vals_2830_, lean_object* v_heq_2831_, lean_object* v_i_2832_, lean_object* v_k_2833_){
_start:
{
uint8_t v_res_2834_; lean_object* v_r_2835_; 
v_res_2834_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18(v_00_u03b2_2828_, v_keys_2829_, v_vals_2830_, v_heq_2831_, v_i_2832_, v_k_2833_);
lean_dec(v_k_2833_);
lean_dec_ref(v_vals_2830_);
lean_dec_ref(v_keys_2829_);
v_r_2835_ = lean_box(v_res_2834_);
return v_r_2835_;
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
