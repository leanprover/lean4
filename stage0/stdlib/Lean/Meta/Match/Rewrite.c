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
v___x_481_ = lean_st_ref_put(v___y_454_, v___x_480_);
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
lean_dec_ref_known(v___x_508_, 1);
if (lean_obj_tag(v_val_510_) == 1)
{
uint8_t v_v_511_; 
v_v_511_ = lean_ctor_get_uint8(v_val_510_, 0);
lean_dec_ref_known(v_val_510_, 0);
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
uint8_t v___x_83853__boxed_537_; lean_object* v_res_538_; 
v___x_83853__boxed_537_ = lean_unbox(v___x_530_);
v_res_538_ = l_Lean_Meta_rwMatcher___lam__0(v_e_529_, v___x_83853__boxed_537_, v_____r_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
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
uint8_t v___y_83895__boxed_571_; lean_object* v_res_572_; 
v___y_83895__boxed_571_ = lean_unbox(v___y_563_);
v_res_572_ = l_Lean_Meta_rwMatcher___lam__1(v___x_562_, v___y_83895__boxed_571_, v_e_564_, v_x_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
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
v_options_602_ = lean_ctor_get(v___y_594_, 1);
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
v_ref_619_ = lean_ctor_get(v___y_616_, 4);
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(lean_object* v_keys_637_, lean_object* v_i_638_, lean_object* v_k_639_){
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
return v___x_641_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg___boxed(lean_object* v_keys_647_, lean_object* v_i_648_, lean_object* v_k_649_){
_start:
{
uint8_t v_res_650_; lean_object* v_r_651_; 
v_res_650_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(v_keys_647_, v_i_648_, v_k_649_);
lean_dec(v_k_649_);
lean_dec_ref(v_keys_647_);
v_r_651_ = lean_box(v_res_650_);
return v_r_651_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(lean_object* v_x_652_, size_t v_x_653_, lean_object* v_x_654_){
_start:
{
if (lean_obj_tag(v_x_652_) == 0)
{
lean_object* v_es_655_; lean_object* v___x_656_; size_t v___x_657_; size_t v___x_658_; lean_object* v_j_659_; lean_object* v___x_660_; 
v_es_655_ = lean_ctor_get(v_x_652_, 0);
v___x_656_ = lean_box(2);
v___x_657_ = ((size_t)31ULL);
v___x_658_ = lean_usize_land(v_x_653_, v___x_657_);
v_j_659_ = lean_usize_to_nat(v___x_658_);
v___x_660_ = lean_array_get_borrowed(v___x_656_, v_es_655_, v_j_659_);
lean_dec(v_j_659_);
switch(lean_obj_tag(v___x_660_))
{
case 0:
{
lean_object* v_key_661_; uint8_t v___x_662_; 
v_key_661_ = lean_ctor_get(v___x_660_, 0);
v___x_662_ = l_Lean_instBEqMVarId_beq(v_x_654_, v_key_661_);
return v___x_662_;
}
case 1:
{
lean_object* v_node_663_; size_t v___x_664_; size_t v___x_665_; 
v_node_663_ = lean_ctor_get(v___x_660_, 0);
v___x_664_ = ((size_t)5ULL);
v___x_665_ = lean_usize_shift_right(v_x_653_, v___x_664_);
v_x_652_ = v_node_663_;
v_x_653_ = v___x_665_;
goto _start;
}
default: 
{
uint8_t v___x_667_; 
v___x_667_ = 0;
return v___x_667_;
}
}
}
else
{
lean_object* v_ks_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
v_ks_668_ = lean_ctor_get(v_x_652_, 0);
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(v_ks_668_, v___x_669_, v_x_654_);
return v___x_670_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_671_, lean_object* v_x_672_, lean_object* v_x_673_){
_start:
{
size_t v_x_84028__boxed_674_; uint8_t v_res_675_; lean_object* v_r_676_; 
v_x_84028__boxed_674_ = lean_unbox_usize(v_x_672_);
lean_dec(v_x_672_);
v_res_675_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_671_, v_x_84028__boxed_674_, v_x_673_);
lean_dec(v_x_673_);
lean_dec_ref(v_x_671_);
v_r_676_ = lean_box(v_res_675_);
return v_r_676_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(lean_object* v_x_677_, lean_object* v_x_678_){
_start:
{
uint64_t v___x_679_; size_t v___x_680_; uint8_t v___x_681_; 
v___x_679_ = l_Lean_instHashableMVarId_hash(v_x_678_);
v___x_680_ = lean_uint64_to_usize(v___x_679_);
v___x_681_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_677_, v___x_680_, v_x_678_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg___boxed(lean_object* v_x_682_, lean_object* v_x_683_){
_start:
{
uint8_t v_res_684_; lean_object* v_r_685_; 
v_res_684_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_x_682_, v_x_683_);
lean_dec(v_x_683_);
lean_dec_ref(v_x_682_);
v_r_685_ = lean_box(v_res_684_);
return v_r_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(lean_object* v_mvarId_686_, lean_object* v___y_687_){
_start:
{
lean_object* v___x_689_; lean_object* v_mctx_690_; lean_object* v_eAssignment_691_; uint8_t v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_689_ = lean_st_ref_get(v___y_687_);
v_mctx_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc_ref(v_mctx_690_);
lean_dec(v___x_689_);
v_eAssignment_691_ = lean_ctor_get(v_mctx_690_, 8);
lean_inc_ref(v_eAssignment_691_);
lean_dec_ref(v_mctx_690_);
v___x_692_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_eAssignment_691_, v_mvarId_686_);
lean_dec_ref(v_eAssignment_691_);
v___x_693_ = lean_box(v___x_692_);
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg___boxed(lean_object* v_mvarId_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_mvarId_695_, v___y_696_);
lean_dec(v___y_696_);
lean_dec(v_mvarId_695_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(lean_object* v_as_699_, size_t v_i_700_, size_t v_stop_701_, lean_object* v_b_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_a_709_; uint8_t v___x_713_; 
v___x_713_ = lean_usize_dec_eq(v_i_700_, v_stop_701_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; lean_object* v___x_717_; 
v___x_714_ = lean_array_uget_borrowed(v_as_699_, v_i_700_);
v___x_717_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v___x_714_, v___y_704_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; uint8_t v___x_719_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v___x_717_, 1);
v___x_719_ = lean_unbox(v_a_718_);
lean_dec(v_a_718_);
if (v___x_719_ == 0)
{
goto v___jp_715_;
}
else
{
v_a_709_ = v_b_702_;
goto v___jp_708_;
}
}
else
{
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_720_; uint8_t v___x_721_; 
v_a_720_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_720_);
lean_dec_ref_known(v___x_717_, 1);
v___x_721_ = lean_unbox(v_a_720_);
lean_dec(v_a_720_);
if (v___x_721_ == 0)
{
v_a_709_ = v_b_702_;
goto v___jp_708_;
}
else
{
goto v___jp_715_;
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec_ref(v_b_702_);
v_a_722_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_717_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_717_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
v___jp_715_:
{
lean_object* v___x_716_; 
lean_inc(v___x_714_);
v___x_716_ = lean_array_push(v_b_702_, v___x_714_);
v_a_709_ = v___x_716_;
goto v___jp_708_;
}
}
else
{
lean_object* v___x_730_; 
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v_b_702_);
return v___x_730_;
}
v___jp_708_:
{
size_t v___x_710_; size_t v___x_711_; 
v___x_710_ = ((size_t)1ULL);
v___x_711_ = lean_usize_add(v_i_700_, v___x_710_);
v_i_700_ = v___x_711_;
v_b_702_ = v_a_709_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8___boxed(lean_object* v_as_731_, lean_object* v_i_732_, lean_object* v_stop_733_, lean_object* v_b_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
size_t v_i_boxed_740_; size_t v_stop_boxed_741_; lean_object* v_res_742_; 
v_i_boxed_740_ = lean_unbox_usize(v_i_732_);
lean_dec(v_i_732_);
v_stop_boxed_741_ = lean_unbox_usize(v_stop_733_);
lean_dec(v_stop_733_);
v_res_742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v_as_731_, v_i_boxed_740_, v_stop_boxed_741_, v_b_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec_ref(v_as_731_);
return v_res_742_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__0));
v___x_745_ = l_Lean_stringToMessageData(v___x_744_);
return v___x_745_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__2));
v___x_748_ = l_Lean_stringToMessageData(v___x_747_);
return v___x_748_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__4));
v___x_751_ = l_Lean_stringToMessageData(v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(lean_object* v_as_752_, size_t v_sz_753_, size_t v_i_754_, lean_object* v_b_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_a_762_; uint8_t v___x_766_; 
v___x_766_ = lean_usize_dec_lt(v_i_754_, v_sz_753_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; 
v___x_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_767_, 0, v_b_755_);
return v___x_767_;
}
else
{
lean_object* v_a_768_; lean_object* v___x_769_; 
v_a_768_ = lean_array_uget_borrowed(v_as_752_, v_i_754_);
v___x_769_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_a_768_, v___y_757_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_771_; lean_object* v___y_773_; lean_object* v___y_775_; lean_object* v___y_776_; uint8_t v___y_777_; lean_object* v___y_793_; lean_object* v___y_795_; lean_object* v___y_796_; uint8_t v___y_797_; lean_object* v___y_813_; uint8_t v___x_814_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_770_);
lean_dec_ref_known(v___x_769_, 1);
v___x_771_ = lean_box(0);
v___x_814_ = lean_unbox(v_a_770_);
lean_dec(v_a_770_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; 
lean_inc(v_a_768_);
v___x_815_ = l_Lean_MVarId_getType(v_a_768_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; uint8_t v___x_817_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc_n(v_a_816_, 2);
lean_dec_ref_known(v___x_815_, 1);
v___x_817_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_a_816_);
if (v___x_817_ == 0)
{
uint8_t v___x_818_; 
v___x_818_ = l_Lean_Expr_isEq(v_a_816_);
if (v___x_818_ == 0)
{
uint8_t v___x_819_; 
v___x_819_ = l_Lean_Expr_isHEq(v_a_816_);
lean_dec(v_a_816_);
if (v___x_819_ == 0)
{
v_a_762_ = v___x_771_;
goto v___jp_761_;
}
else
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_Meta_saveState___redArg(v___y_757_, v___y_759_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_822_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_a_821_);
lean_dec_ref_known(v___x_820_, 1);
lean_inc(v_a_768_);
v___x_822_ = l_Lean_MVarId_assumption(v_a_768_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_dec(v_a_821_);
v___y_793_ = v___x_822_;
goto v___jp_792_;
}
else
{
lean_object* v_a_823_; uint8_t v___y_825_; uint8_t v___x_841_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_a_823_);
v___x_841_ = l_Lean_Exception_isInterrupt(v_a_823_);
if (v___x_841_ == 0)
{
uint8_t v___x_842_; 
v___x_842_ = l_Lean_Exception_isRuntime(v_a_823_);
v___y_825_ = v___x_842_;
goto v___jp_824_;
}
else
{
lean_dec(v_a_823_);
v___y_825_ = v___x_841_;
goto v___jp_824_;
}
v___jp_824_:
{
if (v___y_825_ == 0)
{
lean_object* v___x_826_; 
lean_dec_ref_known(v___x_822_, 1);
v___x_826_ = l_Lean_Meta_SavedState_restore___redArg(v_a_821_, v___y_757_, v___y_759_);
lean_dec(v_a_821_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v___x_827_; 
lean_dec_ref_known(v___x_826_, 1);
v___x_827_ = l_Lean_Meta_saveState___redArg(v___y_757_, v___y_759_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_829_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
lean_dec_ref_known(v___x_827_, 1);
lean_inc(v_a_768_);
v___x_829_ = l_Lean_MVarId_hrefl(v_a_768_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_dec(v_a_828_);
v___y_793_ = v___x_829_;
goto v___jp_792_;
}
else
{
lean_object* v_a_830_; uint8_t v___x_831_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
v___x_831_ = l_Lean_Exception_isInterrupt(v_a_830_);
if (v___x_831_ == 0)
{
uint8_t v___x_832_; 
v___x_832_ = l_Lean_Exception_isRuntime(v_a_830_);
v___y_795_ = v_a_828_;
v___y_796_ = v___x_829_;
v___y_797_ = v___x_832_;
goto v___jp_794_;
}
else
{
lean_dec(v_a_830_);
v___y_795_ = v_a_828_;
v___y_796_ = v___x_829_;
v___y_797_ = v___x_831_;
goto v___jp_794_;
}
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
v_a_833_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_827_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_827_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
else
{
v___y_793_ = v___x_826_;
goto v___jp_792_;
}
}
else
{
lean_dec(v_a_821_);
v___y_793_ = v___x_822_;
goto v___jp_792_;
}
}
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
v_a_843_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_820_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_820_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
else
{
lean_object* v___x_851_; 
lean_dec(v_a_816_);
v___x_851_ = l_Lean_Meta_saveState___redArg(v___y_757_, v___y_759_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_853_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_852_);
lean_dec_ref_known(v___x_851_, 1);
lean_inc(v_a_768_);
v___x_853_ = l_Lean_MVarId_assumption(v_a_768_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_dec(v_a_852_);
v___y_773_ = v___x_853_;
goto v___jp_772_;
}
else
{
lean_object* v_a_854_; uint8_t v___y_856_; uint8_t v___x_872_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
v___x_872_ = l_Lean_Exception_isInterrupt(v_a_854_);
if (v___x_872_ == 0)
{
uint8_t v___x_873_; 
v___x_873_ = l_Lean_Exception_isRuntime(v_a_854_);
v___y_856_ = v___x_873_;
goto v___jp_855_;
}
else
{
lean_dec(v_a_854_);
v___y_856_ = v___x_872_;
goto v___jp_855_;
}
v___jp_855_:
{
if (v___y_856_ == 0)
{
lean_object* v___x_857_; 
lean_dec_ref_known(v___x_853_, 1);
v___x_857_ = l_Lean_Meta_SavedState_restore___redArg(v_a_852_, v___y_757_, v___y_759_);
lean_dec(v_a_852_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v___x_858_; 
lean_dec_ref_known(v___x_857_, 1);
v___x_858_ = l_Lean_Meta_saveState___redArg(v___y_757_, v___y_759_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_860_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref_known(v___x_858_, 1);
lean_inc(v_a_768_);
v___x_860_ = l_Lean_MVarId_refl(v_a_768_, v___x_818_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_dec(v_a_859_);
v___y_773_ = v___x_860_;
goto v___jp_772_;
}
else
{
lean_object* v_a_861_; uint8_t v___x_862_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
v___x_862_ = l_Lean_Exception_isInterrupt(v_a_861_);
if (v___x_862_ == 0)
{
uint8_t v___x_863_; 
v___x_863_ = l_Lean_Exception_isRuntime(v_a_861_);
v___y_775_ = v___x_860_;
v___y_776_ = v_a_859_;
v___y_777_ = v___x_863_;
goto v___jp_774_;
}
else
{
lean_dec(v_a_861_);
v___y_775_ = v___x_860_;
v___y_776_ = v_a_859_;
v___y_777_ = v___x_862_;
goto v___jp_774_;
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
v_a_864_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_858_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_858_);
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
v___y_773_ = v___x_857_;
goto v___jp_772_;
}
}
else
{
lean_dec(v_a_852_);
v___y_773_ = v___x_853_;
goto v___jp_772_;
}
}
}
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
v_a_874_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_851_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_851_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
}
else
{
lean_object* v___x_882_; 
lean_dec(v_a_816_);
v___x_882_ = l_Lean_Meta_saveState___redArg(v___y_757_, v___y_759_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_884_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v___x_882_, 1);
lean_inc(v_a_768_);
v___x_884_ = l_Lean_MVarId_assumption(v_a_768_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_dec(v_a_883_);
v___y_813_ = v___x_884_;
goto v___jp_812_;
}
else
{
lean_object* v_a_885_; uint8_t v___y_887_; uint8_t v___x_902_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
v___x_902_ = l_Lean_Exception_isInterrupt(v_a_885_);
if (v___x_902_ == 0)
{
uint8_t v___x_903_; 
v___x_903_ = l_Lean_Exception_isRuntime(v_a_885_);
v___y_887_ = v___x_903_;
goto v___jp_886_;
}
else
{
lean_dec(v_a_885_);
v___y_887_ = v___x_902_;
goto v___jp_886_;
}
v___jp_886_:
{
if (v___y_887_ == 0)
{
lean_object* v___x_888_; 
lean_dec_ref_known(v___x_884_, 1);
v___x_888_ = l_Lean_Meta_SavedState_restore___redArg(v_a_883_, v___y_757_, v___y_759_);
lean_dec(v_a_883_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_900_; 
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_900_ == 0)
{
lean_object* v_unused_901_; 
v_unused_901_ = lean_ctor_get(v___x_888_, 0);
lean_dec(v_unused_901_);
v___x_890_ = v___x_888_;
v_isShared_891_ = v_isSharedCheck_900_;
goto v_resetjp_889_;
}
else
{
lean_dec(v___x_888_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_900_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_892_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5);
lean_inc(v_a_768_);
if (v_isShared_891_ == 0)
{
lean_ctor_set_tag(v___x_890_, 1);
lean_ctor_set(v___x_890_, 0, v_a_768_);
v___x_894_ = v___x_890_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_768_);
v___x_894_ = v_reuseFailAlloc_899_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_892_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_897_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
v___y_813_ = v___x_898_;
goto v___jp_812_;
}
}
}
else
{
v___y_813_ = v___x_888_;
goto v___jp_812_;
}
}
else
{
lean_dec(v_a_883_);
v___y_813_ = v___x_884_;
goto v___jp_812_;
}
}
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
v_a_904_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_882_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_882_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
v_a_912_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_815_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_815_);
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
v_a_762_ = v___x_771_;
goto v___jp_761_;
}
v___jp_772_:
{
if (lean_obj_tag(v___y_773_) == 0)
{
lean_dec_ref_known(v___y_773_, 1);
v_a_762_ = v___x_771_;
goto v___jp_761_;
}
else
{
return v___y_773_;
}
}
v___jp_774_:
{
if (v___y_777_ == 0)
{
lean_object* v___x_778_; 
lean_dec_ref(v___y_775_);
v___x_778_ = l_Lean_Meta_SavedState_restore___redArg(v___y_776_, v___y_757_, v___y_759_);
lean_dec_ref(v___y_776_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_790_; 
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_790_ == 0)
{
lean_object* v_unused_791_; 
v_unused_791_ = lean_ctor_get(v___x_778_, 0);
lean_dec(v_unused_791_);
v___x_780_ = v___x_778_;
v_isShared_781_ = v_isSharedCheck_790_;
goto v_resetjp_779_;
}
else
{
lean_dec(v___x_778_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_790_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1);
lean_inc(v_a_768_);
if (v_isShared_781_ == 0)
{
lean_ctor_set_tag(v___x_780_, 1);
lean_ctor_set(v___x_780_, 0, v_a_768_);
v___x_784_ = v___x_780_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_768_);
v___x_784_ = v_reuseFailAlloc_789_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_782_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_787_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
v___y_773_ = v___x_788_;
goto v___jp_772_;
}
}
}
else
{
v___y_773_ = v___x_778_;
goto v___jp_772_;
}
}
else
{
lean_dec_ref(v___y_776_);
v___y_773_ = v___y_775_;
goto v___jp_772_;
}
}
v___jp_792_:
{
if (lean_obj_tag(v___y_793_) == 0)
{
lean_dec_ref_known(v___y_793_, 1);
v_a_762_ = v___x_771_;
goto v___jp_761_;
}
else
{
return v___y_793_;
}
}
v___jp_794_:
{
if (v___y_797_ == 0)
{
lean_object* v___x_798_; 
lean_dec_ref(v___y_796_);
v___x_798_ = l_Lean_Meta_SavedState_restore___redArg(v___y_795_, v___y_757_, v___y_759_);
lean_dec_ref(v___y_795_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_810_; 
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_810_ == 0)
{
lean_object* v_unused_811_; 
v_unused_811_ = lean_ctor_get(v___x_798_, 0);
lean_dec(v_unused_811_);
v___x_800_ = v___x_798_;
v_isShared_801_ = v_isSharedCheck_810_;
goto v_resetjp_799_;
}
else
{
lean_dec(v___x_798_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_810_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; lean_object* v___x_804_; 
v___x_802_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1);
lean_inc(v_a_768_);
if (v_isShared_801_ == 0)
{
lean_ctor_set_tag(v___x_800_, 1);
lean_ctor_set(v___x_800_, 0, v_a_768_);
v___x_804_ = v___x_800_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_a_768_);
v___x_804_ = v_reuseFailAlloc_809_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_802_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
v___x_806_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_805_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_807_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
v___y_793_ = v___x_808_;
goto v___jp_792_;
}
}
}
else
{
v___y_793_ = v___x_798_;
goto v___jp_792_;
}
}
else
{
lean_dec_ref(v___y_795_);
v___y_793_ = v___y_796_;
goto v___jp_792_;
}
}
v___jp_812_:
{
if (lean_obj_tag(v___y_813_) == 0)
{
lean_dec_ref_known(v___y_813_, 1);
v_a_762_ = v___x_771_;
goto v___jp_761_;
}
else
{
return v___y_813_;
}
}
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
v_a_920_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_769_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_769_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
v___jp_761_:
{
size_t v___x_763_; size_t v___x_764_; 
v___x_763_ = ((size_t)1ULL);
v___x_764_ = lean_usize_add(v_i_754_, v___x_763_);
v_i_754_ = v___x_764_;
v_b_755_ = v_a_762_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___boxed(lean_object* v_as_928_, lean_object* v_sz_929_, lean_object* v_i_930_, lean_object* v_b_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
size_t v_sz_boxed_937_; size_t v_i_boxed_938_; lean_object* v_res_939_; 
v_sz_boxed_937_ = lean_unbox_usize(v_sz_929_);
lean_dec(v_sz_929_);
v_i_boxed_938_ = lean_unbox_usize(v_i_930_);
lean_dec(v_i_930_);
v_res_939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v_as_928_, v_sz_boxed_937_, v_i_boxed_938_, v_b_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec_ref(v_as_928_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
if (lean_obj_tag(v_a_940_) == 0)
{
lean_object* v___x_942_; 
v___x_942_ = l_List_reverse___redArg(v_a_941_);
return v___x_942_;
}
else
{
lean_object* v_head_943_; lean_object* v_tail_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_953_; 
v_head_943_ = lean_ctor_get(v_a_940_, 0);
v_tail_944_ = lean_ctor_get(v_a_940_, 1);
v_isSharedCheck_953_ = !lean_is_exclusive(v_a_940_);
if (v_isSharedCheck_953_ == 0)
{
v___x_946_ = v_a_940_;
v_isShared_947_ = v_isSharedCheck_953_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_tail_944_);
lean_inc(v_head_943_);
lean_dec(v_a_940_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_953_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_948_; lean_object* v___x_950_; 
v___x_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_948_, 0, v_head_943_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 1, v_a_941_);
lean_ctor_set(v___x_946_, 0, v___x_948_);
v___x_950_ = v___x_946_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_a_941_);
v___x_950_ = v_reuseFailAlloc_952_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
v_a_940_ = v_tail_944_;
v_a_941_ = v___x_950_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__1(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__0));
v___x_956_ = l_Lean_stringToMessageData(v___x_955_);
return v___x_956_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__3(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__2));
v___x_959_ = l_Lean_stringToMessageData(v___x_958_);
return v___x_959_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__5(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__4));
v___x_962_ = l_Lean_stringToMessageData(v___x_961_);
return v___x_962_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__7(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__6));
v___x_965_ = l_Lean_stringToMessageData(v___x_964_);
return v___x_965_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__9(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__8));
v___x_968_ = l_Lean_stringToMessageData(v___x_967_);
return v___x_968_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__12(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__11));
v___x_973_ = l_Lean_stringToMessageData(v___x_972_);
return v___x_973_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__14(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__13));
v___x_976_ = l_Lean_stringToMessageData(v___x_975_);
return v___x_976_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__16(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__15));
v___x_979_ = l_Lean_stringToMessageData(v___x_978_);
return v___x_979_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__22(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__21));
v___x_988_ = l_Lean_stringToMessageData(v___x_987_);
return v___x_988_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__24(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__23));
v___x_991_ = l_Lean_stringToMessageData(v___x_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2(uint8_t v___x_992_, lean_object* v___x_993_, lean_object* v_fst_994_, lean_object* v___x_995_, lean_object* v_e_996_, uint8_t v___y_997_, lean_object* v_snd_998_, lean_object* v_____r_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___y_1006_; lean_object* v_proof_1007_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; uint8_t v___y_1032_; lean_object* v___x_1044_; lean_object* v___y_1046_; uint8_t v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; uint8_t v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v_a_1068_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; uint8_t v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; size_t v_sz_1108_; size_t v___x_1109_; lean_object* v___x_1110_; lean_object* v___y_1112_; uint8_t v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; uint8_t v_fst_1139_; lean_object* v_fst_1140_; lean_object* v_snd_1141_; lean_object* v___x_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1044_ = l_Lean_mkAppN(v___x_993_, v_fst_994_);
v_sz_1108_ = lean_array_size(v_fst_994_);
v___x_1109_ = ((size_t)0ULL);
v___x_1110_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_1108_, v___x_1109_, v_fst_994_);
v___x_1175_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1176_ = lean_unsigned_to_nat(4u);
v___x_1177_ = l_Lean_Expr_isAppOfArity(v_snd_998_, v___x_1175_, v___x_1176_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1179_; uint8_t v___x_1180_; 
v___x_1178_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1179_ = lean_unsigned_to_nat(3u);
v___x_1180_ = l_Lean_Expr_isAppOfArity(v_snd_998_, v___x_1178_, v___x_1179_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_dec_ref(v___x_1110_);
lean_dec_ref(v___x_1044_);
lean_dec_ref(v_e_996_);
v___x_1181_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1182_ = l_Lean_MessageData_ofConstName(v___x_995_, v___y_997_);
v___x_1183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1181_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1183_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1185_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1186_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1186_);
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
else
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = l_Lean_Expr_appFn_x21(v_snd_998_);
v___x_1196_ = l_Lean_Expr_appArg_x21(v___x_1195_);
lean_dec_ref(v___x_1195_);
v___x_1197_ = l_Lean_Expr_appArg_x21(v_snd_998_);
v_fst_1139_ = v___y_997_;
v_fst_1140_ = v___x_1196_;
v_snd_1141_ = v___x_1197_;
goto v___jp_1138_;
}
}
else
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1198_ = l_Lean_Expr_appFn_x21(v_snd_998_);
v___x_1199_ = l_Lean_Expr_appFn_x21(v___x_1198_);
lean_dec_ref(v___x_1198_);
v___x_1200_ = l_Lean_Expr_appArg_x21(v___x_1199_);
lean_dec_ref(v___x_1199_);
v___x_1201_ = l_Lean_Expr_appArg_x21(v_snd_998_);
v_fst_1139_ = v___x_992_;
v_fst_1140_ = v___x_1200_;
v_snd_1141_ = v___x_1201_;
goto v___jp_1138_;
}
v___jp_1005_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1008_, 0, v_proof_1007_);
v___x_1009_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1009_, 0, v___y_1006_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
lean_ctor_set_uint8(v___x_1009_, sizeof(void*)*2, v___x_992_);
v___x_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
return v___x_1010_;
}
v___jp_1011_:
{
if (lean_obj_tag(v___y_1013_) == 0)
{
lean_object* v_a_1014_; 
v_a_1014_ = lean_ctor_get(v___y_1013_, 0);
lean_inc(v_a_1014_);
lean_dec_ref_known(v___y_1013_, 1);
v___y_1006_ = v___y_1012_;
v_proof_1007_ = v_a_1014_;
goto v___jp_1005_;
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec_ref(v___y_1012_);
v_a_1015_ = lean_ctor_get(v___y_1013_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___y_1013_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___y_1013_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___y_1013_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
v___jp_1023_:
{
if (v___y_1032_ == 0)
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
lean_dec_ref(v___y_1026_);
v___x_1033_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1034_ = l_Lean_MessageData_ofExpr(v___y_1025_);
v___x_1035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1035_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = l_Lean_Exception_toMessageData(v___y_1028_);
v___x_1039_ = l_Lean_indentD(v___x_1038_);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1037_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1042_, v___y_1029_, v___y_1027_, v___y_1024_, v___y_1031_);
v___y_1012_ = v___y_1030_;
v___y_1013_ = v___x_1043_;
goto v___jp_1011_;
}
else
{
lean_dec_ref(v___y_1028_);
lean_dec_ref(v___y_1025_);
v___y_1012_ = v___y_1030_;
v___y_1013_ = v___y_1026_;
goto v___jp_1011_;
}
}
v___jp_1045_:
{
lean_object* v___x_1052_; lean_object* v_a_1053_; lean_object* v___x_1054_; 
v___x_1052_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_1046_, v___y_1049_);
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref(v___x_1052_);
v___x_1054_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___x_1044_, v___y_1049_);
if (v___y_1047_ == 0)
{
lean_object* v_a_1055_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1055_);
lean_dec_ref(v___x_1054_);
v___y_1006_ = v_a_1053_;
v_proof_1007_ = v_a_1055_;
goto v___jp_1005_;
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1057_; 
v_a_1056_ = lean_ctor_get(v___x_1054_, 0);
lean_inc_n(v_a_1056_, 2);
lean_dec_ref(v___x_1054_);
v___x_1057_ = l_Lean_Meta_mkEqOfHEq(v_a_1056_, v___x_992_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_dec(v_a_1056_);
v___y_1012_ = v_a_1053_;
v___y_1013_ = v___x_1057_;
goto v___jp_1011_;
}
else
{
lean_object* v_a_1058_; uint8_t v___x_1059_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1058_);
v___x_1059_ = l_Lean_Exception_isInterrupt(v_a_1058_);
if (v___x_1059_ == 0)
{
uint8_t v___x_1060_; 
lean_inc(v_a_1058_);
v___x_1060_ = l_Lean_Exception_isRuntime(v_a_1058_);
v___y_1024_ = v___y_1050_;
v___y_1025_ = v_a_1056_;
v___y_1026_ = v___x_1057_;
v___y_1027_ = v___y_1049_;
v___y_1028_ = v_a_1058_;
v___y_1029_ = v___y_1048_;
v___y_1030_ = v_a_1053_;
v___y_1031_ = v___y_1051_;
v___y_1032_ = v___x_1060_;
goto v___jp_1023_;
}
else
{
v___y_1024_ = v___y_1050_;
v___y_1025_ = v_a_1056_;
v___y_1026_ = v___x_1057_;
v___y_1027_ = v___y_1049_;
v___y_1028_ = v_a_1058_;
v___y_1029_ = v___y_1048_;
v___y_1030_ = v_a_1053_;
v___y_1031_ = v___y_1051_;
v___y_1032_ = v___x_1059_;
goto v___jp_1023_;
}
}
}
}
v___jp_1061_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1069_ = lean_array_get_size(v_a_1068_);
v___x_1070_ = lean_unsigned_to_nat(0u);
v___x_1071_ = lean_nat_dec_eq(v___x_1069_, v___x_1070_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
lean_dec_ref(v___y_1063_);
lean_dec_ref(v___x_1044_);
v___x_1072_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1073_ = l_Lean_MessageData_ofConstName(v___x_995_, v___x_1071_);
v___x_1074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = lean_array_to_list(v_a_1068_);
v___x_1078_ = lean_box(0);
v___x_1079_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_1077_, v___x_1078_);
v___x_1080_ = l_Lean_MessageData_ofList(v___x_1079_);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1076_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1081_, v___y_1064_, v___y_1066_, v___y_1062_, v___y_1067_);
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1082_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
else
{
lean_dec_ref(v_a_1068_);
lean_dec(v___x_995_);
v___y_1046_ = v___y_1063_;
v___y_1047_ = v___y_1065_;
v___y_1048_ = v___y_1064_;
v___y_1049_ = v___y_1066_;
v___y_1050_ = v___y_1062_;
v___y_1051_ = v___y_1067_;
goto v___jp_1045_;
}
}
v___jp_1091_:
{
if (lean_obj_tag(v___y_1098_) == 0)
{
lean_object* v_a_1099_; 
v_a_1099_ = lean_ctor_get(v___y_1098_, 0);
lean_inc(v_a_1099_);
lean_dec_ref_known(v___y_1098_, 1);
v___y_1062_ = v___y_1092_;
v___y_1063_ = v___y_1093_;
v___y_1064_ = v___y_1094_;
v___y_1065_ = v___y_1095_;
v___y_1066_ = v___y_1096_;
v___y_1067_ = v___y_1097_;
v_a_1068_ = v_a_1099_;
goto v___jp_1061_;
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec_ref(v___y_1093_);
lean_dec_ref(v___x_1044_);
lean_dec(v___x_995_);
v_a_1100_ = lean_ctor_get(v___y_1098_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___y_1098_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___y_1098_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___y_1098_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
v___jp_1111_:
{
lean_object* v___x_1118_; size_t v_sz_1119_; lean_object* v___x_1120_; 
v___x_1118_ = lean_box(0);
v_sz_1119_ = lean_array_size(v___x_1110_);
v___x_1120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1110_, v_sz_1119_, v___x_1109_, v___x_1118_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
lean_dec_ref_known(v___x_1120_, 1);
v___x_1121_ = lean_unsigned_to_nat(0u);
v___x_1122_ = lean_array_get_size(v___x_1110_);
v___x_1123_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1124_ = lean_nat_dec_lt(v___x_1121_, v___x_1122_);
if (v___x_1124_ == 0)
{
lean_dec_ref(v___x_1110_);
v___y_1062_ = v___y_1116_;
v___y_1063_ = v___y_1112_;
v___y_1064_ = v___y_1114_;
v___y_1065_ = v___y_1113_;
v___y_1066_ = v___y_1115_;
v___y_1067_ = v___y_1117_;
v_a_1068_ = v___x_1123_;
goto v___jp_1061_;
}
else
{
uint8_t v___x_1125_; 
v___x_1125_ = lean_nat_dec_le(v___x_1122_, v___x_1122_);
if (v___x_1125_ == 0)
{
if (v___x_1124_ == 0)
{
lean_dec_ref(v___x_1110_);
v___y_1062_ = v___y_1116_;
v___y_1063_ = v___y_1112_;
v___y_1064_ = v___y_1114_;
v___y_1065_ = v___y_1113_;
v___y_1066_ = v___y_1115_;
v___y_1067_ = v___y_1117_;
v_a_1068_ = v___x_1123_;
goto v___jp_1061_;
}
else
{
size_t v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = lean_usize_of_nat(v___x_1122_);
v___x_1127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1110_, v___x_1109_, v___x_1126_, v___x_1123_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec_ref(v___x_1110_);
v___y_1092_ = v___y_1116_;
v___y_1093_ = v___y_1112_;
v___y_1094_ = v___y_1114_;
v___y_1095_ = v___y_1113_;
v___y_1096_ = v___y_1115_;
v___y_1097_ = v___y_1117_;
v___y_1098_ = v___x_1127_;
goto v___jp_1091_;
}
}
else
{
size_t v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_usize_of_nat(v___x_1122_);
v___x_1129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1110_, v___x_1109_, v___x_1128_, v___x_1123_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec_ref(v___x_1110_);
v___y_1092_ = v___y_1116_;
v___y_1093_ = v___y_1112_;
v___y_1094_ = v___y_1114_;
v___y_1095_ = v___y_1113_;
v___y_1096_ = v___y_1115_;
v___y_1097_ = v___y_1117_;
v___y_1098_ = v___x_1129_;
goto v___jp_1091_;
}
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec_ref(v___y_1112_);
lean_dec_ref(v___x_1110_);
lean_dec_ref(v___x_1044_);
lean_dec(v___x_995_);
v_a_1130_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1120_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1120_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
v___jp_1138_:
{
lean_object* v___x_1142_; 
lean_inc_ref(v_fst_1140_);
lean_inc_ref(v_e_996_);
v___x_1142_ = l_Lean_Meta_isExprDefEq(v_e_996_, v_fst_1140_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; uint8_t v___x_1144_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref_known(v___x_1142_, 1);
v___x_1144_ = lean_unbox(v_a_1143_);
lean_dec(v_a_1143_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_dec_ref(v_snd_1141_);
lean_dec_ref(v___x_1110_);
lean_dec_ref(v___x_1044_);
v___x_1145_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1146_ = l_Lean_MessageData_ofExpr(v_fst_1140_);
v___x_1147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1145_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1147_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = l_Lean_MessageData_ofConstName(v___x_995_, v___y_997_);
v___x_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1149_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1151_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = l_Lean_MessageData_ofExpr(v_e_996_);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1157_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1158_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1158_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
else
{
lean_dec_ref(v_fst_1140_);
lean_dec_ref(v_e_996_);
v___y_1112_ = v_snd_1141_;
v___y_1113_ = v_fst_1139_;
v___y_1114_ = v___y_1000_;
v___y_1115_ = v___y_1001_;
v___y_1116_ = v___y_1002_;
v___y_1117_ = v___y_1003_;
goto v___jp_1111_;
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
lean_dec_ref(v_snd_1141_);
lean_dec_ref(v_fst_1140_);
lean_dec_ref(v___x_1110_);
lean_dec_ref(v___x_1044_);
lean_dec_ref(v_e_996_);
lean_dec(v___x_995_);
v_a_1167_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1142_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1142_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2___boxed(lean_object* v___x_1202_, lean_object* v___x_1203_, lean_object* v_fst_1204_, lean_object* v___x_1205_, lean_object* v_e_1206_, lean_object* v___y_1207_, lean_object* v_snd_1208_, lean_object* v_____r_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
uint8_t v___x_84666__boxed_1215_; uint8_t v___y_84670__boxed_1216_; lean_object* v_res_1217_; 
v___x_84666__boxed_1215_ = lean_unbox(v___x_1202_);
v___y_84670__boxed_1216_ = lean_unbox(v___y_1207_);
v_res_1217_ = l_Lean_Meta_rwMatcher___lam__2(v___x_84666__boxed_1215_, v___x_1203_, v_fst_1204_, v___x_1205_, v_e_1206_, v___y_84670__boxed_1216_, v_snd_1208_, v_____r_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec_ref(v_snd_1208_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3(uint8_t v___x_1218_, lean_object* v___x_1219_, lean_object* v_fst_1220_, lean_object* v___x_1221_, lean_object* v_e_1222_, uint8_t v___y_1223_, lean_object* v_snd_1224_, lean_object* v_____r_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v___y_1232_; lean_object* v_proof_1233_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; uint8_t v___y_1258_; lean_object* v___x_1270_; lean_object* v___y_1272_; uint8_t v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; uint8_t v___y_1292_; lean_object* v___y_1293_; lean_object* v_a_1294_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; uint8_t v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; size_t v_sz_1334_; size_t v___x_1335_; lean_object* v___x_1336_; lean_object* v___y_1338_; uint8_t v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; uint8_t v_fst_1365_; lean_object* v_fst_1366_; lean_object* v_snd_1367_; lean_object* v___x_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v___x_1270_ = l_Lean_mkAppN(v___x_1219_, v_fst_1220_);
v_sz_1334_ = lean_array_size(v_fst_1220_);
v___x_1335_ = ((size_t)0ULL);
v___x_1336_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_1334_, v___x_1335_, v_fst_1220_);
v___x_1401_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1402_ = lean_unsigned_to_nat(4u);
v___x_1403_ = l_Lean_Expr_isAppOfArity(v_snd_1224_, v___x_1401_, v___x_1402_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v___x_1404_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1405_ = lean_unsigned_to_nat(3u);
v___x_1406_ = l_Lean_Expr_isAppOfArity(v_snd_1224_, v___x_1404_, v___x_1405_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec_ref(v___x_1336_);
lean_dec_ref(v___x_1270_);
lean_dec_ref(v_e_1222_);
v___x_1407_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1408_ = l_Lean_MessageData_ofConstName(v___x_1221_, v___y_1223_);
v___x_1409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1407_);
lean_ctor_set(v___x_1409_, 1, v___x_1408_);
v___x_1410_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1409_);
lean_ctor_set(v___x_1411_, 1, v___x_1410_);
v___x_1412_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1411_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1412_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1412_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
else
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1421_ = l_Lean_Expr_appFn_x21(v_snd_1224_);
v___x_1422_ = l_Lean_Expr_appArg_x21(v___x_1421_);
lean_dec_ref(v___x_1421_);
v___x_1423_ = l_Lean_Expr_appArg_x21(v_snd_1224_);
v_fst_1365_ = v___y_1223_;
v_fst_1366_ = v___x_1422_;
v_snd_1367_ = v___x_1423_;
goto v___jp_1364_;
}
}
else
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1424_ = l_Lean_Expr_appFn_x21(v_snd_1224_);
v___x_1425_ = l_Lean_Expr_appFn_x21(v___x_1424_);
lean_dec_ref(v___x_1424_);
v___x_1426_ = l_Lean_Expr_appArg_x21(v___x_1425_);
lean_dec_ref(v___x_1425_);
v___x_1427_ = l_Lean_Expr_appArg_x21(v_snd_1224_);
v_fst_1365_ = v___x_1218_;
v_fst_1366_ = v___x_1426_;
v_snd_1367_ = v___x_1427_;
goto v___jp_1364_;
}
v___jp_1231_:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1234_, 0, v_proof_1233_);
v___x_1235_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1235_, 0, v___y_1232_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
lean_ctor_set_uint8(v___x_1235_, sizeof(void*)*2, v___x_1218_);
v___x_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
return v___x_1236_;
}
v___jp_1237_:
{
if (lean_obj_tag(v___y_1239_) == 0)
{
lean_object* v_a_1240_; 
v_a_1240_ = lean_ctor_get(v___y_1239_, 0);
lean_inc(v_a_1240_);
lean_dec_ref_known(v___y_1239_, 1);
v___y_1232_ = v___y_1238_;
v_proof_1233_ = v_a_1240_;
goto v___jp_1231_;
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
lean_dec_ref(v___y_1238_);
v_a_1241_ = lean_ctor_get(v___y_1239_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___y_1239_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___y_1239_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___y_1239_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
v___jp_1249_:
{
if (v___y_1258_ == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
lean_dec_ref(v___y_1251_);
v___x_1259_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1260_ = l_Lean_MessageData_ofExpr(v___y_1250_);
v___x_1261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1259_);
lean_ctor_set(v___x_1261_, 1, v___x_1260_);
v___x_1262_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1261_);
lean_ctor_set(v___x_1263_, 1, v___x_1262_);
v___x_1264_ = l_Lean_Exception_toMessageData(v___y_1254_);
v___x_1265_ = l_Lean_indentD(v___x_1264_);
v___x_1266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1263_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1266_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
v___x_1269_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1268_, v___y_1256_, v___y_1257_, v___y_1253_, v___y_1255_);
v___y_1238_ = v___y_1252_;
v___y_1239_ = v___x_1269_;
goto v___jp_1237_;
}
else
{
lean_dec_ref(v___y_1254_);
lean_dec_ref(v___y_1250_);
v___y_1238_ = v___y_1252_;
v___y_1239_ = v___y_1251_;
goto v___jp_1237_;
}
}
v___jp_1271_:
{
lean_object* v___x_1278_; lean_object* v_a_1279_; lean_object* v___x_1280_; 
v___x_1278_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_1272_, v___y_1275_);
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref(v___x_1278_);
v___x_1280_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___x_1270_, v___y_1275_);
if (v___y_1273_ == 0)
{
lean_object* v_a_1281_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
lean_dec_ref(v___x_1280_);
v___y_1232_ = v_a_1279_;
v_proof_1233_ = v_a_1281_;
goto v___jp_1231_;
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1283_; 
v_a_1282_ = lean_ctor_get(v___x_1280_, 0);
lean_inc_n(v_a_1282_, 2);
lean_dec_ref(v___x_1280_);
v___x_1283_ = l_Lean_Meta_mkEqOfHEq(v_a_1282_, v___x_1218_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_dec(v_a_1282_);
v___y_1238_ = v_a_1279_;
v___y_1239_ = v___x_1283_;
goto v___jp_1237_;
}
else
{
lean_object* v_a_1284_; uint8_t v___x_1285_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
v___x_1285_ = l_Lean_Exception_isInterrupt(v_a_1284_);
if (v___x_1285_ == 0)
{
uint8_t v___x_1286_; 
lean_inc(v_a_1284_);
v___x_1286_ = l_Lean_Exception_isRuntime(v_a_1284_);
v___y_1250_ = v_a_1282_;
v___y_1251_ = v___x_1283_;
v___y_1252_ = v_a_1279_;
v___y_1253_ = v___y_1276_;
v___y_1254_ = v_a_1284_;
v___y_1255_ = v___y_1277_;
v___y_1256_ = v___y_1274_;
v___y_1257_ = v___y_1275_;
v___y_1258_ = v___x_1286_;
goto v___jp_1249_;
}
else
{
v___y_1250_ = v_a_1282_;
v___y_1251_ = v___x_1283_;
v___y_1252_ = v_a_1279_;
v___y_1253_ = v___y_1276_;
v___y_1254_ = v_a_1284_;
v___y_1255_ = v___y_1277_;
v___y_1256_ = v___y_1274_;
v___y_1257_ = v___y_1275_;
v___y_1258_ = v___x_1285_;
goto v___jp_1249_;
}
}
}
}
v___jp_1287_:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
v___x_1295_ = lean_array_get_size(v_a_1294_);
v___x_1296_ = lean_unsigned_to_nat(0u);
v___x_1297_ = lean_nat_dec_eq(v___x_1295_, v___x_1296_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_dec_ref(v___y_1289_);
lean_dec_ref(v___x_1270_);
v___x_1298_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1299_ = l_Lean_MessageData_ofConstName(v___x_1221_, v___x_1297_);
v___x_1300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1298_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
v___x_1301_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1300_);
lean_ctor_set(v___x_1302_, 1, v___x_1301_);
v___x_1303_ = lean_array_to_list(v_a_1294_);
v___x_1304_ = lean_box(0);
v___x_1305_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_1303_, v___x_1304_);
v___x_1306_ = l_Lean_MessageData_ofList(v___x_1305_);
v___x_1307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1302_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
v___x_1308_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1307_, v___y_1290_, v___y_1288_, v___y_1291_, v___y_1293_);
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1308_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1308_);
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
else
{
lean_dec_ref(v_a_1294_);
lean_dec(v___x_1221_);
v___y_1272_ = v___y_1289_;
v___y_1273_ = v___y_1292_;
v___y_1274_ = v___y_1290_;
v___y_1275_ = v___y_1288_;
v___y_1276_ = v___y_1291_;
v___y_1277_ = v___y_1293_;
goto v___jp_1271_;
}
}
v___jp_1317_:
{
if (lean_obj_tag(v___y_1324_) == 0)
{
lean_object* v_a_1325_; 
v_a_1325_ = lean_ctor_get(v___y_1324_, 0);
lean_inc(v_a_1325_);
lean_dec_ref_known(v___y_1324_, 1);
v___y_1288_ = v___y_1318_;
v___y_1289_ = v___y_1320_;
v___y_1290_ = v___y_1319_;
v___y_1291_ = v___y_1321_;
v___y_1292_ = v___y_1322_;
v___y_1293_ = v___y_1323_;
v_a_1294_ = v_a_1325_;
goto v___jp_1287_;
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec_ref(v___y_1320_);
lean_dec_ref(v___x_1270_);
lean_dec(v___x_1221_);
v_a_1326_ = lean_ctor_get(v___y_1324_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___y_1324_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___y_1324_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___y_1324_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
v___jp_1337_:
{
lean_object* v___x_1344_; size_t v_sz_1345_; lean_object* v___x_1346_; 
v___x_1344_ = lean_box(0);
v_sz_1345_ = lean_array_size(v___x_1336_);
v___x_1346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1336_, v_sz_1345_, v___x_1335_, v___x_1344_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; uint8_t v___x_1350_; 
lean_dec_ref_known(v___x_1346_, 1);
v___x_1347_ = lean_unsigned_to_nat(0u);
v___x_1348_ = lean_array_get_size(v___x_1336_);
v___x_1349_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1350_ = lean_nat_dec_lt(v___x_1347_, v___x_1348_);
if (v___x_1350_ == 0)
{
lean_dec_ref(v___x_1336_);
v___y_1288_ = v___y_1341_;
v___y_1289_ = v___y_1338_;
v___y_1290_ = v___y_1340_;
v___y_1291_ = v___y_1342_;
v___y_1292_ = v___y_1339_;
v___y_1293_ = v___y_1343_;
v_a_1294_ = v___x_1349_;
goto v___jp_1287_;
}
else
{
uint8_t v___x_1351_; 
v___x_1351_ = lean_nat_dec_le(v___x_1348_, v___x_1348_);
if (v___x_1351_ == 0)
{
if (v___x_1350_ == 0)
{
lean_dec_ref(v___x_1336_);
v___y_1288_ = v___y_1341_;
v___y_1289_ = v___y_1338_;
v___y_1290_ = v___y_1340_;
v___y_1291_ = v___y_1342_;
v___y_1292_ = v___y_1339_;
v___y_1293_ = v___y_1343_;
v_a_1294_ = v___x_1349_;
goto v___jp_1287_;
}
else
{
size_t v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = lean_usize_of_nat(v___x_1348_);
v___x_1353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1336_, v___x_1335_, v___x_1352_, v___x_1349_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
lean_dec_ref(v___x_1336_);
v___y_1318_ = v___y_1341_;
v___y_1319_ = v___y_1340_;
v___y_1320_ = v___y_1338_;
v___y_1321_ = v___y_1342_;
v___y_1322_ = v___y_1339_;
v___y_1323_ = v___y_1343_;
v___y_1324_ = v___x_1353_;
goto v___jp_1317_;
}
}
else
{
size_t v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = lean_usize_of_nat(v___x_1348_);
v___x_1355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1336_, v___x_1335_, v___x_1354_, v___x_1349_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
lean_dec_ref(v___x_1336_);
v___y_1318_ = v___y_1341_;
v___y_1319_ = v___y_1340_;
v___y_1320_ = v___y_1338_;
v___y_1321_ = v___y_1342_;
v___y_1322_ = v___y_1339_;
v___y_1323_ = v___y_1343_;
v___y_1324_ = v___x_1355_;
goto v___jp_1317_;
}
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
lean_dec_ref(v___y_1338_);
lean_dec_ref(v___x_1336_);
lean_dec_ref(v___x_1270_);
lean_dec(v___x_1221_);
v_a_1356_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1346_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1346_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
v___jp_1364_:
{
lean_object* v___x_1368_; 
lean_inc_ref(v_fst_1366_);
lean_inc_ref(v_e_1222_);
v___x_1368_ = l_Lean_Meta_isExprDefEq(v_e_1222_, v_fst_1366_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; uint8_t v___x_1370_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1369_);
lean_dec_ref_known(v___x_1368_, 1);
v___x_1370_ = lean_unbox(v_a_1369_);
lean_dec(v_a_1369_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_dec_ref(v_snd_1367_);
lean_dec_ref(v___x_1336_);
lean_dec_ref(v___x_1270_);
v___x_1371_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1372_ = l_Lean_MessageData_ofExpr(v_fst_1366_);
v___x_1373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1371_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
v___x_1374_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1373_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
v___x_1376_ = l_Lean_MessageData_ofConstName(v___x_1221_, v___y_1223_);
v___x_1377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1375_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
v___x_1378_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1377_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
v___x_1380_ = l_Lean_MessageData_ofExpr(v_e_1222_);
v___x_1381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1379_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_1383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1381_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
v___x_1384_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1383_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1384_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1384_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
else
{
lean_dec_ref(v_fst_1366_);
lean_dec_ref(v_e_1222_);
v___y_1338_ = v_snd_1367_;
v___y_1339_ = v_fst_1365_;
v___y_1340_ = v___y_1226_;
v___y_1341_ = v___y_1227_;
v___y_1342_ = v___y_1228_;
v___y_1343_ = v___y_1229_;
goto v___jp_1337_;
}
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
lean_dec_ref(v_snd_1367_);
lean_dec_ref(v_fst_1366_);
lean_dec_ref(v___x_1336_);
lean_dec_ref(v___x_1270_);
lean_dec_ref(v_e_1222_);
lean_dec(v___x_1221_);
v_a_1393_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1368_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1368_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3___boxed(lean_object* v___x_1428_, lean_object* v___x_1429_, lean_object* v_fst_1430_, lean_object* v___x_1431_, lean_object* v_e_1432_, lean_object* v___y_1433_, lean_object* v_snd_1434_, lean_object* v_____r_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
uint8_t v___x_85176__boxed_1441_; uint8_t v___y_85180__boxed_1442_; lean_object* v_res_1443_; 
v___x_85176__boxed_1441_ = lean_unbox(v___x_1428_);
v___y_85180__boxed_1442_ = lean_unbox(v___y_1433_);
v_res_1443_ = l_Lean_Meta_rwMatcher___lam__3(v___x_85176__boxed_1441_, v___x_1429_, v_fst_1430_, v___x_1431_, v_e_1432_, v___y_85180__boxed_1442_, v_snd_1434_, v_____r_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec_ref(v_snd_1434_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4(uint8_t v___x_1444_, lean_object* v___x_1445_, lean_object* v_fst_1446_, lean_object* v___x_1447_, lean_object* v_e_1448_, uint8_t v___y_1449_, lean_object* v_snd_1450_, lean_object* v_____r_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v___y_1458_; lean_object* v_proof_1459_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; uint8_t v___y_1484_; lean_object* v___x_1496_; lean_object* v___y_1498_; uint8_t v___y_1499_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1514_; uint8_t v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v_a_1520_; lean_object* v___y_1544_; lean_object* v___y_1545_; uint8_t v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; size_t v_sz_1560_; size_t v___x_1561_; lean_object* v___x_1562_; lean_object* v___y_1564_; uint8_t v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; uint8_t v_fst_1591_; lean_object* v_fst_1592_; lean_object* v_snd_1593_; lean_object* v___x_1627_; lean_object* v___x_1628_; uint8_t v___x_1629_; 
v___x_1496_ = l_Lean_mkAppN(v___x_1445_, v_fst_1446_);
v_sz_1560_ = lean_array_size(v_fst_1446_);
v___x_1561_ = ((size_t)0ULL);
v___x_1562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_1560_, v___x_1561_, v_fst_1446_);
v___x_1627_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1628_ = lean_unsigned_to_nat(4u);
v___x_1629_ = l_Lean_Expr_isAppOfArity(v_snd_1450_, v___x_1627_, v___x_1628_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1630_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1631_ = lean_unsigned_to_nat(3u);
v___x_1632_ = l_Lean_Expr_isAppOfArity(v_snd_1450_, v___x_1630_, v___x_1631_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
lean_dec_ref(v___x_1562_);
lean_dec_ref(v___x_1496_);
lean_dec_ref(v_e_1448_);
v___x_1633_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1634_ = l_Lean_MessageData_ofConstName(v___x_1447_, v___y_1449_);
v___x_1635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1635_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
v___x_1638_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1637_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1638_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1638_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
else
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1647_ = l_Lean_Expr_appFn_x21(v_snd_1450_);
v___x_1648_ = l_Lean_Expr_appArg_x21(v___x_1647_);
lean_dec_ref(v___x_1647_);
v___x_1649_ = l_Lean_Expr_appArg_x21(v_snd_1450_);
v_fst_1591_ = v___y_1449_;
v_fst_1592_ = v___x_1648_;
v_snd_1593_ = v___x_1649_;
goto v___jp_1590_;
}
}
else
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1650_ = l_Lean_Expr_appFn_x21(v_snd_1450_);
v___x_1651_ = l_Lean_Expr_appFn_x21(v___x_1650_);
lean_dec_ref(v___x_1650_);
v___x_1652_ = l_Lean_Expr_appArg_x21(v___x_1651_);
lean_dec_ref(v___x_1651_);
v___x_1653_ = l_Lean_Expr_appArg_x21(v_snd_1450_);
v_fst_1591_ = v___x_1444_;
v_fst_1592_ = v___x_1652_;
v_snd_1593_ = v___x_1653_;
goto v___jp_1590_;
}
v___jp_1457_:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1460_, 0, v_proof_1459_);
v___x_1461_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1461_, 0, v___y_1458_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
lean_ctor_set_uint8(v___x_1461_, sizeof(void*)*2, v___x_1444_);
v___x_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
return v___x_1462_;
}
v___jp_1463_:
{
if (lean_obj_tag(v___y_1465_) == 0)
{
lean_object* v_a_1466_; 
v_a_1466_ = lean_ctor_get(v___y_1465_, 0);
lean_inc(v_a_1466_);
lean_dec_ref_known(v___y_1465_, 1);
v___y_1458_ = v___y_1464_;
v_proof_1459_ = v_a_1466_;
goto v___jp_1457_;
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec_ref(v___y_1464_);
v_a_1467_ = lean_ctor_get(v___y_1465_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___y_1465_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___y_1465_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___y_1465_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
v___jp_1475_:
{
if (v___y_1484_ == 0)
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
lean_dec_ref(v___y_1483_);
v___x_1485_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1486_ = l_Lean_MessageData_ofExpr(v___y_1479_);
v___x_1487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1485_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
v___x_1488_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1487_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = l_Lean_Exception_toMessageData(v___y_1476_);
v___x_1491_ = l_Lean_indentD(v___x_1490_);
v___x_1492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1489_);
lean_ctor_set(v___x_1492_, 1, v___x_1491_);
v___x_1493_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1492_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
v___x_1495_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1494_, v___y_1480_, v___y_1478_, v___y_1482_, v___y_1481_);
v___y_1464_ = v___y_1477_;
v___y_1465_ = v___x_1495_;
goto v___jp_1463_;
}
else
{
lean_dec_ref(v___y_1479_);
lean_dec_ref(v___y_1476_);
v___y_1464_ = v___y_1477_;
v___y_1465_ = v___y_1483_;
goto v___jp_1463_;
}
}
v___jp_1497_:
{
lean_object* v___x_1504_; lean_object* v_a_1505_; lean_object* v___x_1506_; 
v___x_1504_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_1498_, v___y_1501_);
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_a_1505_);
lean_dec_ref(v___x_1504_);
v___x_1506_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___x_1496_, v___y_1501_);
if (v___y_1499_ == 0)
{
lean_object* v_a_1507_; 
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_a_1507_);
lean_dec_ref(v___x_1506_);
v___y_1458_ = v_a_1505_;
v_proof_1459_ = v_a_1507_;
goto v___jp_1457_;
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1509_; 
v_a_1508_ = lean_ctor_get(v___x_1506_, 0);
lean_inc_n(v_a_1508_, 2);
lean_dec_ref(v___x_1506_);
v___x_1509_ = l_Lean_Meta_mkEqOfHEq(v_a_1508_, v___x_1444_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_dec(v_a_1508_);
v___y_1464_ = v_a_1505_;
v___y_1465_ = v___x_1509_;
goto v___jp_1463_;
}
else
{
lean_object* v_a_1510_; uint8_t v___x_1511_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
v___x_1511_ = l_Lean_Exception_isInterrupt(v_a_1510_);
if (v___x_1511_ == 0)
{
uint8_t v___x_1512_; 
lean_inc(v_a_1510_);
v___x_1512_ = l_Lean_Exception_isRuntime(v_a_1510_);
v___y_1476_ = v_a_1510_;
v___y_1477_ = v_a_1505_;
v___y_1478_ = v___y_1501_;
v___y_1479_ = v_a_1508_;
v___y_1480_ = v___y_1500_;
v___y_1481_ = v___y_1503_;
v___y_1482_ = v___y_1502_;
v___y_1483_ = v___x_1509_;
v___y_1484_ = v___x_1512_;
goto v___jp_1475_;
}
else
{
v___y_1476_ = v_a_1510_;
v___y_1477_ = v_a_1505_;
v___y_1478_ = v___y_1501_;
v___y_1479_ = v_a_1508_;
v___y_1480_ = v___y_1500_;
v___y_1481_ = v___y_1503_;
v___y_1482_ = v___y_1502_;
v___y_1483_ = v___x_1509_;
v___y_1484_ = v___x_1511_;
goto v___jp_1475_;
}
}
}
}
v___jp_1513_:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v___x_1521_ = lean_array_get_size(v_a_1520_);
v___x_1522_ = lean_unsigned_to_nat(0u);
v___x_1523_ = lean_nat_dec_eq(v___x_1521_, v___x_1522_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
lean_dec_ref(v___y_1514_);
lean_dec_ref(v___x_1496_);
v___x_1524_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1525_ = l_Lean_MessageData_ofConstName(v___x_1447_, v___x_1523_);
v___x_1526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1524_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
v___x_1527_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1526_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
v___x_1529_ = lean_array_to_list(v_a_1520_);
v___x_1530_ = lean_box(0);
v___x_1531_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_1529_, v___x_1530_);
v___x_1532_ = l_Lean_MessageData_ofList(v___x_1531_);
v___x_1533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1528_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1533_, v___y_1518_, v___y_1516_, v___y_1517_, v___y_1519_);
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1534_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1534_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
else
{
lean_dec_ref(v_a_1520_);
lean_dec(v___x_1447_);
v___y_1498_ = v___y_1514_;
v___y_1499_ = v___y_1515_;
v___y_1500_ = v___y_1518_;
v___y_1501_ = v___y_1516_;
v___y_1502_ = v___y_1517_;
v___y_1503_ = v___y_1519_;
goto v___jp_1497_;
}
}
v___jp_1543_:
{
if (lean_obj_tag(v___y_1550_) == 0)
{
lean_object* v_a_1551_; 
v_a_1551_ = lean_ctor_get(v___y_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref_known(v___y_1550_, 1);
v___y_1514_ = v___y_1544_;
v___y_1515_ = v___y_1546_;
v___y_1516_ = v___y_1545_;
v___y_1517_ = v___y_1547_;
v___y_1518_ = v___y_1548_;
v___y_1519_ = v___y_1549_;
v_a_1520_ = v_a_1551_;
goto v___jp_1513_;
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
lean_dec_ref(v___y_1544_);
lean_dec_ref(v___x_1496_);
lean_dec(v___x_1447_);
v_a_1552_ = lean_ctor_get(v___y_1550_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___y_1550_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___y_1550_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___y_1550_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
v___jp_1563_:
{
lean_object* v___x_1570_; size_t v_sz_1571_; lean_object* v___x_1572_; 
v___x_1570_ = lean_box(0);
v_sz_1571_ = lean_array_size(v___x_1562_);
v___x_1572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1562_, v_sz_1571_, v___x_1561_, v___x_1570_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; uint8_t v___x_1576_; 
lean_dec_ref_known(v___x_1572_, 1);
v___x_1573_ = lean_unsigned_to_nat(0u);
v___x_1574_ = lean_array_get_size(v___x_1562_);
v___x_1575_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1576_ = lean_nat_dec_lt(v___x_1573_, v___x_1574_);
if (v___x_1576_ == 0)
{
lean_dec_ref(v___x_1562_);
v___y_1514_ = v___y_1564_;
v___y_1515_ = v___y_1565_;
v___y_1516_ = v___y_1567_;
v___y_1517_ = v___y_1568_;
v___y_1518_ = v___y_1566_;
v___y_1519_ = v___y_1569_;
v_a_1520_ = v___x_1575_;
goto v___jp_1513_;
}
else
{
uint8_t v___x_1577_; 
v___x_1577_ = lean_nat_dec_le(v___x_1574_, v___x_1574_);
if (v___x_1577_ == 0)
{
if (v___x_1576_ == 0)
{
lean_dec_ref(v___x_1562_);
v___y_1514_ = v___y_1564_;
v___y_1515_ = v___y_1565_;
v___y_1516_ = v___y_1567_;
v___y_1517_ = v___y_1568_;
v___y_1518_ = v___y_1566_;
v___y_1519_ = v___y_1569_;
v_a_1520_ = v___x_1575_;
goto v___jp_1513_;
}
else
{
size_t v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = lean_usize_of_nat(v___x_1574_);
v___x_1579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1562_, v___x_1561_, v___x_1578_, v___x_1575_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
lean_dec_ref(v___x_1562_);
v___y_1544_ = v___y_1564_;
v___y_1545_ = v___y_1567_;
v___y_1546_ = v___y_1565_;
v___y_1547_ = v___y_1568_;
v___y_1548_ = v___y_1566_;
v___y_1549_ = v___y_1569_;
v___y_1550_ = v___x_1579_;
goto v___jp_1543_;
}
}
else
{
size_t v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = lean_usize_of_nat(v___x_1574_);
v___x_1581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1562_, v___x_1561_, v___x_1580_, v___x_1575_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
lean_dec_ref(v___x_1562_);
v___y_1544_ = v___y_1564_;
v___y_1545_ = v___y_1567_;
v___y_1546_ = v___y_1565_;
v___y_1547_ = v___y_1568_;
v___y_1548_ = v___y_1566_;
v___y_1549_ = v___y_1569_;
v___y_1550_ = v___x_1581_;
goto v___jp_1543_;
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec_ref(v___y_1564_);
lean_dec_ref(v___x_1562_);
lean_dec_ref(v___x_1496_);
lean_dec(v___x_1447_);
v_a_1582_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1572_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1572_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
v___jp_1590_:
{
lean_object* v___x_1594_; 
lean_inc_ref(v_fst_1592_);
lean_inc_ref(v_e_1448_);
v___x_1594_ = l_Lean_Meta_isExprDefEq(v_e_1448_, v_fst_1592_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; uint8_t v___x_1596_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1595_);
lean_dec_ref_known(v___x_1594_, 1);
v___x_1596_ = lean_unbox(v_a_1595_);
lean_dec(v_a_1595_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec_ref(v_snd_1593_);
lean_dec_ref(v___x_1562_);
lean_dec_ref(v___x_1496_);
v___x_1597_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1598_ = l_Lean_MessageData_ofExpr(v_fst_1592_);
v___x_1599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1597_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
v___x_1600_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1599_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
v___x_1602_ = l_Lean_MessageData_ofConstName(v___x_1447_, v___y_1449_);
v___x_1603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1601_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
v___x_1604_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1603_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
v___x_1606_ = l_Lean_MessageData_ofExpr(v_e_1448_);
v___x_1607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1605_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
v___x_1608_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_1609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1607_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
v___x_1610_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1609_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1610_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1610_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
else
{
lean_dec_ref(v_fst_1592_);
lean_dec_ref(v_e_1448_);
v___y_1564_ = v_snd_1593_;
v___y_1565_ = v_fst_1591_;
v___y_1566_ = v___y_1452_;
v___y_1567_ = v___y_1453_;
v___y_1568_ = v___y_1454_;
v___y_1569_ = v___y_1455_;
goto v___jp_1563_;
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_dec_ref(v_snd_1593_);
lean_dec_ref(v_fst_1592_);
lean_dec_ref(v___x_1562_);
lean_dec_ref(v___x_1496_);
lean_dec_ref(v_e_1448_);
lean_dec(v___x_1447_);
v_a_1619_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1594_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1594_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4___boxed(lean_object* v___x_1654_, lean_object* v___x_1655_, lean_object* v_fst_1656_, lean_object* v___x_1657_, lean_object* v_e_1658_, lean_object* v___y_1659_, lean_object* v_snd_1660_, lean_object* v_____r_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
uint8_t v___x_85661__boxed_1667_; uint8_t v___y_85665__boxed_1668_; lean_object* v_res_1669_; 
v___x_85661__boxed_1667_ = lean_unbox(v___x_1654_);
v___y_85665__boxed_1668_ = lean_unbox(v___y_1659_);
v_res_1669_ = l_Lean_Meta_rwMatcher___lam__4(v___x_85661__boxed_1667_, v___x_1655_, v_fst_1656_, v___x_1657_, v_e_1658_, v___y_85665__boxed_1668_, v_snd_1660_, v_____r_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec_ref(v_snd_1660_);
return v_res_1669_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1670_; double v___x_1671_; 
v___x_1670_ = lean_unsigned_to_nat(0u);
v___x_1671_ = lean_float_of_nat(v___x_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(lean_object* v_cls_1675_, lean_object* v_msg_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v_ref_1682_; lean_object* v___x_1683_; lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1728_; 
v_ref_1682_ = lean_ctor_get(v___y_1679_, 4);
v___x_1683_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1686_ = v___x_1683_;
v_isShared_1687_ = v_isSharedCheck_1728_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1683_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1728_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; lean_object* v_traceState_1689_; lean_object* v_env_1690_; lean_object* v_nextMacroScope_1691_; lean_object* v_ngen_1692_; lean_object* v_auxDeclNGen_1693_; lean_object* v_cache_1694_; lean_object* v_messages_1695_; lean_object* v_infoState_1696_; lean_object* v_snapshotTasks_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1727_; 
v___x_1688_ = lean_st_ref_take(v___y_1680_);
v_traceState_1689_ = lean_ctor_get(v___x_1688_, 4);
v_env_1690_ = lean_ctor_get(v___x_1688_, 0);
v_nextMacroScope_1691_ = lean_ctor_get(v___x_1688_, 1);
v_ngen_1692_ = lean_ctor_get(v___x_1688_, 2);
v_auxDeclNGen_1693_ = lean_ctor_get(v___x_1688_, 3);
v_cache_1694_ = lean_ctor_get(v___x_1688_, 5);
v_messages_1695_ = lean_ctor_get(v___x_1688_, 6);
v_infoState_1696_ = lean_ctor_get(v___x_1688_, 7);
v_snapshotTasks_1697_ = lean_ctor_get(v___x_1688_, 8);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1699_ = v___x_1688_;
v_isShared_1700_ = v_isSharedCheck_1727_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_snapshotTasks_1697_);
lean_inc(v_infoState_1696_);
lean_inc(v_messages_1695_);
lean_inc(v_cache_1694_);
lean_inc(v_traceState_1689_);
lean_inc(v_auxDeclNGen_1693_);
lean_inc(v_ngen_1692_);
lean_inc(v_nextMacroScope_1691_);
lean_inc(v_env_1690_);
lean_dec(v___x_1688_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1727_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
uint64_t v_tid_1701_; lean_object* v_traces_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1726_; 
v_tid_1701_ = lean_ctor_get_uint64(v_traceState_1689_, sizeof(void*)*1);
v_traces_1702_ = lean_ctor_get(v_traceState_1689_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v_traceState_1689_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1704_ = v_traceState_1689_;
v_isShared_1705_ = v_isSharedCheck_1726_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_traces_1702_);
lean_dec(v_traceState_1689_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1726_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1706_; double v___x_1707_; uint8_t v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1716_; 
v___x_1706_ = lean_box(0);
v___x_1707_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0);
v___x_1708_ = 0;
v___x_1709_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1));
v___x_1710_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1710_, 0, v_cls_1675_);
lean_ctor_set(v___x_1710_, 1, v___x_1706_);
lean_ctor_set(v___x_1710_, 2, v___x_1709_);
lean_ctor_set_float(v___x_1710_, sizeof(void*)*3, v___x_1707_);
lean_ctor_set_float(v___x_1710_, sizeof(void*)*3 + 8, v___x_1707_);
lean_ctor_set_uint8(v___x_1710_, sizeof(void*)*3 + 16, v___x_1708_);
v___x_1711_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__2));
v___x_1712_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1710_);
lean_ctor_set(v___x_1712_, 1, v_a_1684_);
lean_ctor_set(v___x_1712_, 2, v___x_1711_);
lean_inc(v_ref_1682_);
v___x_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1713_, 0, v_ref_1682_);
lean_ctor_set(v___x_1713_, 1, v___x_1712_);
v___x_1714_ = l_Lean_PersistentArray_push___redArg(v_traces_1702_, v___x_1713_);
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 0, v___x_1714_);
v___x_1716_ = v___x_1704_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1714_);
lean_ctor_set_uint64(v_reuseFailAlloc_1725_, sizeof(void*)*1, v_tid_1701_);
v___x_1716_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
lean_object* v___x_1718_; 
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 4, v___x_1716_);
v___x_1718_ = v___x_1699_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_env_1690_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_nextMacroScope_1691_);
lean_ctor_set(v_reuseFailAlloc_1724_, 2, v_ngen_1692_);
lean_ctor_set(v_reuseFailAlloc_1724_, 3, v_auxDeclNGen_1693_);
lean_ctor_set(v_reuseFailAlloc_1724_, 4, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1724_, 5, v_cache_1694_);
lean_ctor_set(v_reuseFailAlloc_1724_, 6, v_messages_1695_);
lean_ctor_set(v_reuseFailAlloc_1724_, 7, v_infoState_1696_);
lean_ctor_set(v_reuseFailAlloc_1724_, 8, v_snapshotTasks_1697_);
v___x_1718_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1722_; 
v___x_1719_ = lean_st_ref_put(v___y_1680_, v___x_1718_);
v___x_1720_ = lean_box(0);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v___x_1720_);
v___x_1722_ = v___x_1686_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1720_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___boxed(lean_object* v_cls_1729_, lean_object* v_msg_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v_cls_1729_, v_msg_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(lean_object* v_a_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Lean_Meta_reduceRecMatcher_x3f(v_a_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1757_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1746_ = v___x_1743_;
v_isShared_1747_ = v_isSharedCheck_1757_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1743_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1757_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
if (lean_obj_tag(v_a_1744_) == 1)
{
lean_object* v_val_1748_; lean_object* v___x_1749_; 
lean_del_object(v___x_1746_);
lean_dec_ref(v_a_1737_);
v_val_1748_ = lean_ctor_get(v_a_1744_, 0);
lean_inc(v_val_1748_);
lean_dec_ref_known(v_a_1744_, 1);
v___x_1749_ = l_Lean_Expr_headBeta(v_val_1748_);
v_a_1737_ = v___x_1749_;
goto _start;
}
else
{
lean_object* v___x_1751_; uint8_t v___x_1752_; 
lean_dec(v_a_1744_);
lean_inc_ref(v_a_1737_);
v___x_1751_ = l_Lean_Expr_headBeta(v_a_1737_);
v___x_1752_ = lean_expr_eqv(v_a_1737_, v___x_1751_);
if (v___x_1752_ == 0)
{
lean_del_object(v___x_1746_);
lean_dec_ref(v_a_1737_);
v_a_1737_ = v___x_1751_;
goto _start;
}
else
{
lean_object* v___x_1755_; 
lean_dec_ref(v___x_1751_);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 0, v_a_1737_);
v___x_1755_ = v___x_1746_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1737_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
lean_dec_ref(v_a_1737_);
v_a_1758_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1743_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1743_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg___boxed(lean_object* v_a_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(v_a_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(lean_object* v_opts_1773_, lean_object* v_opt_1774_){
_start:
{
lean_object* v_name_1775_; lean_object* v_defValue_1776_; lean_object* v_map_1777_; lean_object* v___x_1778_; 
v_name_1775_ = lean_ctor_get(v_opt_1774_, 0);
v_defValue_1776_ = lean_ctor_get(v_opt_1774_, 1);
v_map_1777_ = lean_ctor_get(v_opts_1773_, 0);
v___x_1778_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1777_, v_name_1775_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_inc(v_defValue_1776_);
return v_defValue_1776_;
}
else
{
lean_object* v_val_1779_; 
v_val_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_val_1779_);
lean_dec_ref_known(v___x_1778_, 1);
if (lean_obj_tag(v_val_1779_) == 3)
{
lean_object* v_v_1780_; 
v_v_1780_ = lean_ctor_get(v_val_1779_, 0);
lean_inc(v_v_1780_);
lean_dec_ref_known(v_val_1779_, 1);
return v_v_1780_;
}
else
{
lean_dec(v_val_1779_);
lean_inc(v_defValue_1776_);
return v_defValue_1776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16___boxed(lean_object* v_opts_1781_, lean_object* v_opt_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_1781_, v_opt_1782_);
lean_dec_ref(v_opt_1782_);
lean_dec_ref(v_opts_1781_);
return v_res_1783_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(lean_object* v_e_1784_){
_start:
{
if (lean_obj_tag(v_e_1784_) == 0)
{
uint8_t v___x_1785_; 
v___x_1785_ = 2;
return v___x_1785_;
}
else
{
uint8_t v___x_1786_; 
v___x_1786_ = 0;
return v___x_1786_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___boxed(lean_object* v_e_1787_){
_start:
{
uint8_t v_res_1788_; lean_object* v_r_1789_; 
v_res_1788_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(v_e_1787_);
lean_dec_ref(v_e_1787_);
v_r_1789_ = lean_box(v_res_1788_);
return v_r_1789_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(lean_object* v_x_1790_){
_start:
{
if (lean_obj_tag(v_x_1790_) == 0)
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
v_a_1792_ = lean_ctor_get(v_x_1790_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v_x_1790_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v_x_1790_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v_x_1790_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
lean_ctor_set_tag(v___x_1794_, 1);
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
v_a_1800_ = lean_ctor_get(v_x_1790_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_x_1790_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v_x_1790_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v_x_1790_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
lean_ctor_set_tag(v___x_1802_, 0);
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg___boxed(lean_object* v_x_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(v_x_1808_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15(size_t v_sz_1811_, size_t v_i_1812_, lean_object* v_bs_1813_){
_start:
{
uint8_t v___x_1814_; 
v___x_1814_ = lean_usize_dec_lt(v_i_1812_, v_sz_1811_);
if (v___x_1814_ == 0)
{
return v_bs_1813_;
}
else
{
lean_object* v_v_1815_; lean_object* v_msg_1816_; lean_object* v___x_1817_; lean_object* v_bs_x27_1818_; size_t v___x_1819_; size_t v___x_1820_; lean_object* v___x_1821_; 
v_v_1815_ = lean_array_uget_borrowed(v_bs_1813_, v_i_1812_);
v_msg_1816_ = lean_ctor_get(v_v_1815_, 1);
lean_inc_ref(v_msg_1816_);
v___x_1817_ = lean_unsigned_to_nat(0u);
v_bs_x27_1818_ = lean_array_uset(v_bs_1813_, v_i_1812_, v___x_1817_);
v___x_1819_ = ((size_t)1ULL);
v___x_1820_ = lean_usize_add(v_i_1812_, v___x_1819_);
v___x_1821_ = lean_array_uset(v_bs_x27_1818_, v_i_1812_, v_msg_1816_);
v_i_1812_ = v___x_1820_;
v_bs_1813_ = v___x_1821_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15___boxed(lean_object* v_sz_1823_, lean_object* v_i_1824_, lean_object* v_bs_1825_){
_start:
{
size_t v_sz_boxed_1826_; size_t v_i_boxed_1827_; lean_object* v_res_1828_; 
v_sz_boxed_1826_ = lean_unbox_usize(v_sz_1823_);
lean_dec(v_sz_1823_);
v_i_boxed_1827_ = lean_unbox_usize(v_i_1824_);
lean_dec(v_i_1824_);
v_res_1828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15(v_sz_boxed_1826_, v_i_boxed_1827_, v_bs_1825_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(lean_object* v_oldTraces_1829_, lean_object* v_data_1830_, lean_object* v_ref_1831_, lean_object* v_msg_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v_toCold_1838_; lean_object* v_options_1839_; lean_object* v_currRecDepth_1840_; lean_object* v_maxRecDepth_1841_; lean_object* v_ref_1842_; lean_object* v_currNamespace_1843_; lean_object* v_openDecls_1844_; lean_object* v_initHeartbeats_1845_; lean_object* v_maxHeartbeats_1846_; lean_object* v_currMacroScope_1847_; uint8_t v_diag_1848_; uint8_t v_suppressElabErrors_1849_; lean_object* v___x_1850_; lean_object* v_traceState_1851_; lean_object* v_traces_1852_; lean_object* v_ref_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; size_t v_sz_1856_; size_t v___x_1857_; lean_object* v___x_1858_; lean_object* v_msg_1859_; lean_object* v___x_1860_; lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1898_; 
v_toCold_1838_ = lean_ctor_get(v___y_1835_, 0);
v_options_1839_ = lean_ctor_get(v___y_1835_, 1);
v_currRecDepth_1840_ = lean_ctor_get(v___y_1835_, 2);
v_maxRecDepth_1841_ = lean_ctor_get(v___y_1835_, 3);
v_ref_1842_ = lean_ctor_get(v___y_1835_, 4);
v_currNamespace_1843_ = lean_ctor_get(v___y_1835_, 5);
v_openDecls_1844_ = lean_ctor_get(v___y_1835_, 6);
v_initHeartbeats_1845_ = lean_ctor_get(v___y_1835_, 7);
v_maxHeartbeats_1846_ = lean_ctor_get(v___y_1835_, 8);
v_currMacroScope_1847_ = lean_ctor_get(v___y_1835_, 9);
v_diag_1848_ = lean_ctor_get_uint8(v___y_1835_, sizeof(void*)*10);
v_suppressElabErrors_1849_ = lean_ctor_get_uint8(v___y_1835_, sizeof(void*)*10 + 1);
v___x_1850_ = lean_st_ref_get(v___y_1836_);
v_traceState_1851_ = lean_ctor_get(v___x_1850_, 4);
lean_inc_ref(v_traceState_1851_);
lean_dec(v___x_1850_);
v_traces_1852_ = lean_ctor_get(v_traceState_1851_, 0);
lean_inc_ref(v_traces_1852_);
lean_dec_ref(v_traceState_1851_);
v_ref_1853_ = l_Lean_replaceRef(v_ref_1831_, v_ref_1842_);
lean_inc(v_currMacroScope_1847_);
lean_inc(v_maxHeartbeats_1846_);
lean_inc(v_initHeartbeats_1845_);
lean_inc(v_openDecls_1844_);
lean_inc(v_currNamespace_1843_);
lean_inc(v_maxRecDepth_1841_);
lean_inc(v_currRecDepth_1840_);
lean_inc_ref(v_options_1839_);
lean_inc_ref(v_toCold_1838_);
v___x_1854_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1854_, 0, v_toCold_1838_);
lean_ctor_set(v___x_1854_, 1, v_options_1839_);
lean_ctor_set(v___x_1854_, 2, v_currRecDepth_1840_);
lean_ctor_set(v___x_1854_, 3, v_maxRecDepth_1841_);
lean_ctor_set(v___x_1854_, 4, v_ref_1853_);
lean_ctor_set(v___x_1854_, 5, v_currNamespace_1843_);
lean_ctor_set(v___x_1854_, 6, v_openDecls_1844_);
lean_ctor_set(v___x_1854_, 7, v_initHeartbeats_1845_);
lean_ctor_set(v___x_1854_, 8, v_maxHeartbeats_1846_);
lean_ctor_set(v___x_1854_, 9, v_currMacroScope_1847_);
lean_ctor_set_uint8(v___x_1854_, sizeof(void*)*10, v_diag_1848_);
lean_ctor_set_uint8(v___x_1854_, sizeof(void*)*10 + 1, v_suppressElabErrors_1849_);
v___x_1855_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1852_);
lean_dec_ref(v_traces_1852_);
v_sz_1856_ = lean_array_size(v___x_1855_);
v___x_1857_ = ((size_t)0ULL);
v___x_1858_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15(v_sz_1856_, v___x_1857_, v___x_1855_);
v_msg_1859_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1859_, 0, v_data_1830_);
lean_ctor_set(v_msg_1859_, 1, v_msg_1832_);
lean_ctor_set(v_msg_1859_, 2, v___x_1858_);
v___x_1860_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_1859_, v___y_1833_, v___y_1834_, v___x_1854_, v___y_1836_);
lean_dec_ref_known(v___x_1854_, 10);
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1898_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1898_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1865_; lean_object* v_traceState_1866_; lean_object* v_env_1867_; lean_object* v_nextMacroScope_1868_; lean_object* v_ngen_1869_; lean_object* v_auxDeclNGen_1870_; lean_object* v_cache_1871_; lean_object* v_messages_1872_; lean_object* v_infoState_1873_; lean_object* v_snapshotTasks_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1897_; 
v___x_1865_ = lean_st_ref_take(v___y_1836_);
v_traceState_1866_ = lean_ctor_get(v___x_1865_, 4);
v_env_1867_ = lean_ctor_get(v___x_1865_, 0);
v_nextMacroScope_1868_ = lean_ctor_get(v___x_1865_, 1);
v_ngen_1869_ = lean_ctor_get(v___x_1865_, 2);
v_auxDeclNGen_1870_ = lean_ctor_get(v___x_1865_, 3);
v_cache_1871_ = lean_ctor_get(v___x_1865_, 5);
v_messages_1872_ = lean_ctor_get(v___x_1865_, 6);
v_infoState_1873_ = lean_ctor_get(v___x_1865_, 7);
v_snapshotTasks_1874_ = lean_ctor_get(v___x_1865_, 8);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1876_ = v___x_1865_;
v_isShared_1877_ = v_isSharedCheck_1897_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_snapshotTasks_1874_);
lean_inc(v_infoState_1873_);
lean_inc(v_messages_1872_);
lean_inc(v_cache_1871_);
lean_inc(v_traceState_1866_);
lean_inc(v_auxDeclNGen_1870_);
lean_inc(v_ngen_1869_);
lean_inc(v_nextMacroScope_1868_);
lean_inc(v_env_1867_);
lean_dec(v___x_1865_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1897_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
uint64_t v_tid_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1895_; 
v_tid_1878_ = lean_ctor_get_uint64(v_traceState_1866_, sizeof(void*)*1);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_traceState_1866_);
if (v_isSharedCheck_1895_ == 0)
{
lean_object* v_unused_1896_; 
v_unused_1896_ = lean_ctor_get(v_traceState_1866_, 0);
lean_dec(v_unused_1896_);
v___x_1880_ = v_traceState_1866_;
v_isShared_1881_ = v_isSharedCheck_1895_;
goto v_resetjp_1879_;
}
else
{
lean_dec(v_traceState_1866_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1895_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1882_, 0, v_ref_1831_);
lean_ctor_set(v___x_1882_, 1, v_a_1861_);
v___x_1883_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1829_, v___x_1882_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v___x_1883_);
v___x_1885_ = v___x_1880_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1883_);
lean_ctor_set_uint64(v_reuseFailAlloc_1894_, sizeof(void*)*1, v_tid_1878_);
v___x_1885_ = v_reuseFailAlloc_1894_;
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
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_env_1867_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v_nextMacroScope_1868_);
lean_ctor_set(v_reuseFailAlloc_1893_, 2, v_ngen_1869_);
lean_ctor_set(v_reuseFailAlloc_1893_, 3, v_auxDeclNGen_1870_);
lean_ctor_set(v_reuseFailAlloc_1893_, 4, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1893_, 5, v_cache_1871_);
lean_ctor_set(v_reuseFailAlloc_1893_, 6, v_messages_1872_);
lean_ctor_set(v_reuseFailAlloc_1893_, 7, v_infoState_1873_);
lean_ctor_set(v_reuseFailAlloc_1893_, 8, v_snapshotTasks_1874_);
v___x_1887_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1891_; 
v___x_1888_ = lean_st_ref_put(v___y_1836_, v___x_1887_);
v___x_1889_ = lean_box(0);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1889_);
v___x_1891_ = v___x_1863_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1889_);
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
lean_object* v_fst_1927_; lean_object* v_snd_1928_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v_data_1932_; lean_object* v_fst_1943_; lean_object* v_snd_1944_; lean_object* v___x_1945_; uint8_t v___x_1946_; lean_object* v___y_1948_; lean_object* v_a_1949_; uint8_t v___y_1964_; double v___y_1995_; 
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
lean_object* v___x_2000_; uint8_t v___x_2001_; 
v___x_2000_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2001_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_opts_1917_, v___x_2000_);
if (v___x_2001_ == 0)
{
lean_object* v___x_2002_; lean_object* v___x_2003_; double v___x_2004_; double v___x_2005_; double v___x_2006_; 
v___x_2002_ = l_Lean_trace_profiler_threshold;
v___x_2003_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_1917_, v___x_2002_);
v___x_2004_ = lean_float_of_nat(v___x_2003_);
v___x_2005_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2);
v___x_2006_ = lean_float_div(v___x_2004_, v___x_2005_);
v___y_1995_ = v___x_2006_;
goto v___jp_1994_;
}
else
{
lean_object* v___x_2007_; lean_object* v___x_2008_; double v___x_2009_; 
v___x_2007_ = l_Lean_trace_profiler_threshold;
v___x_2008_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_1917_, v___x_2007_);
v___x_2009_ = lean_float_of_nat(v___x_2008_);
v___y_1995_ = v___x_2009_;
goto v___jp_1994_;
}
}
v___jp_1929_:
{
lean_object* v___x_1933_; 
lean_inc(v___y_1930_);
v___x_1933_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(v_oldTraces_1919_, v_data_1932_, v___y_1930_, v___y_1931_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
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
v___y_1930_ = v___y_1948_;
v___y_1931_ = v_a_1949_;
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
v___y_1930_ = v___y_1948_;
v___y_1931_ = v_a_1949_;
v_data_1932_ = v_data_1955_;
goto v___jp_1929_;
}
}
v___jp_1958_:
{
lean_object* v_ref_1959_; lean_object* v___x_1960_; 
v_ref_1959_ = lean_ctor_get(v___y_1924_, 4);
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
lean_object* v___x_1965_; lean_object* v_traceState_1966_; lean_object* v_env_1967_; lean_object* v_nextMacroScope_1968_; lean_object* v_ngen_1969_; lean_object* v_auxDeclNGen_1970_; lean_object* v_cache_1971_; lean_object* v_messages_1972_; lean_object* v_infoState_1973_; lean_object* v_snapshotTasks_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1993_; 
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
v_messages_1972_ = lean_ctor_get(v___x_1965_, 6);
v_infoState_1973_ = lean_ctor_get(v___x_1965_, 7);
v_snapshotTasks_1974_ = lean_ctor_get(v___x_1965_, 8);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1976_ = v___x_1965_;
v_isShared_1977_ = v_isSharedCheck_1993_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_snapshotTasks_1974_);
lean_inc(v_infoState_1973_);
lean_inc(v_messages_1972_);
lean_inc(v_cache_1971_);
lean_inc(v_traceState_1966_);
lean_inc(v_auxDeclNGen_1970_);
lean_inc(v_ngen_1969_);
lean_inc(v_nextMacroScope_1968_);
lean_inc(v_env_1967_);
lean_dec(v___x_1965_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1993_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
uint64_t v_tid_1978_; lean_object* v_traces_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1992_; 
v_tid_1978_ = lean_ctor_get_uint64(v_traceState_1966_, sizeof(void*)*1);
v_traces_1979_ = lean_ctor_get(v_traceState_1966_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v_traceState_1966_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1981_ = v_traceState_1966_;
v_isShared_1982_ = v_isSharedCheck_1992_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_traces_1979_);
lean_dec(v_traceState_1966_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1992_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1983_; lean_object* v___x_1985_; 
v___x_1983_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1919_, v_traces_1979_);
lean_dec_ref(v_traces_1979_);
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 0, v___x_1983_);
v___x_1985_ = v___x_1981_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1983_);
lean_ctor_set_uint64(v_reuseFailAlloc_1991_, sizeof(void*)*1, v_tid_1978_);
v___x_1985_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_object* v___x_1987_; 
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 4, v___x_1985_);
v___x_1987_ = v___x_1976_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_env_1967_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_nextMacroScope_1968_);
lean_ctor_set(v_reuseFailAlloc_1990_, 2, v_ngen_1969_);
lean_ctor_set(v_reuseFailAlloc_1990_, 3, v_auxDeclNGen_1970_);
lean_ctor_set(v_reuseFailAlloc_1990_, 4, v___x_1985_);
lean_ctor_set(v_reuseFailAlloc_1990_, 5, v_cache_1971_);
lean_ctor_set(v_reuseFailAlloc_1990_, 6, v_messages_1972_);
lean_ctor_set(v_reuseFailAlloc_1990_, 7, v_infoState_1973_);
lean_ctor_set(v_reuseFailAlloc_1990_, 8, v_snapshotTasks_1974_);
v___x_1987_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1988_ = lean_st_ref_put(v___y_1925_, v___x_1987_);
v___x_1989_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(v_fst_1927_);
return v___x_1989_;
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
v___jp_1994_:
{
double v___x_1996_; double v___x_1997_; double v___x_1998_; uint8_t v___x_1999_; 
v___x_1996_ = lean_unbox_float(v_snd_1944_);
v___x_1997_ = lean_unbox_float(v_fst_1943_);
v___x_1998_ = lean_float_sub(v___x_1996_, v___x_1997_);
v___x_1999_ = lean_float_decLt(v___y_1995_, v___x_1998_);
v___y_1964_ = v___x_1999_;
goto v___jp_1963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___boxed(lean_object* v_cls_2010_, lean_object* v_collapsed_2011_, lean_object* v_tag_2012_, lean_object* v_opts_2013_, lean_object* v_clsEnabled_2014_, lean_object* v_oldTraces_2015_, lean_object* v_msg_2016_, lean_object* v_resStartStop_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
uint8_t v_collapsed_boxed_2023_; uint8_t v_clsEnabled_boxed_2024_; lean_object* v_res_2025_; 
v_collapsed_boxed_2023_ = lean_unbox(v_collapsed_2011_);
v_clsEnabled_boxed_2024_ = lean_unbox(v_clsEnabled_2014_);
v_res_2025_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v_cls_2010_, v_collapsed_boxed_2023_, v_tag_2012_, v_opts_2013_, v_clsEnabled_boxed_2024_, v_oldTraces_2015_, v_msg_2016_, v_resStartStop_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec_ref(v_opts_2013_);
return v_res_2025_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__3(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__2));
v___x_2031_ = l_Lean_stringToMessageData(v___x_2030_);
return v___x_2031_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__5(void){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2033_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__4));
v___x_2034_ = l_Lean_stringToMessageData(v___x_2033_);
return v___x_2034_;
}
}
static double _init_l_Lean_Meta_rwMatcher___closed__6(void){
_start:
{
lean_object* v___x_2035_; double v___x_2036_; 
v___x_2035_ = lean_unsigned_to_nat(1000000000u);
v___x_2036_ = lean_float_of_nat(v___x_2035_);
return v___x_2036_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__8(void){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__7));
v___x_2039_ = l_Lean_stringToMessageData(v___x_2038_);
return v___x_2039_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__13(void){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2047_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2048_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
v___x_2049_ = l_Lean_Name_append(v___x_2048_, v___x_2047_);
return v___x_2049_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__15(void){
_start:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__14));
v___x_2052_ = l_Lean_stringToMessageData(v___x_2051_);
return v___x_2052_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__17(void){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__16));
v___x_2055_ = l_Lean_stringToMessageData(v___x_2054_);
return v___x_2055_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__19(void){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__18));
v___x_2058_ = l_Lean_stringToMessageData(v___x_2057_);
return v___x_2058_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__21(void){
_start:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2060_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__20));
v___x_2061_ = l_Lean_stringToMessageData(v___x_2060_);
return v___x_2061_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__22(void){
_start:
{
lean_object* v___x_2062_; lean_object* v_dummy_2063_; 
v___x_2062_ = lean_box(0);
v_dummy_2063_ = l_Lean_Expr_sort___override(v___x_2062_);
return v_dummy_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher(lean_object* v_altIdx_2073_, lean_object* v_e_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_){
_start:
{
lean_object* v___y_2081_; lean_object* v___y_2100_; lean_object* v___y_2104_; uint8_t v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2108_; uint8_t v___y_2109_; lean_object* v___y_2138_; uint8_t v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v_a_2142_; lean_object* v___y_2146_; uint8_t v___y_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2153_; lean_object* v___y_2154_; uint8_t v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; uint8_t v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; uint8_t v___y_2162_; lean_object* v___y_2163_; lean_object* v_a_2164_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; uint8_t v___y_2177_; lean_object* v___y_2178_; uint8_t v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v___y_2182_; uint8_t v___y_2183_; lean_object* v___y_2184_; lean_object* v_a_2185_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; uint8_t v___y_2191_; lean_object* v___y_2192_; uint8_t v___y_2193_; lean_object* v___y_2194_; lean_object* v___y_2195_; lean_object* v___y_2196_; uint8_t v___y_2197_; lean_object* v___y_2198_; lean_object* v___y_2199_; lean_object* v___y_2210_; lean_object* v___y_2211_; uint8_t v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; uint8_t v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; uint8_t v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v_a_2221_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; uint8_t v___y_2237_; lean_object* v___y_2238_; uint8_t v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; uint8_t v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v_a_2245_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; uint8_t v___y_2251_; lean_object* v___y_2252_; uint8_t v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; uint8_t v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2270_; lean_object* v___y_2271_; uint8_t v___y_2272_; uint8_t v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; uint8_t v___y_2278_; lean_object* v___y_2279_; uint8_t v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; uint8_t v___y_2283_; lean_object* v___y_2284_; uint8_t v___y_2350_; uint8_t v___y_2355_; lean_object* v___y_2360_; uint8_t v___y_2361_; lean_object* v_proof_2362_; lean_object* v___y_2367_; uint8_t v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; uint8_t v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2377_; uint8_t v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; uint8_t v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; uint8_t v___y_2390_; lean_object* v___y_2403_; uint8_t v___y_2404_; lean_object* v___y_2405_; uint8_t v___y_2406_; uint8_t v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2425_; uint8_t v___y_2426_; lean_object* v___y_2427_; uint8_t v___y_2428_; uint8_t v___y_2429_; lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v_a_2437_; lean_object* v___y_2454_; uint8_t v___y_2455_; lean_object* v___y_2456_; uint8_t v___y_2457_; uint8_t v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2470_; uint8_t v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; uint8_t v___y_2474_; uint8_t v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; size_t v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2498_; uint8_t v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; uint8_t v___y_2502_; lean_object* v___y_2503_; size_t v___y_2504_; lean_object* v___y_2505_; uint8_t v_fst_2506_; lean_object* v_fst_2507_; lean_object* v_snd_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___x_2532_; uint8_t v___y_2534_; lean_object* v___x_2727_; uint8_t v___x_2728_; 
v___x_2532_ = lean_box(0);
v___x_2727_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__25));
v___x_2728_ = l_Lean_Expr_isAppOf(v_e_2074_, v___x_2727_);
if (v___x_2728_ == 0)
{
lean_object* v___x_2729_; uint8_t v___x_2730_; 
v___x_2729_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__27));
v___x_2730_ = l_Lean_Expr_isAppOf(v_e_2074_, v___x_2729_);
v___y_2534_ = v___x_2730_;
goto v___jp_2533_;
}
else
{
v___y_2534_ = v___x_2728_;
goto v___jp_2533_;
}
v___jp_2080_:
{
if (lean_obj_tag(v___y_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2090_; 
v_a_2082_ = lean_ctor_get(v___y_2081_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___y_2081_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2084_ = v___y_2081_;
v_isShared_2085_ = v_isSharedCheck_2090_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___y_2081_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2090_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v_a_2086_; lean_object* v___x_2088_; 
v_a_2086_ = lean_ctor_get(v_a_2082_, 0);
lean_inc(v_a_2086_);
lean_dec(v_a_2082_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 0, v_a_2086_);
v___x_2088_ = v___x_2084_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
v_a_2091_ = lean_ctor_get(v___y_2081_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___y_2081_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___y_2081_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___y_2081_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
v___jp_2099_:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = lean_box(0);
lean_inc(v_a_2078_);
lean_inc_ref(v_a_2077_);
lean_inc(v_a_2076_);
lean_inc_ref(v_a_2075_);
v___x_2102_ = lean_apply_6(v___y_2100_, v___x_2101_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, lean_box(0));
v___y_2081_ = v___x_2102_;
goto v___jp_2080_;
}
v___jp_2103_:
{
if (v___y_2109_ == 0)
{
lean_object* v_options_2110_; uint8_t v_hasTrace_2111_; 
v_options_2110_ = lean_ctor_get(v_a_2077_, 1);
v_hasTrace_2111_ = lean_ctor_get_uint8(v_options_2110_, sizeof(void*)*1);
if (v_hasTrace_2111_ == 0)
{
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec(v___y_2106_);
v___y_2100_ = v___y_2104_;
goto v___jp_2099_;
}
else
{
lean_object* v_toCold_2112_; lean_object* v_inheritedTraceOptions_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; uint8_t v___x_2116_; 
v_toCold_2112_ = lean_ctor_get(v_a_2077_, 0);
v_inheritedTraceOptions_2113_ = lean_ctor_get(v_toCold_2112_, 4);
v___x_2114_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2106_);
v___x_2115_ = l_Lean_Name_append(v___x_2114_, v___y_2106_);
v___x_2116_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2113_, v_options_2110_, v___x_2115_);
lean_dec(v___x_2115_);
if (v___x_2116_ == 0)
{
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec(v___y_2106_);
v___y_2100_ = v___y_2104_;
goto v___jp_2099_;
}
else
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2117_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__3, &l_Lean_Meta_rwMatcher___closed__3_once, _init_l_Lean_Meta_rwMatcher___closed__3);
v___x_2118_ = l_Lean_MessageData_ofConstName(v___y_2107_, v___y_2105_);
v___x_2119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2117_);
lean_ctor_set(v___x_2119_, 1, v___x_2118_);
v___x_2120_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__5, &l_Lean_Meta_rwMatcher___closed__5_once, _init_l_Lean_Meta_rwMatcher___closed__5);
v___x_2121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2119_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
v___x_2122_ = l_Lean_Exception_toMessageData(v___y_2108_);
v___x_2123_ = l_Lean_indentD(v___x_2122_);
v___x_2124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2121_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2106_, v___x_2124_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2127_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2125_, 1);
lean_inc(v_a_2078_);
lean_inc_ref(v_a_2077_);
lean_inc(v_a_2076_);
lean_inc_ref(v_a_2075_);
v___x_2127_ = lean_apply_6(v___y_2104_, v_a_2126_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, lean_box(0));
v___y_2081_ = v___x_2127_;
goto v___jp_2080_;
}
else
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_dec_ref(v___y_2104_);
v_a_2128_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2125_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2125_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
}
}
else
{
lean_object* v___x_2136_; 
lean_dec(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2104_);
v___x_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2136_, 0, v___y_2108_);
return v___x_2136_;
}
}
v___jp_2137_:
{
uint8_t v___x_2143_; 
v___x_2143_ = l_Lean_Exception_isInterrupt(v_a_2142_);
if (v___x_2143_ == 0)
{
uint8_t v___x_2144_; 
lean_inc_ref(v_a_2142_);
v___x_2144_ = l_Lean_Exception_isRuntime(v_a_2142_);
v___y_2104_ = v___y_2138_;
v___y_2105_ = v___y_2139_;
v___y_2106_ = v___y_2140_;
v___y_2107_ = v___y_2141_;
v___y_2108_ = v_a_2142_;
v___y_2109_ = v___x_2144_;
goto v___jp_2103_;
}
else
{
v___y_2104_ = v___y_2138_;
v___y_2105_ = v___y_2139_;
v___y_2106_ = v___y_2140_;
v___y_2107_ = v___y_2141_;
v___y_2108_ = v_a_2142_;
v___y_2109_ = v___x_2143_;
goto v___jp_2103_;
}
}
v___jp_2145_:
{
if (lean_obj_tag(v___y_2150_) == 0)
{
lean_dec(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2146_);
return v___y_2150_;
}
else
{
lean_object* v_a_2151_; 
v_a_2151_ = lean_ctor_get(v___y_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref_known(v___y_2150_, 1);
v___y_2138_ = v___y_2146_;
v___y_2139_ = v___y_2147_;
v___y_2140_ = v___y_2148_;
v___y_2141_ = v___y_2149_;
v_a_2142_ = v_a_2151_;
goto v___jp_2137_;
}
}
v___jp_2152_:
{
lean_object* v___x_2165_; double v___x_2166_; double v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2165_ = lean_io_get_num_heartbeats();
v___x_2166_ = lean_float_of_nat(v___y_2161_);
v___x_2167_ = lean_float_of_nat(v___x_2165_);
v___x_2168_ = lean_box_float(v___x_2166_);
v___x_2169_ = lean_box_float(v___x_2167_);
v___x_2170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2168_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
v___x_2171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2171_, 0, v_a_2164_);
lean_ctor_set(v___x_2171_, 1, v___x_2170_);
lean_inc_ref(v___y_2159_);
lean_inc(v___y_2157_);
v___x_2172_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v___y_2157_, v___y_2158_, v___y_2159_, v___y_2163_, v___y_2162_, v___y_2156_, v___y_2154_, v___x_2171_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
v___y_2146_ = v___y_2153_;
v___y_2147_ = v___y_2155_;
v___y_2148_ = v___y_2157_;
v___y_2149_ = v___y_2160_;
v___y_2150_ = v___x_2172_;
goto v___jp_2145_;
}
v___jp_2173_:
{
lean_object* v___x_2186_; 
v___x_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2186_, 0, v_a_2185_);
v___y_2153_ = v___y_2175_;
v___y_2154_ = v___y_2174_;
v___y_2155_ = v___y_2177_;
v___y_2156_ = v___y_2176_;
v___y_2157_ = v___y_2178_;
v___y_2158_ = v___y_2179_;
v___y_2159_ = v___y_2180_;
v___y_2160_ = v___y_2182_;
v___y_2161_ = v___y_2181_;
v___y_2162_ = v___y_2183_;
v___y_2163_ = v___y_2184_;
v_a_2164_ = v___x_2186_;
goto v___jp_2152_;
}
v___jp_2187_:
{
if (lean_obj_tag(v___y_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
v_a_2200_ = lean_ctor_get(v___y_2199_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___y_2199_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___y_2199_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___y_2199_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
lean_ctor_set_tag(v___x_2202_, 1);
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
v___y_2153_ = v___y_2189_;
v___y_2154_ = v___y_2188_;
v___y_2155_ = v___y_2191_;
v___y_2156_ = v___y_2190_;
v___y_2157_ = v___y_2192_;
v___y_2158_ = v___y_2193_;
v___y_2159_ = v___y_2194_;
v___y_2160_ = v___y_2196_;
v___y_2161_ = v___y_2195_;
v___y_2162_ = v___y_2197_;
v___y_2163_ = v___y_2198_;
v_a_2164_ = v___x_2205_;
goto v___jp_2152_;
}
}
}
else
{
lean_object* v_a_2208_; 
v_a_2208_ = lean_ctor_get(v___y_2199_, 0);
lean_inc(v_a_2208_);
lean_dec_ref_known(v___y_2199_, 1);
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
v___y_2184_ = v___y_2198_;
v_a_2185_ = v_a_2208_;
goto v___jp_2173_;
}
}
v___jp_2209_:
{
lean_object* v___x_2222_; double v___x_2223_; double v___x_2224_; double v___x_2225_; double v___x_2226_; double v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2222_ = lean_io_mono_nanos_now();
v___x_2223_ = lean_float_of_nat(v___y_2219_);
v___x_2224_ = lean_float_once(&l_Lean_Meta_rwMatcher___closed__6, &l_Lean_Meta_rwMatcher___closed__6_once, _init_l_Lean_Meta_rwMatcher___closed__6);
v___x_2225_ = lean_float_div(v___x_2223_, v___x_2224_);
v___x_2226_ = lean_float_of_nat(v___x_2222_);
v___x_2227_ = lean_float_div(v___x_2226_, v___x_2224_);
v___x_2228_ = lean_box_float(v___x_2225_);
v___x_2229_ = lean_box_float(v___x_2227_);
v___x_2230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2228_);
lean_ctor_set(v___x_2230_, 1, v___x_2229_);
v___x_2231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2231_, 0, v_a_2221_);
lean_ctor_set(v___x_2231_, 1, v___x_2230_);
lean_inc_ref(v___y_2216_);
lean_inc(v___y_2214_);
v___x_2232_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v___y_2214_, v___y_2215_, v___y_2216_, v___y_2220_, v___y_2218_, v___y_2213_, v___y_2211_, v___x_2231_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
v___y_2146_ = v___y_2210_;
v___y_2147_ = v___y_2212_;
v___y_2148_ = v___y_2214_;
v___y_2149_ = v___y_2217_;
v___y_2150_ = v___x_2232_;
goto v___jp_2145_;
}
v___jp_2233_:
{
lean_object* v___x_2246_; 
v___x_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2246_, 0, v_a_2245_);
v___y_2210_ = v___y_2235_;
v___y_2211_ = v___y_2234_;
v___y_2212_ = v___y_2237_;
v___y_2213_ = v___y_2236_;
v___y_2214_ = v___y_2238_;
v___y_2215_ = v___y_2239_;
v___y_2216_ = v___y_2240_;
v___y_2217_ = v___y_2241_;
v___y_2218_ = v___y_2242_;
v___y_2219_ = v___y_2243_;
v___y_2220_ = v___y_2244_;
v_a_2221_ = v___x_2246_;
goto v___jp_2209_;
}
v___jp_2247_:
{
if (lean_obj_tag(v___y_2259_) == 0)
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
v_a_2260_ = lean_ctor_get(v___y_2259_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___y_2259_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2262_ = v___y_2259_;
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___y_2259_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2265_; 
if (v_isShared_2263_ == 0)
{
lean_ctor_set_tag(v___x_2262_, 1);
v___x_2265_ = v___x_2262_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_a_2260_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
v___y_2210_ = v___y_2249_;
v___y_2211_ = v___y_2248_;
v___y_2212_ = v___y_2251_;
v___y_2213_ = v___y_2250_;
v___y_2214_ = v___y_2252_;
v___y_2215_ = v___y_2253_;
v___y_2216_ = v___y_2254_;
v___y_2217_ = v___y_2255_;
v___y_2218_ = v___y_2256_;
v___y_2219_ = v___y_2257_;
v___y_2220_ = v___y_2258_;
v_a_2221_ = v___x_2265_;
goto v___jp_2209_;
}
}
}
else
{
lean_object* v_a_2268_; 
v_a_2268_ = lean_ctor_get(v___y_2259_, 0);
lean_inc(v_a_2268_);
lean_dec_ref_known(v___y_2259_, 1);
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
v___y_2244_ = v___y_2258_;
v_a_2245_ = v_a_2268_;
goto v___jp_2233_;
}
}
v___jp_2269_:
{
lean_object* v___x_2285_; lean_object* v_a_2286_; lean_object* v___x_2287_; uint8_t v___x_2288_; 
v___x_2285_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg(v_a_2078_);
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
lean_dec_ref(v___x_2285_);
v___x_2287_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2288_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v___y_2284_, v___x_2287_);
if (v___x_2288_ == 0)
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2289_ = lean_io_mono_nanos_now();
lean_inc(v_a_2078_);
lean_inc_ref(v_a_2077_);
lean_inc(v_a_2076_);
lean_inc_ref(v_a_2075_);
v___x_2290_ = lean_infer_type(v___y_2277_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_a_2291_; uint8_t v___x_2292_; lean_object* v___x_2293_; 
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2291_);
lean_dec_ref_known(v___x_2290_, 1);
v___x_2292_ = 0;
v___x_2293_ = l_Lean_Meta_forallMetaTelescope(v_a_2291_, v___x_2292_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v_snd_2295_; lean_object* v_fst_2296_; lean_object* v_snd_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2315_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_a_2294_);
lean_dec_ref_known(v___x_2293_, 1);
v_snd_2295_ = lean_ctor_get(v_a_2294_, 1);
lean_inc(v_snd_2295_);
v_fst_2296_ = lean_ctor_get(v_a_2294_, 0);
lean_inc(v_fst_2296_);
lean_dec(v_a_2294_);
v_snd_2297_ = lean_ctor_get(v_snd_2295_, 1);
v_isSharedCheck_2315_ = !lean_is_exclusive(v_snd_2295_);
if (v_isSharedCheck_2315_ == 0)
{
lean_object* v_unused_2316_; 
v_unused_2316_ = lean_ctor_get(v_snd_2295_, 0);
lean_dec(v_unused_2316_);
v___x_2299_ = v_snd_2295_;
v_isShared_2300_ = v_isSharedCheck_2315_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_snd_2297_);
lean_dec(v_snd_2295_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2315_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; uint8_t v___x_2303_; 
v___x_2301_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2279_);
v___x_2302_ = l_Lean_Name_append(v___x_2301_, v___y_2279_);
v___x_2303_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2275_, v___y_2284_, v___x_2302_);
lean_dec(v___x_2302_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
lean_del_object(v___x_2299_);
v___x_2304_ = lean_box(0);
v___x_2305_ = l_Lean_Meta_rwMatcher___lam__2(v___y_2273_, v___y_2271_, v_fst_2296_, v___y_2274_, v_e_2074_, v___y_2272_, v_snd_2297_, v___x_2304_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
lean_dec(v_snd_2297_);
v___y_2248_ = v___y_2270_;
v___y_2249_ = v___y_2276_;
v___y_2250_ = v_a_2286_;
v___y_2251_ = v___y_2278_;
v___y_2252_ = v___y_2279_;
v___y_2253_ = v___y_2280_;
v___y_2254_ = v___y_2281_;
v___y_2255_ = v___y_2282_;
v___y_2256_ = v___y_2283_;
v___y_2257_ = v___x_2289_;
v___y_2258_ = v___y_2284_;
v___y_2259_ = v___x_2305_;
goto v___jp_2247_;
}
else
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2309_; 
v___x_2306_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2297_);
v___x_2307_ = l_Lean_indentExpr(v_snd_2297_);
if (v_isShared_2300_ == 0)
{
lean_ctor_set_tag(v___x_2299_, 7);
lean_ctor_set(v___x_2299_, 1, v___x_2307_);
lean_ctor_set(v___x_2299_, 0, v___x_2306_);
v___x_2309_ = v___x_2299_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2306_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v___x_2307_);
v___x_2309_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
lean_object* v___x_2310_; 
lean_inc(v___y_2279_);
v___x_2310_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2279_, v___x_2309_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; lean_object* v___x_2312_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2311_);
lean_dec_ref_known(v___x_2310_, 1);
v___x_2312_ = l_Lean_Meta_rwMatcher___lam__2(v___y_2273_, v___y_2271_, v_fst_2296_, v___y_2274_, v_e_2074_, v___y_2272_, v_snd_2297_, v_a_2311_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
lean_dec(v_snd_2297_);
v___y_2248_ = v___y_2270_;
v___y_2249_ = v___y_2276_;
v___y_2250_ = v_a_2286_;
v___y_2251_ = v___y_2278_;
v___y_2252_ = v___y_2279_;
v___y_2253_ = v___y_2280_;
v___y_2254_ = v___y_2281_;
v___y_2255_ = v___y_2282_;
v___y_2256_ = v___y_2283_;
v___y_2257_ = v___x_2289_;
v___y_2258_ = v___y_2284_;
v___y_2259_ = v___x_2312_;
goto v___jp_2247_;
}
else
{
lean_object* v_a_2313_; 
lean_dec(v_snd_2297_);
lean_dec(v_fst_2296_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2271_);
lean_dec_ref(v_e_2074_);
v_a_2313_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2313_);
lean_dec_ref_known(v___x_2310_, 1);
v___y_2234_ = v___y_2270_;
v___y_2235_ = v___y_2276_;
v___y_2236_ = v_a_2286_;
v___y_2237_ = v___y_2278_;
v___y_2238_ = v___y_2279_;
v___y_2239_ = v___y_2280_;
v___y_2240_ = v___y_2281_;
v___y_2241_ = v___y_2282_;
v___y_2242_ = v___y_2283_;
v___y_2243_ = v___x_2289_;
v___y_2244_ = v___y_2284_;
v_a_2245_ = v_a_2313_;
goto v___jp_2233_;
}
}
}
}
}
else
{
lean_object* v_a_2317_; 
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2271_);
lean_dec_ref(v_e_2074_);
v_a_2317_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_a_2317_);
lean_dec_ref_known(v___x_2293_, 1);
v___y_2234_ = v___y_2270_;
v___y_2235_ = v___y_2276_;
v___y_2236_ = v_a_2286_;
v___y_2237_ = v___y_2278_;
v___y_2238_ = v___y_2279_;
v___y_2239_ = v___y_2280_;
v___y_2240_ = v___y_2281_;
v___y_2241_ = v___y_2282_;
v___y_2242_ = v___y_2283_;
v___y_2243_ = v___x_2289_;
v___y_2244_ = v___y_2284_;
v_a_2245_ = v_a_2317_;
goto v___jp_2233_;
}
}
else
{
lean_object* v_a_2318_; 
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2271_);
lean_dec_ref(v_e_2074_);
v_a_2318_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2318_);
lean_dec_ref_known(v___x_2290_, 1);
v___y_2234_ = v___y_2270_;
v___y_2235_ = v___y_2276_;
v___y_2236_ = v_a_2286_;
v___y_2237_ = v___y_2278_;
v___y_2238_ = v___y_2279_;
v___y_2239_ = v___y_2280_;
v___y_2240_ = v___y_2281_;
v___y_2241_ = v___y_2282_;
v___y_2242_ = v___y_2283_;
v___y_2243_ = v___x_2289_;
v___y_2244_ = v___y_2284_;
v_a_2245_ = v_a_2318_;
goto v___jp_2233_;
}
}
else
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2078_);
lean_inc_ref(v_a_2077_);
lean_inc(v_a_2076_);
lean_inc_ref(v_a_2075_);
v___x_2320_ = lean_infer_type(v___y_2277_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; uint8_t v___x_2322_; lean_object* v___x_2323_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref_known(v___x_2320_, 1);
v___x_2322_ = 0;
v___x_2323_ = l_Lean_Meta_forallMetaTelescope(v_a_2321_, v___x_2322_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
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
lean_inc(v___y_2279_);
v___x_2332_ = l_Lean_Name_append(v___x_2331_, v___y_2279_);
v___x_2333_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2275_, v___y_2284_, v___x_2332_);
lean_dec(v___x_2332_);
if (v___x_2333_ == 0)
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
lean_del_object(v___x_2329_);
v___x_2334_ = lean_box(0);
v___x_2335_ = l_Lean_Meta_rwMatcher___lam__3(v___y_2273_, v___y_2271_, v_fst_2326_, v___y_2274_, v_e_2074_, v___y_2272_, v_snd_2327_, v___x_2334_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
lean_dec(v_snd_2327_);
v___y_2188_ = v___y_2270_;
v___y_2189_ = v___y_2276_;
v___y_2190_ = v_a_2286_;
v___y_2191_ = v___y_2278_;
v___y_2192_ = v___y_2279_;
v___y_2193_ = v___y_2280_;
v___y_2194_ = v___y_2281_;
v___y_2195_ = v___x_2319_;
v___y_2196_ = v___y_2282_;
v___y_2197_ = v___y_2283_;
v___y_2198_ = v___y_2284_;
v___y_2199_ = v___x_2335_;
goto v___jp_2187_;
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
lean_inc(v___y_2279_);
v___x_2340_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2279_, v___x_2339_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v___x_2342_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
lean_dec_ref_known(v___x_2340_, 1);
v___x_2342_ = l_Lean_Meta_rwMatcher___lam__3(v___y_2273_, v___y_2271_, v_fst_2326_, v___y_2274_, v_e_2074_, v___y_2272_, v_snd_2327_, v_a_2341_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
lean_dec(v_snd_2327_);
v___y_2188_ = v___y_2270_;
v___y_2189_ = v___y_2276_;
v___y_2190_ = v_a_2286_;
v___y_2191_ = v___y_2278_;
v___y_2192_ = v___y_2279_;
v___y_2193_ = v___y_2280_;
v___y_2194_ = v___y_2281_;
v___y_2195_ = v___x_2319_;
v___y_2196_ = v___y_2282_;
v___y_2197_ = v___y_2283_;
v___y_2198_ = v___y_2284_;
v___y_2199_ = v___x_2342_;
goto v___jp_2187_;
}
else
{
lean_object* v_a_2343_; 
lean_dec(v_snd_2327_);
lean_dec(v_fst_2326_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2271_);
lean_dec_ref(v_e_2074_);
v_a_2343_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2343_);
lean_dec_ref_known(v___x_2340_, 1);
v___y_2174_ = v___y_2270_;
v___y_2175_ = v___y_2276_;
v___y_2176_ = v_a_2286_;
v___y_2177_ = v___y_2278_;
v___y_2178_ = v___y_2279_;
v___y_2179_ = v___y_2280_;
v___y_2180_ = v___y_2281_;
v___y_2181_ = v___x_2319_;
v___y_2182_ = v___y_2282_;
v___y_2183_ = v___y_2283_;
v___y_2184_ = v___y_2284_;
v_a_2185_ = v_a_2343_;
goto v___jp_2173_;
}
}
}
}
}
else
{
lean_object* v_a_2347_; 
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2271_);
lean_dec_ref(v_e_2074_);
v_a_2347_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2347_);
lean_dec_ref_known(v___x_2323_, 1);
v___y_2174_ = v___y_2270_;
v___y_2175_ = v___y_2276_;
v___y_2176_ = v_a_2286_;
v___y_2177_ = v___y_2278_;
v___y_2178_ = v___y_2279_;
v___y_2179_ = v___y_2280_;
v___y_2180_ = v___y_2281_;
v___y_2181_ = v___x_2319_;
v___y_2182_ = v___y_2282_;
v___y_2183_ = v___y_2283_;
v___y_2184_ = v___y_2284_;
v_a_2185_ = v_a_2347_;
goto v___jp_2173_;
}
}
else
{
lean_object* v_a_2348_; 
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2271_);
lean_dec_ref(v_e_2074_);
v_a_2348_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2348_);
lean_dec_ref_known(v___x_2320_, 1);
v___y_2174_ = v___y_2270_;
v___y_2175_ = v___y_2276_;
v___y_2176_ = v_a_2286_;
v___y_2177_ = v___y_2278_;
v___y_2178_ = v___y_2279_;
v___y_2179_ = v___y_2280_;
v___y_2180_ = v___y_2281_;
v___y_2181_ = v___x_2319_;
v___y_2182_ = v___y_2282_;
v___y_2183_ = v___y_2283_;
v___y_2184_ = v___y_2284_;
v_a_2185_ = v_a_2348_;
goto v___jp_2173_;
}
}
}
v___jp_2349_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2351_ = lean_box(0);
v___x_2352_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2352_, 0, v_e_2074_);
lean_ctor_set(v___x_2352_, 1, v___x_2351_);
lean_ctor_set_uint8(v___x_2352_, sizeof(void*)*2, v___y_2350_);
v___x_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2352_);
return v___x_2353_;
}
v___jp_2354_:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2356_ = lean_box(0);
v___x_2357_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2357_, 0, v_e_2074_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
lean_ctor_set_uint8(v___x_2357_, sizeof(void*)*2, v___y_2355_);
v___x_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
return v___x_2358_;
}
v___jp_2359_:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2363_, 0, v_proof_2362_);
v___x_2364_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2364_, 0, v___y_2360_);
lean_ctor_set(v___x_2364_, 1, v___x_2363_);
lean_ctor_set_uint8(v___x_2364_, sizeof(void*)*2, v___y_2361_);
v___x_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
return v___x_2365_;
}
v___jp_2366_:
{
if (lean_obj_tag(v___y_2373_) == 0)
{
lean_object* v_a_2374_; 
lean_dec(v___y_2372_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2367_);
v_a_2374_ = lean_ctor_get(v___y_2373_, 0);
lean_inc(v_a_2374_);
lean_dec_ref_known(v___y_2373_, 1);
v___y_2360_ = v___y_2369_;
v___y_2361_ = v___y_2371_;
v_proof_2362_ = v_a_2374_;
goto v___jp_2359_;
}
else
{
lean_object* v_a_2375_; 
lean_dec_ref(v___y_2369_);
v_a_2375_ = lean_ctor_get(v___y_2373_, 0);
lean_inc(v_a_2375_);
lean_dec_ref_known(v___y_2373_, 1);
v___y_2138_ = v___y_2367_;
v___y_2139_ = v___y_2368_;
v___y_2140_ = v___y_2370_;
v___y_2141_ = v___y_2372_;
v_a_2142_ = v_a_2375_;
goto v___jp_2137_;
}
}
v___jp_2376_:
{
if (v___y_2390_ == 0)
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
lean_dec_ref(v___y_2388_);
v___x_2391_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_2392_ = l_Lean_MessageData_ofExpr(v___y_2381_);
v___x_2393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2391_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
v___x_2394_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_2395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2393_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = l_Lean_Exception_toMessageData(v___y_2382_);
v___x_2397_ = l_Lean_indentD(v___x_2396_);
v___x_2398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2395_);
lean_ctor_set(v___x_2398_, 1, v___x_2397_);
v___x_2399_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_2400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2398_);
lean_ctor_set(v___x_2400_, 1, v___x_2399_);
v___x_2401_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2400_, v___y_2379_, v___y_2386_, v___y_2380_, v___y_2389_);
v___y_2367_ = v___y_2377_;
v___y_2368_ = v___y_2378_;
v___y_2369_ = v___y_2383_;
v___y_2370_ = v___y_2384_;
v___y_2371_ = v___y_2385_;
v___y_2372_ = v___y_2387_;
v___y_2373_ = v___x_2401_;
goto v___jp_2366_;
}
else
{
lean_dec_ref(v___y_2382_);
lean_dec_ref(v___y_2381_);
v___y_2367_ = v___y_2377_;
v___y_2368_ = v___y_2378_;
v___y_2369_ = v___y_2383_;
v___y_2370_ = v___y_2384_;
v___y_2371_ = v___y_2385_;
v___y_2372_ = v___y_2387_;
v___y_2373_ = v___y_2388_;
goto v___jp_2366_;
}
}
v___jp_2402_:
{
lean_object* v___x_2415_; lean_object* v_a_2416_; lean_object* v___x_2417_; 
v___x_2415_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_2408_, v___y_2412_);
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_a_2416_);
lean_dec_ref(v___x_2415_);
v___x_2417_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_2410_, v___y_2412_);
if (v___y_2406_ == 0)
{
lean_object* v_a_2418_; 
lean_dec(v___y_2409_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2403_);
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2418_);
lean_dec_ref(v___x_2417_);
v___y_2360_ = v_a_2416_;
v___y_2361_ = v___y_2407_;
v_proof_2362_ = v_a_2418_;
goto v___jp_2359_;
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2420_; 
v_a_2419_ = lean_ctor_get(v___x_2417_, 0);
lean_inc_n(v_a_2419_, 2);
lean_dec_ref(v___x_2417_);
v___x_2420_ = l_Lean_Meta_mkEqOfHEq(v_a_2419_, v___y_2407_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_dec(v_a_2419_);
v___y_2367_ = v___y_2403_;
v___y_2368_ = v___y_2404_;
v___y_2369_ = v_a_2416_;
v___y_2370_ = v___y_2405_;
v___y_2371_ = v___y_2407_;
v___y_2372_ = v___y_2409_;
v___y_2373_ = v___x_2420_;
goto v___jp_2366_;
}
else
{
lean_object* v_a_2421_; uint8_t v___x_2422_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
lean_inc(v_a_2421_);
v___x_2422_ = l_Lean_Exception_isInterrupt(v_a_2421_);
if (v___x_2422_ == 0)
{
uint8_t v___x_2423_; 
lean_inc(v_a_2421_);
v___x_2423_ = l_Lean_Exception_isRuntime(v_a_2421_);
v___y_2377_ = v___y_2403_;
v___y_2378_ = v___y_2404_;
v___y_2379_ = v___y_2411_;
v___y_2380_ = v___y_2413_;
v___y_2381_ = v_a_2419_;
v___y_2382_ = v_a_2421_;
v___y_2383_ = v_a_2416_;
v___y_2384_ = v___y_2405_;
v___y_2385_ = v___y_2407_;
v___y_2386_ = v___y_2412_;
v___y_2387_ = v___y_2409_;
v___y_2388_ = v___x_2420_;
v___y_2389_ = v___y_2414_;
v___y_2390_ = v___x_2423_;
goto v___jp_2376_;
}
else
{
v___y_2377_ = v___y_2403_;
v___y_2378_ = v___y_2404_;
v___y_2379_ = v___y_2411_;
v___y_2380_ = v___y_2413_;
v___y_2381_ = v_a_2419_;
v___y_2382_ = v_a_2421_;
v___y_2383_ = v_a_2416_;
v___y_2384_ = v___y_2405_;
v___y_2385_ = v___y_2407_;
v___y_2386_ = v___y_2412_;
v___y_2387_ = v___y_2409_;
v___y_2388_ = v___x_2420_;
v___y_2389_ = v___y_2414_;
v___y_2390_ = v___x_2422_;
goto v___jp_2376_;
}
}
}
}
v___jp_2424_:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; 
v___x_2438_ = lean_array_get_size(v_a_2437_);
v___x_2439_ = lean_unsigned_to_nat(0u);
v___x_2440_ = lean_nat_dec_eq(v___x_2438_, v___x_2439_);
if (v___x_2440_ == 0)
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v_a_2452_; 
lean_dec_ref(v___y_2435_);
lean_dec_ref(v___y_2430_);
v___x_2441_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
lean_inc(v___y_2433_);
v___x_2442_ = l_Lean_MessageData_ofConstName(v___y_2433_, v___x_2440_);
v___x_2443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2441_);
lean_ctor_set(v___x_2443_, 1, v___x_2442_);
v___x_2444_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_2445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2443_);
lean_ctor_set(v___x_2445_, 1, v___x_2444_);
v___x_2446_ = lean_array_to_list(v_a_2437_);
v___x_2447_ = lean_box(0);
v___x_2448_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_2446_, v___x_2447_);
v___x_2449_ = l_Lean_MessageData_ofList(v___x_2448_);
v___x_2450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2445_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
v___x_2451_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2450_, v___y_2436_, v___y_2431_, v___y_2434_, v___y_2432_);
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
lean_inc(v_a_2452_);
lean_dec_ref(v___x_2451_);
v___y_2138_ = v___y_2425_;
v___y_2139_ = v___y_2426_;
v___y_2140_ = v___y_2427_;
v___y_2141_ = v___y_2433_;
v_a_2142_ = v_a_2452_;
goto v___jp_2137_;
}
else
{
lean_dec_ref(v_a_2437_);
v___y_2403_ = v___y_2425_;
v___y_2404_ = v___y_2426_;
v___y_2405_ = v___y_2427_;
v___y_2406_ = v___y_2429_;
v___y_2407_ = v___y_2428_;
v___y_2408_ = v___y_2430_;
v___y_2409_ = v___y_2433_;
v___y_2410_ = v___y_2435_;
v___y_2411_ = v___y_2436_;
v___y_2412_ = v___y_2431_;
v___y_2413_ = v___y_2434_;
v___y_2414_ = v___y_2432_;
goto v___jp_2402_;
}
}
v___jp_2453_:
{
if (lean_obj_tag(v___y_2466_) == 0)
{
lean_object* v_a_2467_; 
v_a_2467_ = lean_ctor_get(v___y_2466_, 0);
lean_inc(v_a_2467_);
lean_dec_ref_known(v___y_2466_, 1);
v___y_2425_ = v___y_2454_;
v___y_2426_ = v___y_2455_;
v___y_2427_ = v___y_2456_;
v___y_2428_ = v___y_2458_;
v___y_2429_ = v___y_2457_;
v___y_2430_ = v___y_2460_;
v___y_2431_ = v___y_2459_;
v___y_2432_ = v___y_2462_;
v___y_2433_ = v___y_2461_;
v___y_2434_ = v___y_2463_;
v___y_2435_ = v___y_2465_;
v___y_2436_ = v___y_2464_;
v_a_2437_ = v_a_2467_;
goto v___jp_2424_;
}
else
{
lean_object* v_a_2468_; 
lean_dec_ref(v___y_2465_);
lean_dec_ref(v___y_2460_);
v_a_2468_ = lean_ctor_get(v___y_2466_, 0);
lean_inc(v_a_2468_);
lean_dec_ref_known(v___y_2466_, 1);
v___y_2138_ = v___y_2454_;
v___y_2139_ = v___y_2455_;
v___y_2140_ = v___y_2456_;
v___y_2141_ = v___y_2461_;
v_a_2142_ = v_a_2468_;
goto v___jp_2137_;
}
}
v___jp_2469_:
{
lean_object* v___x_2484_; size_t v_sz_2485_; lean_object* v___x_2486_; 
v___x_2484_ = lean_box(0);
v_sz_2485_ = lean_array_size(v___y_2472_);
v___x_2486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___y_2472_, v_sz_2485_, v___y_2478_, v___x_2484_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; uint8_t v___x_2490_; 
lean_dec_ref_known(v___x_2486_, 1);
v___x_2487_ = lean_unsigned_to_nat(0u);
v___x_2488_ = lean_array_get_size(v___y_2472_);
v___x_2489_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_2490_ = lean_nat_dec_lt(v___x_2487_, v___x_2488_);
if (v___x_2490_ == 0)
{
lean_dec_ref(v___y_2472_);
v___y_2425_ = v___y_2470_;
v___y_2426_ = v___y_2471_;
v___y_2427_ = v___y_2473_;
v___y_2428_ = v___y_2475_;
v___y_2429_ = v___y_2474_;
v___y_2430_ = v___y_2476_;
v___y_2431_ = v___y_2481_;
v___y_2432_ = v___y_2483_;
v___y_2433_ = v___y_2477_;
v___y_2434_ = v___y_2482_;
v___y_2435_ = v___y_2479_;
v___y_2436_ = v___y_2480_;
v_a_2437_ = v___x_2489_;
goto v___jp_2424_;
}
else
{
uint8_t v___x_2491_; 
v___x_2491_ = lean_nat_dec_le(v___x_2488_, v___x_2488_);
if (v___x_2491_ == 0)
{
if (v___x_2490_ == 0)
{
lean_dec_ref(v___y_2472_);
v___y_2425_ = v___y_2470_;
v___y_2426_ = v___y_2471_;
v___y_2427_ = v___y_2473_;
v___y_2428_ = v___y_2475_;
v___y_2429_ = v___y_2474_;
v___y_2430_ = v___y_2476_;
v___y_2431_ = v___y_2481_;
v___y_2432_ = v___y_2483_;
v___y_2433_ = v___y_2477_;
v___y_2434_ = v___y_2482_;
v___y_2435_ = v___y_2479_;
v___y_2436_ = v___y_2480_;
v_a_2437_ = v___x_2489_;
goto v___jp_2424_;
}
else
{
size_t v___x_2492_; lean_object* v___x_2493_; 
v___x_2492_ = lean_usize_of_nat(v___x_2488_);
v___x_2493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___y_2472_, v___y_2478_, v___x_2492_, v___x_2489_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
lean_dec_ref(v___y_2472_);
v___y_2454_ = v___y_2470_;
v___y_2455_ = v___y_2471_;
v___y_2456_ = v___y_2473_;
v___y_2457_ = v___y_2474_;
v___y_2458_ = v___y_2475_;
v___y_2459_ = v___y_2481_;
v___y_2460_ = v___y_2476_;
v___y_2461_ = v___y_2477_;
v___y_2462_ = v___y_2483_;
v___y_2463_ = v___y_2482_;
v___y_2464_ = v___y_2480_;
v___y_2465_ = v___y_2479_;
v___y_2466_ = v___x_2493_;
goto v___jp_2453_;
}
}
else
{
size_t v___x_2494_; lean_object* v___x_2495_; 
v___x_2494_ = lean_usize_of_nat(v___x_2488_);
v___x_2495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___y_2472_, v___y_2478_, v___x_2494_, v___x_2489_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
lean_dec_ref(v___y_2472_);
v___y_2454_ = v___y_2470_;
v___y_2455_ = v___y_2471_;
v___y_2456_ = v___y_2473_;
v___y_2457_ = v___y_2474_;
v___y_2458_ = v___y_2475_;
v___y_2459_ = v___y_2481_;
v___y_2460_ = v___y_2476_;
v___y_2461_ = v___y_2477_;
v___y_2462_ = v___y_2483_;
v___y_2463_ = v___y_2482_;
v___y_2464_ = v___y_2480_;
v___y_2465_ = v___y_2479_;
v___y_2466_ = v___x_2495_;
goto v___jp_2453_;
}
}
}
else
{
lean_object* v_a_2496_; 
lean_dec_ref(v___y_2479_);
lean_dec_ref(v___y_2476_);
lean_dec_ref(v___y_2472_);
v_a_2496_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_a_2496_);
lean_dec_ref_known(v___x_2486_, 1);
v___y_2138_ = v___y_2470_;
v___y_2139_ = v___y_2471_;
v___y_2140_ = v___y_2473_;
v___y_2141_ = v___y_2477_;
v_a_2142_ = v_a_2496_;
goto v___jp_2137_;
}
}
v___jp_2497_:
{
lean_object* v___x_2513_; 
lean_inc_ref(v_fst_2507_);
lean_inc_ref(v_e_2074_);
v___x_2513_ = l_Lean_Meta_isExprDefEq(v_e_2074_, v_fst_2507_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; uint8_t v___x_2515_; 
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
lean_inc(v_a_2514_);
lean_dec_ref_known(v___x_2513_, 1);
v___x_2515_ = lean_unbox(v_a_2514_);
lean_dec(v_a_2514_);
if (v___x_2515_ == 0)
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v_a_2530_; 
lean_dec_ref(v_snd_2508_);
lean_dec_ref(v___y_2505_);
lean_dec_ref(v___y_2500_);
v___x_2516_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_2517_ = l_Lean_MessageData_ofExpr(v_fst_2507_);
v___x_2518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2516_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_2520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2518_);
lean_ctor_set(v___x_2520_, 1, v___x_2519_);
lean_inc(v___y_2503_);
v___x_2521_ = l_Lean_MessageData_ofConstName(v___y_2503_, v___y_2499_);
v___x_2522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2520_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
v___x_2523_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_2524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2522_);
lean_ctor_set(v___x_2524_, 1, v___x_2523_);
v___x_2525_ = l_Lean_MessageData_ofExpr(v_e_2074_);
v___x_2526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2524_);
lean_ctor_set(v___x_2526_, 1, v___x_2525_);
v___x_2527_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_2528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2526_);
lean_ctor_set(v___x_2528_, 1, v___x_2527_);
v___x_2529_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2528_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_a_2530_);
lean_dec_ref(v___x_2529_);
v___y_2138_ = v___y_2498_;
v___y_2139_ = v___y_2499_;
v___y_2140_ = v___y_2501_;
v___y_2141_ = v___y_2503_;
v_a_2142_ = v_a_2530_;
goto v___jp_2137_;
}
else
{
lean_dec_ref(v_fst_2507_);
lean_dec_ref(v_e_2074_);
v___y_2470_ = v___y_2498_;
v___y_2471_ = v___y_2499_;
v___y_2472_ = v___y_2500_;
v___y_2473_ = v___y_2501_;
v___y_2474_ = v_fst_2506_;
v___y_2475_ = v___y_2502_;
v___y_2476_ = v_snd_2508_;
v___y_2477_ = v___y_2503_;
v___y_2478_ = v___y_2504_;
v___y_2479_ = v___y_2505_;
v___y_2480_ = v___y_2509_;
v___y_2481_ = v___y_2510_;
v___y_2482_ = v___y_2511_;
v___y_2483_ = v___y_2512_;
goto v___jp_2469_;
}
}
else
{
lean_object* v_a_2531_; 
lean_dec_ref(v_snd_2508_);
lean_dec_ref(v_fst_2507_);
lean_dec_ref(v___y_2505_);
lean_dec_ref(v___y_2500_);
lean_dec_ref(v_e_2074_);
v_a_2531_ = lean_ctor_get(v___x_2513_, 0);
lean_inc(v_a_2531_);
lean_dec_ref_known(v___x_2513_, 1);
v___y_2138_ = v___y_2498_;
v___y_2139_ = v___y_2499_;
v___y_2140_ = v___y_2501_;
v___y_2141_ = v___y_2503_;
v_a_2142_ = v_a_2531_;
goto v___jp_2137_;
}
}
v___jp_2533_:
{
uint8_t v___x_2535_; 
v___x_2535_ = 1;
if (v___y_2534_ == 0)
{
lean_object* v___x_2536_; lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2707_; 
v___x_2536_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(v_e_2074_, v_a_2078_);
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2539_ = v___x_2536_;
v_isShared_2540_ = v_isSharedCheck_2707_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2536_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2707_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
uint8_t v___x_2541_; 
v___x_2541_ = lean_unbox(v_a_2537_);
lean_dec(v_a_2537_);
if (v___x_2541_ == 0)
{
lean_object* v_options_2542_; uint8_t v_hasTrace_2543_; 
lean_del_object(v___x_2539_);
lean_dec(v_altIdx_2073_);
v_options_2542_ = lean_ctor_get(v_a_2077_, 1);
v_hasTrace_2543_ = lean_ctor_get_uint8(v_options_2542_, sizeof(void*)*1);
if (v_hasTrace_2543_ == 0)
{
v___y_2355_ = v___x_2535_;
goto v___jp_2354_;
}
else
{
lean_object* v_toCold_2544_; lean_object* v_inheritedTraceOptions_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; uint8_t v___x_2548_; 
v_toCold_2544_ = lean_ctor_get(v_a_2077_, 0);
v_inheritedTraceOptions_2545_ = lean_ctor_get(v_toCold_2544_, 4);
v___x_2546_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2547_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2548_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2545_, v_options_2542_, v___x_2547_);
if (v___x_2548_ == 0)
{
v___y_2355_ = v___x_2535_;
goto v___jp_2354_;
}
else
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2549_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__15, &l_Lean_Meta_rwMatcher___closed__15_once, _init_l_Lean_Meta_rwMatcher___closed__15);
lean_inc_ref(v_e_2074_);
v___x_2550_ = l_Lean_indentExpr(v_e_2074_);
v___x_2551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2549_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
v___x_2552_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2546_, v___x_2551_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_dec_ref_known(v___x_2552_, 1);
v___y_2355_ = v___x_2535_;
goto v___jp_2354_;
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec_ref(v_e_2074_);
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2552_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2552_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
}
}
else
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2561_ = l_Lean_Expr_getAppFn(v_e_2074_);
v___x_2562_ = l_Lean_Expr_constName_x21(v___x_2561_);
lean_inc(v_a_2078_);
lean_inc_ref(v_a_2077_);
lean_inc(v_a_2076_);
lean_inc_ref(v_a_2075_);
lean_inc(v___x_2562_);
v___x_2563_ = lean_get_congr_match_equations_for(v___x_2562_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2565_; uint8_t v___x_2566_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_a_2564_);
lean_dec_ref_known(v___x_2563_, 1);
v___x_2565_ = lean_array_get_size(v_a_2564_);
v___x_2566_ = lean_nat_dec_lt(v_altIdx_2073_, v___x_2565_);
if (v___x_2566_ == 0)
{
lean_object* v_options_2567_; uint8_t v_hasTrace_2568_; 
lean_dec(v_a_2564_);
lean_dec_ref(v___x_2561_);
v_options_2567_ = lean_ctor_get(v_a_2077_, 1);
v_hasTrace_2568_ = lean_ctor_get_uint8(v_options_2567_, sizeof(void*)*1);
if (v_hasTrace_2568_ == 0)
{
lean_dec(v___x_2562_);
lean_del_object(v___x_2539_);
lean_dec(v_altIdx_2073_);
v___y_2350_ = v___x_2535_;
goto v___jp_2349_;
}
else
{
lean_object* v_toCold_2569_; lean_object* v_inheritedTraceOptions_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; 
v_toCold_2569_ = lean_ctor_get(v_a_2077_, 0);
v_inheritedTraceOptions_2570_ = lean_ctor_get(v_toCold_2569_, 4);
v___x_2571_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2572_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2573_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2570_, v_options_2567_, v___x_2572_);
if (v___x_2573_ == 0)
{
lean_dec(v___x_2562_);
lean_del_object(v___x_2539_);
lean_dec(v_altIdx_2073_);
v___y_2350_ = v___x_2535_;
goto v___jp_2349_;
}
else
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2574_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__17, &l_Lean_Meta_rwMatcher___closed__17_once, _init_l_Lean_Meta_rwMatcher___closed__17);
v___x_2575_ = l_Nat_reprFast(v_altIdx_2073_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set_tag(v___x_2539_, 3);
lean_ctor_set(v___x_2539_, 0, v___x_2575_);
v___x_2577_ = v___x_2539_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2575_);
v___x_2577_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2578_ = l_Lean_MessageData_ofFormat(v___x_2577_);
v___x_2579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2574_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
v___x_2580_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__19, &l_Lean_Meta_rwMatcher___closed__19_once, _init_l_Lean_Meta_rwMatcher___closed__19);
v___x_2581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2579_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
v___x_2582_ = l_Nat_reprFast(v___x_2565_);
v___x_2583_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2582_);
v___x_2584_ = l_Lean_MessageData_ofFormat(v___x_2583_);
v___x_2585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2581_);
lean_ctor_set(v___x_2585_, 1, v___x_2584_);
v___x_2586_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__21, &l_Lean_Meta_rwMatcher___closed__21_once, _init_l_Lean_Meta_rwMatcher___closed__21);
v___x_2587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2585_);
lean_ctor_set(v___x_2587_, 1, v___x_2586_);
v___x_2588_ = l_Lean_MessageData_ofConstName(v___x_2562_, v___x_2566_);
v___x_2589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2587_);
lean_ctor_set(v___x_2589_, 1, v___x_2588_);
v___x_2590_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2571_, v___x_2589_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_dec_ref_known(v___x_2590_, 1);
v___y_2350_ = v___x_2535_;
goto v___jp_2349_;
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
lean_dec_ref(v_e_2074_);
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2590_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2590_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
}
}
}
else
{
lean_object* v_options_2600_; lean_object* v_toCold_2601_; uint8_t v_hasTrace_2602_; lean_object* v_nargs_2603_; lean_object* v___x_2604_; lean_object* v___f_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v_dummy_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
lean_dec(v___x_2562_);
lean_del_object(v___x_2539_);
v_options_2600_ = lean_ctor_get(v_a_2077_, 1);
v_toCold_2601_ = lean_ctor_get(v_a_2077_, 0);
v_hasTrace_2602_ = lean_ctor_get_uint8(v_options_2600_, sizeof(void*)*1);
v_nargs_2603_ = l_Lean_Expr_getAppNumArgs(v_e_2074_);
v___x_2604_ = lean_box(v___x_2535_);
lean_inc_ref_n(v_e_2074_, 2);
v___f_2605_ = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2605_, 0, v_e_2074_);
lean_closure_set(v___f_2605_, 1, v___x_2604_);
v___x_2606_ = lean_array_get(v___x_2532_, v_a_2564_, v_altIdx_2073_);
lean_dec(v_altIdx_2073_);
lean_dec(v_a_2564_);
v___x_2607_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2608_ = l_Lean_Expr_constLevels_x21(v___x_2561_);
lean_dec_ref(v___x_2561_);
lean_inc(v___x_2606_);
v___x_2609_ = l_Lean_mkConst(v___x_2606_, v___x_2608_);
v_dummy_2610_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__22, &l_Lean_Meta_rwMatcher___closed__22_once, _init_l_Lean_Meta_rwMatcher___closed__22);
lean_inc(v_nargs_2603_);
v___x_2611_ = lean_mk_array(v_nargs_2603_, v_dummy_2610_);
v___x_2612_ = lean_unsigned_to_nat(1u);
v___x_2613_ = lean_nat_sub(v_nargs_2603_, v___x_2612_);
lean_dec(v_nargs_2603_);
v___x_2614_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2074_, v___x_2611_, v___x_2613_);
v___x_2615_ = l_Lean_mkAppN(v___x_2609_, v___x_2614_);
lean_dec_ref(v___x_2614_);
if (v_hasTrace_2602_ == 0)
{
lean_object* v___x_2616_; 
lean_inc(v_a_2078_);
lean_inc_ref(v_a_2077_);
lean_inc(v_a_2076_);
lean_inc_ref(v_a_2075_);
lean_inc_ref(v___x_2615_);
v___x_2616_ = lean_infer_type(v___x_2615_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; uint8_t v___x_2618_; lean_object* v___x_2619_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v___x_2616_, 1);
v___x_2618_ = 0;
v___x_2619_ = l_Lean_Meta_forallMetaTelescope(v_a_2617_, v___x_2618_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
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
lean_dec_ref(v_e_2074_);
v___x_2640_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
lean_inc(v___x_2606_);
v___x_2641_ = l_Lean_MessageData_ofConstName(v___x_2606_, v___y_2534_);
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
v___x_2647_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2646_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_a_2648_);
lean_dec_ref(v___x_2647_);
v___y_2138_ = v___f_2605_;
v___y_2139_ = v___y_2534_;
v___y_2140_ = v___x_2607_;
v___y_2141_ = v___x_2606_;
v_a_2142_ = v_a_2648_;
goto v___jp_2137_;
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
v___y_2498_ = v___f_2605_;
v___y_2499_ = v___y_2534_;
v___y_2500_ = v___x_2633_;
v___y_2501_ = v___x_2607_;
v___y_2502_ = v___x_2535_;
v___y_2503_ = v___x_2606_;
v___y_2504_ = v___x_2632_;
v___y_2505_ = v___x_2630_;
v_fst_2506_ = v___y_2534_;
v_fst_2507_ = v___x_2652_;
v_snd_2508_ = v___x_2653_;
v___y_2509_ = v_a_2075_;
v___y_2510_ = v_a_2076_;
v___y_2511_ = v_a_2077_;
v___y_2512_ = v_a_2078_;
goto v___jp_2497_;
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
v___y_2498_ = v___f_2605_;
v___y_2499_ = v___y_2534_;
v___y_2500_ = v___x_2633_;
v___y_2501_ = v___x_2607_;
v___y_2502_ = v___x_2535_;
v___y_2503_ = v___x_2606_;
v___y_2504_ = v___x_2632_;
v___y_2505_ = v___x_2630_;
v_fst_2506_ = v___x_2535_;
v_fst_2507_ = v___x_2656_;
v_snd_2508_ = v___x_2657_;
v___y_2509_ = v_a_2075_;
v___y_2510_ = v_a_2076_;
v___y_2511_ = v_a_2077_;
v___y_2512_ = v_a_2078_;
goto v___jp_2497_;
}
}
}
}
else
{
lean_object* v_a_2661_; 
lean_dec_ref(v___x_2615_);
lean_dec_ref(v_e_2074_);
v_a_2661_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_a_2661_);
lean_dec_ref_known(v___x_2619_, 1);
v___y_2138_ = v___f_2605_;
v___y_2139_ = v___y_2534_;
v___y_2140_ = v___x_2607_;
v___y_2141_ = v___x_2606_;
v_a_2142_ = v_a_2661_;
goto v___jp_2137_;
}
}
else
{
lean_object* v_a_2662_; 
lean_dec_ref(v___x_2615_);
lean_dec_ref(v_e_2074_);
v_a_2662_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2662_);
lean_dec_ref_known(v___x_2616_, 1);
v___y_2138_ = v___f_2605_;
v___y_2139_ = v___y_2534_;
v___y_2140_ = v___x_2607_;
v___y_2141_ = v___x_2606_;
v_a_2142_ = v_a_2662_;
goto v___jp_2137_;
}
}
else
{
lean_object* v_inheritedTraceOptions_2663_; lean_object* v___x_2664_; lean_object* v___f_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; uint8_t v___x_2668_; 
v_inheritedTraceOptions_2663_ = lean_ctor_get(v_toCold_2601_, 4);
v___x_2664_ = lean_box(v___y_2534_);
lean_inc_ref(v_e_2074_);
lean_inc(v___x_2606_);
v___f_2665_ = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__1___boxed), 9, 3);
lean_closure_set(v___f_2665_, 0, v___x_2606_);
lean_closure_set(v___f_2665_, 1, v___x_2664_);
lean_closure_set(v___f_2665_, 2, v_e_2074_);
v___x_2666_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1));
v___x_2667_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2668_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2663_, v_options_2600_, v___x_2667_);
if (v___x_2668_ == 0)
{
lean_object* v___x_2669_; uint8_t v___x_2670_; 
v___x_2669_ = l_Lean_trace_profiler;
v___x_2670_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_options_2600_, v___x_2669_);
if (v___x_2670_ == 0)
{
lean_object* v___x_2671_; 
lean_dec_ref(v___f_2665_);
lean_inc(v_a_2078_);
lean_inc_ref(v_a_2077_);
lean_inc(v_a_2076_);
lean_inc_ref(v_a_2075_);
lean_inc_ref(v___x_2615_);
v___x_2671_ = lean_infer_type(v___x_2615_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; uint8_t v___x_2673_; lean_object* v___x_2674_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_a_2672_);
lean_dec_ref_known(v___x_2671_, 1);
v___x_2673_ = 0;
v___x_2674_ = l_Lean_Meta_forallMetaTelescope(v_a_2672_, v___x_2673_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v_a_2675_; lean_object* v_snd_2676_; 
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
lean_inc(v_a_2675_);
lean_dec_ref_known(v___x_2674_, 1);
v_snd_2676_ = lean_ctor_get(v_a_2675_, 1);
lean_inc(v_snd_2676_);
if (v___x_2668_ == 0)
{
lean_object* v_fst_2677_; lean_object* v_snd_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v_fst_2677_ = lean_ctor_get(v_a_2675_, 0);
lean_inc(v_fst_2677_);
lean_dec(v_a_2675_);
v_snd_2678_ = lean_ctor_get(v_snd_2676_, 1);
lean_inc(v_snd_2678_);
lean_dec(v_snd_2676_);
v___x_2679_ = lean_box(0);
lean_inc(v___x_2606_);
v___x_2680_ = l_Lean_Meta_rwMatcher___lam__4(v___x_2535_, v___x_2615_, v_fst_2677_, v___x_2606_, v_e_2074_, v___y_2534_, v_snd_2678_, v___x_2679_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
lean_dec(v_snd_2678_);
v___y_2146_ = v___f_2605_;
v___y_2147_ = v___y_2534_;
v___y_2148_ = v___x_2607_;
v___y_2149_ = v___x_2606_;
v___y_2150_ = v___x_2680_;
goto v___jp_2145_;
}
else
{
lean_object* v_fst_2681_; lean_object* v_snd_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2695_; 
v_fst_2681_ = lean_ctor_get(v_a_2675_, 0);
lean_inc(v_fst_2681_);
lean_dec(v_a_2675_);
v_snd_2682_ = lean_ctor_get(v_snd_2676_, 1);
v_isSharedCheck_2695_ = !lean_is_exclusive(v_snd_2676_);
if (v_isSharedCheck_2695_ == 0)
{
lean_object* v_unused_2696_; 
v_unused_2696_ = lean_ctor_get(v_snd_2676_, 0);
lean_dec(v_unused_2696_);
v___x_2684_ = v_snd_2676_;
v_isShared_2685_ = v_isSharedCheck_2695_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_snd_2682_);
lean_dec(v_snd_2676_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2695_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2689_; 
v___x_2686_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2682_);
v___x_2687_ = l_Lean_indentExpr(v_snd_2682_);
if (v_isShared_2685_ == 0)
{
lean_ctor_set_tag(v___x_2684_, 7);
lean_ctor_set(v___x_2684_, 1, v___x_2687_);
lean_ctor_set(v___x_2684_, 0, v___x_2686_);
v___x_2689_ = v___x_2684_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2686_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v___x_2687_);
v___x_2689_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
lean_object* v___x_2690_; 
v___x_2690_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2607_, v___x_2689_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v_a_2691_; lean_object* v___x_2692_; 
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_a_2691_);
lean_dec_ref_known(v___x_2690_, 1);
lean_inc(v___x_2606_);
v___x_2692_ = l_Lean_Meta_rwMatcher___lam__4(v___x_2535_, v___x_2615_, v_fst_2681_, v___x_2606_, v_e_2074_, v___y_2534_, v_snd_2682_, v_a_2691_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
lean_dec(v_snd_2682_);
v___y_2146_ = v___f_2605_;
v___y_2147_ = v___y_2534_;
v___y_2148_ = v___x_2607_;
v___y_2149_ = v___x_2606_;
v___y_2150_ = v___x_2692_;
goto v___jp_2145_;
}
else
{
lean_object* v_a_2693_; 
lean_dec(v_snd_2682_);
lean_dec(v_fst_2681_);
lean_dec_ref(v___x_2615_);
lean_dec_ref(v_e_2074_);
v_a_2693_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_a_2693_);
lean_dec_ref_known(v___x_2690_, 1);
v___y_2138_ = v___f_2605_;
v___y_2139_ = v___y_2534_;
v___y_2140_ = v___x_2607_;
v___y_2141_ = v___x_2606_;
v_a_2142_ = v_a_2693_;
goto v___jp_2137_;
}
}
}
}
}
else
{
lean_object* v_a_2697_; 
lean_dec_ref(v___x_2615_);
lean_dec_ref(v_e_2074_);
v_a_2697_ = lean_ctor_get(v___x_2674_, 0);
lean_inc(v_a_2697_);
lean_dec_ref_known(v___x_2674_, 1);
v___y_2138_ = v___f_2605_;
v___y_2139_ = v___y_2534_;
v___y_2140_ = v___x_2607_;
v___y_2141_ = v___x_2606_;
v_a_2142_ = v_a_2697_;
goto v___jp_2137_;
}
}
else
{
lean_object* v_a_2698_; 
lean_dec_ref(v___x_2615_);
lean_dec_ref(v_e_2074_);
v_a_2698_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_a_2698_);
lean_dec_ref_known(v___x_2671_, 1);
v___y_2138_ = v___f_2605_;
v___y_2139_ = v___y_2534_;
v___y_2140_ = v___x_2607_;
v___y_2141_ = v___x_2606_;
v_a_2142_ = v_a_2698_;
goto v___jp_2137_;
}
}
else
{
lean_inc(v___x_2606_);
lean_inc_ref(v___x_2615_);
v___y_2270_ = v___f_2665_;
v___y_2271_ = v___x_2615_;
v___y_2272_ = v___y_2534_;
v___y_2273_ = v___x_2535_;
v___y_2274_ = v___x_2606_;
v___y_2275_ = v_inheritedTraceOptions_2663_;
v___y_2276_ = v___f_2605_;
v___y_2277_ = v___x_2615_;
v___y_2278_ = v___y_2534_;
v___y_2279_ = v___x_2607_;
v___y_2280_ = v___x_2535_;
v___y_2281_ = v___x_2666_;
v___y_2282_ = v___x_2606_;
v___y_2283_ = v___x_2668_;
v___y_2284_ = v_options_2600_;
goto v___jp_2269_;
}
}
else
{
lean_inc(v___x_2606_);
lean_inc_ref(v___x_2615_);
v___y_2270_ = v___f_2665_;
v___y_2271_ = v___x_2615_;
v___y_2272_ = v___y_2534_;
v___y_2273_ = v___x_2535_;
v___y_2274_ = v___x_2606_;
v___y_2275_ = v_inheritedTraceOptions_2663_;
v___y_2276_ = v___f_2605_;
v___y_2277_ = v___x_2615_;
v___y_2278_ = v___y_2534_;
v___y_2279_ = v___x_2607_;
v___y_2280_ = v___x_2535_;
v___y_2281_ = v___x_2666_;
v___y_2282_ = v___x_2606_;
v___y_2283_ = v___x_2668_;
v___y_2284_ = v_options_2600_;
goto v___jp_2269_;
}
}
}
}
else
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
lean_dec(v___x_2562_);
lean_dec_ref(v___x_2561_);
lean_del_object(v___x_2539_);
lean_dec_ref(v_e_2074_);
lean_dec(v_altIdx_2073_);
v_a_2699_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2563_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2563_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2702_ == 0)
{
v___x_2704_ = v___x_2701_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_a_2699_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
}
}
else
{
lean_object* v___x_2708_; 
lean_dec(v_altIdx_2073_);
v___x_2708_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(v_e_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2718_; 
v_a_2709_ = lean_ctor_get(v___x_2708_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2711_ = v___x_2708_;
v_isShared_2712_ = v_isSharedCheck_2718_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2708_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2718_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2716_; 
v___x_2713_ = lean_box(0);
v___x_2714_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2714_, 0, v_a_2709_);
lean_ctor_set(v___x_2714_, 1, v___x_2713_);
lean_ctor_set_uint8(v___x_2714_, sizeof(void*)*2, v___x_2535_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 0, v___x_2714_);
v___x_2716_ = v___x_2711_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2714_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
v_a_2719_ = lean_ctor_get(v___x_2708_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2708_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2708_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___boxed(lean_object* v_altIdx_2731_, lean_object* v_e_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l_Lean_Meta_rwMatcher(v_altIdx_2731_, v_e_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
lean_dec(v_a_2736_);
lean_dec_ref(v_a_2735_);
lean_dec(v_a_2734_);
lean_dec_ref(v_a_2733_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(lean_object* v_mvarId_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_mvarId_2739_, v___y_2741_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___boxed(lean_object* v_mvarId_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(v_mvarId_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v_mvarId_2746_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5(lean_object* v_00_u03b1_2753_, lean_object* v_msg_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v_msg_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___boxed(lean_object* v_00_u03b1_2761_, lean_object* v_msg_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5(v_00_u03b1_2761_, v_msg_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14(lean_object* v_00_u03b1_2769_, lean_object* v_x_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(v_x_2770_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___boxed(lean_object* v_00_u03b1_2777_, lean_object* v_x_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14(v_00_u03b1_2777_, v_x_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12(lean_object* v_inst_2785_, lean_object* v_a_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v___x_2792_; 
v___x_2792_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(v_a_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___boxed(lean_object* v_inst_2793_, lean_object* v_a_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v_res_2800_; 
v_res_2800_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12(v_inst_2793_, v_a_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
return v_res_2800_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(lean_object* v_00_u03b2_2801_, lean_object* v_x_2802_, lean_object* v_x_2803_){
_start:
{
uint8_t v___x_2804_; 
v___x_2804_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_x_2802_, v_x_2803_);
return v___x_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2805_, lean_object* v_x_2806_, lean_object* v_x_2807_){
_start:
{
uint8_t v_res_2808_; lean_object* v_r_2809_; 
v_res_2808_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(v_00_u03b2_2805_, v_x_2806_, v_x_2807_);
lean_dec(v_x_2807_);
lean_dec_ref(v_x_2806_);
v_r_2809_ = lean_box(v_res_2808_);
return v_r_2809_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5(lean_object* v_00_u03b2_2810_, lean_object* v_x_2811_, size_t v_x_2812_, lean_object* v_x_2813_){
_start:
{
uint8_t v___x_2814_; 
v___x_2814_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_2811_, v_x_2812_, v_x_2813_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b2_2815_, lean_object* v_x_2816_, lean_object* v_x_2817_, lean_object* v_x_2818_){
_start:
{
size_t v_x_88171__boxed_2819_; uint8_t v_res_2820_; lean_object* v_r_2821_; 
v_x_88171__boxed_2819_ = lean_unbox_usize(v_x_2817_);
lean_dec(v_x_2817_);
v_res_2820_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5(v_00_u03b2_2815_, v_x_2816_, v_x_88171__boxed_2819_, v_x_2818_);
lean_dec(v_x_2818_);
lean_dec_ref(v_x_2816_);
v_r_2821_ = lean_box(v_res_2820_);
return v_r_2821_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18(lean_object* v_00_u03b2_2822_, lean_object* v_keys_2823_, lean_object* v_vals_2824_, lean_object* v_heq_2825_, lean_object* v_i_2826_, lean_object* v_k_2827_){
_start:
{
uint8_t v___x_2828_; 
v___x_2828_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(v_keys_2823_, v_i_2826_, v_k_2827_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___boxed(lean_object* v_00_u03b2_2829_, lean_object* v_keys_2830_, lean_object* v_vals_2831_, lean_object* v_heq_2832_, lean_object* v_i_2833_, lean_object* v_k_2834_){
_start:
{
uint8_t v_res_2835_; lean_object* v_r_2836_; 
v_res_2835_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18(v_00_u03b2_2829_, v_keys_2830_, v_vals_2831_, v_heq_2832_, v_i_2833_, v_k_2834_);
lean_dec(v_k_2834_);
lean_dec_ref(v_vals_2831_);
lean_dec_ref(v_keys_2830_);
v_r_2836_ = lean_box(v_res_2835_);
return v_r_2836_;
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
