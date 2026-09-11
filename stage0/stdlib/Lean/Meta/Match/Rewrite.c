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
uint8_t v___x_83903__boxed_537_; lean_object* v_res_538_; 
v___x_83903__boxed_537_ = lean_unbox(v___x_530_);
v_res_538_ = l_Lean_Meta_rwMatcher___lam__0(v_e_529_, v___x_83903__boxed_537_, v_____r_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
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
uint8_t v___y_83945__boxed_571_; lean_object* v_res_572_; 
v___y_83945__boxed_571_ = lean_unbox(v___y_563_);
v_res_572_ = l_Lean_Meta_rwMatcher___lam__1(v___x_562_, v___y_83945__boxed_571_, v_e_564_, v_x_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
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
lean_object* v___x_597_; lean_object* v_env_598_; lean_object* v___x_599_; lean_object* v_toCold_600_; lean_object* v_mctx_601_; lean_object* v_lctx_602_; lean_object* v_options_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_597_ = lean_st_ref_get(v___y_595_);
v_env_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc_ref(v_env_598_);
lean_dec(v___x_597_);
v___x_599_ = lean_st_ref_get(v___y_593_);
v_toCold_600_ = lean_ctor_get(v___y_594_, 0);
v_mctx_601_ = lean_ctor_get(v___x_599_, 0);
lean_inc_ref(v_mctx_601_);
lean_dec(v___x_599_);
v_lctx_602_ = lean_ctor_get(v___y_592_, 2);
v_options_603_ = lean_ctor_get(v_toCold_600_, 2);
lean_inc_ref(v_options_603_);
lean_inc_ref(v_lctx_602_);
v___x_604_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_604_, 0, v_env_598_);
lean_ctor_set(v___x_604_, 1, v_mctx_601_);
lean_ctor_set(v___x_604_, 2, v_lctx_602_);
lean_ctor_set(v___x_604_, 3, v_options_603_);
v___x_605_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v_msgData_591_);
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
v_ref_620_ = lean_ctor_get(v___y_617_, 2);
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(lean_object* v_keys_638_, lean_object* v_i_639_, lean_object* v_k_640_){
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
return v___x_642_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg___boxed(lean_object* v_keys_648_, lean_object* v_i_649_, lean_object* v_k_650_){
_start:
{
uint8_t v_res_651_; lean_object* v_r_652_; 
v_res_651_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(v_keys_648_, v_i_649_, v_k_650_);
lean_dec(v_k_650_);
lean_dec_ref(v_keys_648_);
v_r_652_ = lean_box(v_res_651_);
return v_r_652_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(lean_object* v_x_653_, size_t v_x_654_, lean_object* v_x_655_){
_start:
{
if (lean_obj_tag(v_x_653_) == 0)
{
lean_object* v_es_656_; lean_object* v___x_657_; size_t v___x_658_; size_t v___x_659_; lean_object* v_j_660_; lean_object* v___x_661_; 
v_es_656_ = lean_ctor_get(v_x_653_, 0);
v___x_657_ = lean_box(2);
v___x_658_ = ((size_t)31ULL);
v___x_659_ = lean_usize_land(v_x_654_, v___x_658_);
v_j_660_ = lean_usize_to_nat(v___x_659_);
v___x_661_ = lean_array_get_borrowed(v___x_657_, v_es_656_, v_j_660_);
lean_dec(v_j_660_);
switch(lean_obj_tag(v___x_661_))
{
case 0:
{
lean_object* v_key_662_; uint8_t v___x_663_; 
v_key_662_ = lean_ctor_get(v___x_661_, 0);
v___x_663_ = l_Lean_instBEqMVarId_beq(v_x_655_, v_key_662_);
return v___x_663_;
}
case 1:
{
lean_object* v_node_664_; size_t v___x_665_; size_t v___x_666_; 
v_node_664_ = lean_ctor_get(v___x_661_, 0);
v___x_665_ = ((size_t)5ULL);
v___x_666_ = lean_usize_shift_right(v_x_654_, v___x_665_);
v_x_653_ = v_node_664_;
v_x_654_ = v___x_666_;
goto _start;
}
default: 
{
uint8_t v___x_668_; 
v___x_668_ = 0;
return v___x_668_;
}
}
}
else
{
lean_object* v_ks_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v_ks_669_ = lean_ctor_get(v_x_653_, 0);
v___x_670_ = lean_unsigned_to_nat(0u);
v___x_671_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(v_ks_669_, v___x_670_, v_x_655_);
return v___x_671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_672_, lean_object* v_x_673_, lean_object* v_x_674_){
_start:
{
size_t v_x_84078__boxed_675_; uint8_t v_res_676_; lean_object* v_r_677_; 
v_x_84078__boxed_675_ = lean_unbox_usize(v_x_673_);
lean_dec(v_x_673_);
v_res_676_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_672_, v_x_84078__boxed_675_, v_x_674_);
lean_dec(v_x_674_);
lean_dec_ref(v_x_672_);
v_r_677_ = lean_box(v_res_676_);
return v_r_677_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(lean_object* v_x_678_, lean_object* v_x_679_){
_start:
{
uint64_t v___x_680_; size_t v___x_681_; uint8_t v___x_682_; 
v___x_680_ = l_Lean_instHashableMVarId_hash(v_x_679_);
v___x_681_ = lean_uint64_to_usize(v___x_680_);
v___x_682_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_678_, v___x_681_, v_x_679_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg___boxed(lean_object* v_x_683_, lean_object* v_x_684_){
_start:
{
uint8_t v_res_685_; lean_object* v_r_686_; 
v_res_685_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_x_683_, v_x_684_);
lean_dec(v_x_684_);
lean_dec_ref(v_x_683_);
v_r_686_ = lean_box(v_res_685_);
return v_r_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(lean_object* v_mvarId_687_, lean_object* v___y_688_){
_start:
{
lean_object* v___x_690_; lean_object* v_mctx_691_; lean_object* v_eAssignment_692_; uint8_t v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_690_ = lean_st_ref_get(v___y_688_);
v_mctx_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc_ref(v_mctx_691_);
lean_dec(v___x_690_);
v_eAssignment_692_ = lean_ctor_get(v_mctx_691_, 8);
lean_inc_ref(v_eAssignment_692_);
lean_dec_ref(v_mctx_691_);
v___x_693_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_eAssignment_692_, v_mvarId_687_);
lean_dec_ref(v_eAssignment_692_);
v___x_694_ = lean_box(v___x_693_);
v___x_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg___boxed(lean_object* v_mvarId_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_mvarId_696_, v___y_697_);
lean_dec(v___y_697_);
lean_dec(v_mvarId_696_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(lean_object* v_as_700_, size_t v_i_701_, size_t v_stop_702_, lean_object* v_b_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_a_710_; uint8_t v___x_714_; 
v___x_714_ = lean_usize_dec_eq(v_i_701_, v_stop_702_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; lean_object* v___x_718_; 
v___x_715_ = lean_array_uget_borrowed(v_as_700_, v_i_701_);
v___x_718_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v___x_715_, v___y_705_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; uint8_t v___x_720_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_718_, 1);
v___x_720_ = lean_unbox(v_a_719_);
lean_dec(v_a_719_);
if (v___x_720_ == 0)
{
goto v___jp_716_;
}
else
{
v_a_710_ = v_b_703_;
goto v___jp_709_;
}
}
else
{
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_721_; uint8_t v___x_722_; 
v_a_721_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_721_);
lean_dec_ref_known(v___x_718_, 1);
v___x_722_ = lean_unbox(v_a_721_);
lean_dec(v_a_721_);
if (v___x_722_ == 0)
{
v_a_710_ = v_b_703_;
goto v___jp_709_;
}
else
{
goto v___jp_716_;
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec_ref(v_b_703_);
v_a_723_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_718_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_718_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
v___jp_716_:
{
lean_object* v___x_717_; 
lean_inc(v___x_715_);
v___x_717_ = lean_array_push(v_b_703_, v___x_715_);
v_a_710_ = v___x_717_;
goto v___jp_709_;
}
}
else
{
lean_object* v___x_731_; 
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v_b_703_);
return v___x_731_;
}
v___jp_709_:
{
size_t v___x_711_; size_t v___x_712_; 
v___x_711_ = ((size_t)1ULL);
v___x_712_ = lean_usize_add(v_i_701_, v___x_711_);
v_i_701_ = v___x_712_;
v_b_703_ = v_a_710_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8___boxed(lean_object* v_as_732_, lean_object* v_i_733_, lean_object* v_stop_734_, lean_object* v_b_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
size_t v_i_boxed_741_; size_t v_stop_boxed_742_; lean_object* v_res_743_; 
v_i_boxed_741_ = lean_unbox_usize(v_i_733_);
lean_dec(v_i_733_);
v_stop_boxed_742_ = lean_unbox_usize(v_stop_734_);
lean_dec(v_stop_734_);
v_res_743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v_as_732_, v_i_boxed_741_, v_stop_boxed_742_, v_b_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec_ref(v_as_732_);
return v_res_743_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__0));
v___x_746_ = l_Lean_stringToMessageData(v___x_745_);
return v___x_746_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__2));
v___x_749_ = l_Lean_stringToMessageData(v___x_748_);
return v___x_749_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__4));
v___x_752_ = l_Lean_stringToMessageData(v___x_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(lean_object* v_as_753_, size_t v_sz_754_, size_t v_i_755_, lean_object* v_b_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v_a_763_; uint8_t v___x_767_; 
v___x_767_ = lean_usize_dec_lt(v_i_755_, v_sz_754_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; 
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v_b_756_);
return v___x_768_;
}
else
{
lean_object* v_a_769_; lean_object* v___x_770_; 
v_a_769_ = lean_array_uget_borrowed(v_as_753_, v_i_755_);
v___x_770_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_a_769_, v___y_758_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_772_; lean_object* v___y_774_; lean_object* v___y_776_; lean_object* v___y_777_; uint8_t v___y_778_; lean_object* v___y_794_; lean_object* v___y_796_; lean_object* v___y_797_; uint8_t v___y_798_; lean_object* v___y_814_; uint8_t v___x_815_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref_known(v___x_770_, 1);
v___x_772_ = lean_box(0);
v___x_815_ = lean_unbox(v_a_771_);
lean_dec(v_a_771_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; 
lean_inc(v_a_769_);
v___x_816_ = l_Lean_MVarId_getType(v_a_769_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; uint8_t v___x_818_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc_n(v_a_817_, 2);
lean_dec_ref_known(v___x_816_, 1);
v___x_818_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_a_817_);
if (v___x_818_ == 0)
{
uint8_t v___x_819_; 
v___x_819_ = l_Lean_Expr_isEq(v_a_817_);
if (v___x_819_ == 0)
{
uint8_t v___x_820_; 
v___x_820_ = l_Lean_Expr_isHEq(v_a_817_);
lean_dec(v_a_817_);
if (v___x_820_ == 0)
{
v_a_763_ = v___x_772_;
goto v___jp_762_;
}
else
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_Meta_saveState___redArg(v___y_758_, v___y_760_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_823_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_a_822_);
lean_dec_ref_known(v___x_821_, 1);
lean_inc(v_a_769_);
v___x_823_ = l_Lean_MVarId_assumption(v_a_769_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_dec(v_a_822_);
v___y_794_ = v___x_823_;
goto v___jp_793_;
}
else
{
lean_object* v_a_824_; uint8_t v___y_826_; uint8_t v___x_842_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_824_);
v___x_842_ = l_Lean_Exception_isInterrupt(v_a_824_);
if (v___x_842_ == 0)
{
uint8_t v___x_843_; 
v___x_843_ = l_Lean_Exception_isRuntime(v_a_824_);
v___y_826_ = v___x_843_;
goto v___jp_825_;
}
else
{
lean_dec(v_a_824_);
v___y_826_ = v___x_842_;
goto v___jp_825_;
}
v___jp_825_:
{
if (v___y_826_ == 0)
{
lean_object* v___x_827_; 
lean_dec_ref_known(v___x_823_, 1);
v___x_827_ = l_Lean_Meta_SavedState_restore___redArg(v_a_822_, v___y_758_, v___y_760_);
lean_dec(v_a_822_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v___x_828_; 
lean_dec_ref_known(v___x_827_, 1);
v___x_828_ = l_Lean_Meta_saveState___redArg(v___y_758_, v___y_760_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_830_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_a_829_);
lean_dec_ref_known(v___x_828_, 1);
lean_inc(v_a_769_);
v___x_830_ = l_Lean_MVarId_hrefl(v_a_769_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_dec(v_a_829_);
v___y_794_ = v___x_830_;
goto v___jp_793_;
}
else
{
lean_object* v_a_831_; uint8_t v___x_832_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_a_831_);
v___x_832_ = l_Lean_Exception_isInterrupt(v_a_831_);
if (v___x_832_ == 0)
{
uint8_t v___x_833_; 
v___x_833_ = l_Lean_Exception_isRuntime(v_a_831_);
v___y_796_ = v_a_829_;
v___y_797_ = v___x_830_;
v___y_798_ = v___x_833_;
goto v___jp_795_;
}
else
{
lean_dec(v_a_831_);
v___y_796_ = v_a_829_;
v___y_797_ = v___x_830_;
v___y_798_ = v___x_832_;
goto v___jp_795_;
}
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
v_a_834_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_828_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_828_);
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
v___y_794_ = v___x_827_;
goto v___jp_793_;
}
}
else
{
lean_dec(v_a_822_);
v___y_794_ = v___x_823_;
goto v___jp_793_;
}
}
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
v_a_844_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_821_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_821_);
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
}
else
{
lean_object* v___x_852_; 
lean_dec(v_a_817_);
v___x_852_ = l_Lean_Meta_saveState___redArg(v___y_758_, v___y_760_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_854_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v___x_852_, 1);
lean_inc(v_a_769_);
v___x_854_ = l_Lean_MVarId_assumption(v_a_769_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_dec(v_a_853_);
v___y_774_ = v___x_854_;
goto v___jp_773_;
}
else
{
lean_object* v_a_855_; uint8_t v___y_857_; uint8_t v___x_873_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
v___x_873_ = l_Lean_Exception_isInterrupt(v_a_855_);
if (v___x_873_ == 0)
{
uint8_t v___x_874_; 
v___x_874_ = l_Lean_Exception_isRuntime(v_a_855_);
v___y_857_ = v___x_874_;
goto v___jp_856_;
}
else
{
lean_dec(v_a_855_);
v___y_857_ = v___x_873_;
goto v___jp_856_;
}
v___jp_856_:
{
if (v___y_857_ == 0)
{
lean_object* v___x_858_; 
lean_dec_ref_known(v___x_854_, 1);
v___x_858_ = l_Lean_Meta_SavedState_restore___redArg(v_a_853_, v___y_758_, v___y_760_);
lean_dec(v_a_853_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v___x_859_; 
lean_dec_ref_known(v___x_858_, 1);
v___x_859_ = l_Lean_Meta_saveState___redArg(v___y_758_, v___y_760_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_861_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref_known(v___x_859_, 1);
lean_inc(v_a_769_);
v___x_861_ = l_Lean_MVarId_refl(v_a_769_, v___x_819_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_dec(v_a_860_);
v___y_774_ = v___x_861_;
goto v___jp_773_;
}
else
{
lean_object* v_a_862_; uint8_t v___x_863_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
v___x_863_ = l_Lean_Exception_isInterrupt(v_a_862_);
if (v___x_863_ == 0)
{
uint8_t v___x_864_; 
v___x_864_ = l_Lean_Exception_isRuntime(v_a_862_);
v___y_776_ = v___x_861_;
v___y_777_ = v_a_860_;
v___y_778_ = v___x_864_;
goto v___jp_775_;
}
else
{
lean_dec(v_a_862_);
v___y_776_ = v___x_861_;
v___y_777_ = v_a_860_;
v___y_778_ = v___x_863_;
goto v___jp_775_;
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
v_a_865_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_859_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_859_);
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
v___y_774_ = v___x_858_;
goto v___jp_773_;
}
}
else
{
lean_dec(v_a_853_);
v___y_774_ = v___x_854_;
goto v___jp_773_;
}
}
}
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
v_a_875_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_852_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_852_);
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
}
else
{
lean_object* v___x_883_; 
lean_dec(v_a_817_);
v___x_883_ = l_Lean_Meta_saveState___redArg(v___y_758_, v___y_760_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_885_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_883_, 1);
lean_inc(v_a_769_);
v___x_885_ = l_Lean_MVarId_assumption(v_a_769_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_dec(v_a_884_);
v___y_814_ = v___x_885_;
goto v___jp_813_;
}
else
{
lean_object* v_a_886_; uint8_t v___y_888_; uint8_t v___x_903_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
v___x_903_ = l_Lean_Exception_isInterrupt(v_a_886_);
if (v___x_903_ == 0)
{
uint8_t v___x_904_; 
v___x_904_ = l_Lean_Exception_isRuntime(v_a_886_);
v___y_888_ = v___x_904_;
goto v___jp_887_;
}
else
{
lean_dec(v_a_886_);
v___y_888_ = v___x_903_;
goto v___jp_887_;
}
v___jp_887_:
{
if (v___y_888_ == 0)
{
lean_object* v___x_889_; 
lean_dec_ref_known(v___x_885_, 1);
v___x_889_ = l_Lean_Meta_SavedState_restore___redArg(v_a_884_, v___y_758_, v___y_760_);
lean_dec(v_a_884_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_901_; 
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_901_ == 0)
{
lean_object* v_unused_902_; 
v_unused_902_ = lean_ctor_get(v___x_889_, 0);
lean_dec(v_unused_902_);
v___x_891_ = v___x_889_;
v_isShared_892_ = v_isSharedCheck_901_;
goto v_resetjp_890_;
}
else
{
lean_dec(v___x_889_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_901_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; lean_object* v___x_895_; 
v___x_893_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5);
lean_inc(v_a_769_);
if (v_isShared_892_ == 0)
{
lean_ctor_set_tag(v___x_891_, 1);
lean_ctor_set(v___x_891_, 0, v_a_769_);
v___x_895_ = v___x_891_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_769_);
v___x_895_ = v_reuseFailAlloc_900_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_893_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_898_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
v___y_814_ = v___x_899_;
goto v___jp_813_;
}
}
}
else
{
v___y_814_ = v___x_889_;
goto v___jp_813_;
}
}
else
{
lean_dec(v_a_884_);
v___y_814_ = v___x_885_;
goto v___jp_813_;
}
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
v_a_905_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_883_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_883_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
v_a_913_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_816_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_816_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
else
{
v_a_763_ = v___x_772_;
goto v___jp_762_;
}
v___jp_773_:
{
if (lean_obj_tag(v___y_774_) == 0)
{
lean_dec_ref_known(v___y_774_, 1);
v_a_763_ = v___x_772_;
goto v___jp_762_;
}
else
{
return v___y_774_;
}
}
v___jp_775_:
{
if (v___y_778_ == 0)
{
lean_object* v___x_779_; 
lean_dec_ref(v___y_776_);
v___x_779_ = l_Lean_Meta_SavedState_restore___redArg(v___y_777_, v___y_758_, v___y_760_);
lean_dec_ref(v___y_777_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_791_; 
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; 
v_unused_792_ = lean_ctor_get(v___x_779_, 0);
lean_dec(v_unused_792_);
v___x_781_ = v___x_779_;
v_isShared_782_ = v_isSharedCheck_791_;
goto v_resetjp_780_;
}
else
{
lean_dec(v___x_779_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_791_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_783_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1);
lean_inc(v_a_769_);
if (v_isShared_782_ == 0)
{
lean_ctor_set_tag(v___x_781_, 1);
lean_ctor_set(v___x_781_, 0, v_a_769_);
v___x_785_ = v___x_781_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_769_);
v___x_785_ = v_reuseFailAlloc_790_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_783_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_786_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_788_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
v___y_774_ = v___x_789_;
goto v___jp_773_;
}
}
}
else
{
v___y_774_ = v___x_779_;
goto v___jp_773_;
}
}
else
{
lean_dec_ref(v___y_777_);
v___y_774_ = v___y_776_;
goto v___jp_773_;
}
}
v___jp_793_:
{
if (lean_obj_tag(v___y_794_) == 0)
{
lean_dec_ref_known(v___y_794_, 1);
v_a_763_ = v___x_772_;
goto v___jp_762_;
}
else
{
return v___y_794_;
}
}
v___jp_795_:
{
if (v___y_798_ == 0)
{
lean_object* v___x_799_; 
lean_dec_ref(v___y_797_);
v___x_799_ = l_Lean_Meta_SavedState_restore___redArg(v___y_796_, v___y_758_, v___y_760_);
lean_dec_ref(v___y_796_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_811_; 
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_811_ == 0)
{
lean_object* v_unused_812_; 
v_unused_812_ = lean_ctor_get(v___x_799_, 0);
lean_dec(v_unused_812_);
v___x_801_ = v___x_799_;
v_isShared_802_ = v_isSharedCheck_811_;
goto v_resetjp_800_;
}
else
{
lean_dec(v___x_799_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_811_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_803_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1);
lean_inc(v_a_769_);
if (v_isShared_802_ == 0)
{
lean_ctor_set_tag(v___x_801_, 1);
lean_ctor_set(v___x_801_, 0, v_a_769_);
v___x_805_ = v___x_801_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_769_);
v___x_805_ = v_reuseFailAlloc_810_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_803_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_806_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_808_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
v___y_794_ = v___x_809_;
goto v___jp_793_;
}
}
}
else
{
v___y_794_ = v___x_799_;
goto v___jp_793_;
}
}
else
{
lean_dec_ref(v___y_796_);
v___y_794_ = v___y_797_;
goto v___jp_793_;
}
}
v___jp_813_:
{
if (lean_obj_tag(v___y_814_) == 0)
{
lean_dec_ref_known(v___y_814_, 1);
v_a_763_ = v___x_772_;
goto v___jp_762_;
}
else
{
return v___y_814_;
}
}
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
v_a_921_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_770_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_770_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
v___jp_762_:
{
size_t v___x_764_; size_t v___x_765_; 
v___x_764_ = ((size_t)1ULL);
v___x_765_ = lean_usize_add(v_i_755_, v___x_764_);
v_i_755_ = v___x_765_;
v_b_756_ = v_a_763_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___boxed(lean_object* v_as_929_, lean_object* v_sz_930_, lean_object* v_i_931_, lean_object* v_b_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
size_t v_sz_boxed_938_; size_t v_i_boxed_939_; lean_object* v_res_940_; 
v_sz_boxed_938_ = lean_unbox_usize(v_sz_930_);
lean_dec(v_sz_930_);
v_i_boxed_939_ = lean_unbox_usize(v_i_931_);
lean_dec(v_i_931_);
v_res_940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v_as_929_, v_sz_boxed_938_, v_i_boxed_939_, v_b_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec_ref(v_as_929_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(lean_object* v_a_941_, lean_object* v_a_942_){
_start:
{
if (lean_obj_tag(v_a_941_) == 0)
{
lean_object* v___x_943_; 
v___x_943_ = l_List_reverse___redArg(v_a_942_);
return v___x_943_;
}
else
{
lean_object* v_head_944_; lean_object* v_tail_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_954_; 
v_head_944_ = lean_ctor_get(v_a_941_, 0);
v_tail_945_ = lean_ctor_get(v_a_941_, 1);
v_isSharedCheck_954_ = !lean_is_exclusive(v_a_941_);
if (v_isSharedCheck_954_ == 0)
{
v___x_947_ = v_a_941_;
v_isShared_948_ = v_isSharedCheck_954_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_tail_945_);
lean_inc(v_head_944_);
lean_dec(v_a_941_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_954_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_949_, 0, v_head_944_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v_a_942_);
lean_ctor_set(v___x_947_, 0, v___x_949_);
v___x_951_ = v___x_947_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v_a_942_);
v___x_951_ = v_reuseFailAlloc_953_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
v_a_941_ = v_tail_945_;
v_a_942_ = v___x_951_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__1(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__0));
v___x_957_ = l_Lean_stringToMessageData(v___x_956_);
return v___x_957_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__3(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__2));
v___x_960_ = l_Lean_stringToMessageData(v___x_959_);
return v___x_960_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__5(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__4));
v___x_963_ = l_Lean_stringToMessageData(v___x_962_);
return v___x_963_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__7(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_965_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__6));
v___x_966_ = l_Lean_stringToMessageData(v___x_965_);
return v___x_966_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__9(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__8));
v___x_969_ = l_Lean_stringToMessageData(v___x_968_);
return v___x_969_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__12(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__11));
v___x_974_ = l_Lean_stringToMessageData(v___x_973_);
return v___x_974_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__14(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__13));
v___x_977_ = l_Lean_stringToMessageData(v___x_976_);
return v___x_977_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__16(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__15));
v___x_980_ = l_Lean_stringToMessageData(v___x_979_);
return v___x_980_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__22(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__21));
v___x_989_ = l_Lean_stringToMessageData(v___x_988_);
return v___x_989_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__24(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__23));
v___x_992_ = l_Lean_stringToMessageData(v___x_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2(uint8_t v___x_993_, lean_object* v___x_994_, lean_object* v_fst_995_, lean_object* v___x_996_, lean_object* v_e_997_, uint8_t v___y_998_, lean_object* v_snd_999_, lean_object* v_____r_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___y_1007_; lean_object* v_proof_1008_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; uint8_t v___y_1033_; lean_object* v___x_1045_; lean_object* v___y_1047_; uint8_t v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; uint8_t v___y_1068_; lean_object* v_a_1069_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; uint8_t v___y_1098_; lean_object* v___y_1099_; size_t v_sz_1109_; size_t v___x_1110_; lean_object* v___x_1111_; lean_object* v___y_1113_; uint8_t v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; uint8_t v_fst_1140_; lean_object* v_fst_1141_; lean_object* v_snd_1142_; lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1045_ = l_Lean_mkAppN(v___x_994_, v_fst_995_);
v_sz_1109_ = lean_array_size(v_fst_995_);
v___x_1110_ = ((size_t)0ULL);
v___x_1111_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_1109_, v___x_1110_, v_fst_995_);
v___x_1176_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1177_ = lean_unsigned_to_nat(4u);
v___x_1178_ = l_Lean_Expr_isAppOfArity(v_snd_999_, v___x_1176_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1179_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1180_ = lean_unsigned_to_nat(3u);
v___x_1181_ = l_Lean_Expr_isAppOfArity(v_snd_999_, v___x_1179_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
lean_dec_ref(v___x_1111_);
lean_dec_ref(v___x_1045_);
lean_dec_ref(v_e_997_);
v___x_1182_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1183_ = l_Lean_MessageData_ofConstName(v___x_996_, v___y_998_);
v___x_1184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1182_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1184_);
lean_ctor_set(v___x_1186_, 1, v___x_1185_);
v___x_1187_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1186_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1187_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1187_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
else
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1196_ = l_Lean_Expr_appFn_x21(v_snd_999_);
v___x_1197_ = l_Lean_Expr_appArg_x21(v___x_1196_);
lean_dec_ref(v___x_1196_);
v___x_1198_ = l_Lean_Expr_appArg_x21(v_snd_999_);
v_fst_1140_ = v___y_998_;
v_fst_1141_ = v___x_1197_;
v_snd_1142_ = v___x_1198_;
goto v___jp_1139_;
}
}
else
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1199_ = l_Lean_Expr_appFn_x21(v_snd_999_);
v___x_1200_ = l_Lean_Expr_appFn_x21(v___x_1199_);
lean_dec_ref(v___x_1199_);
v___x_1201_ = l_Lean_Expr_appArg_x21(v___x_1200_);
lean_dec_ref(v___x_1200_);
v___x_1202_ = l_Lean_Expr_appArg_x21(v_snd_999_);
v_fst_1140_ = v___x_993_;
v_fst_1141_ = v___x_1201_;
v_snd_1142_ = v___x_1202_;
goto v___jp_1139_;
}
v___jp_1006_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1009_, 0, v_proof_1008_);
v___x_1010_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1010_, 0, v___y_1007_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
lean_ctor_set_uint8(v___x_1010_, sizeof(void*)*2, v___x_993_);
v___x_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
return v___x_1011_;
}
v___jp_1012_:
{
if (lean_obj_tag(v___y_1014_) == 0)
{
lean_object* v_a_1015_; 
v_a_1015_ = lean_ctor_get(v___y_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref_known(v___y_1014_, 1);
v___y_1007_ = v___y_1013_;
v_proof_1008_ = v_a_1015_;
goto v___jp_1006_;
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_dec_ref(v___y_1013_);
v_a_1016_ = lean_ctor_get(v___y_1014_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___y_1014_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___y_1014_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___y_1014_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
v___jp_1024_:
{
if (v___y_1033_ == 0)
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_dec_ref(v___y_1031_);
v___x_1034_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1035_ = l_Lean_MessageData_ofExpr(v___y_1029_);
v___x_1036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = l_Lean_Exception_toMessageData(v___y_1028_);
v___x_1040_ = l_Lean_indentD(v___x_1039_);
v___x_1041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1038_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1041_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1043_, v___y_1025_, v___y_1032_, v___y_1027_, v___y_1030_);
v___y_1013_ = v___y_1026_;
v___y_1014_ = v___x_1044_;
goto v___jp_1012_;
}
else
{
lean_dec_ref(v___y_1029_);
lean_dec_ref(v___y_1028_);
v___y_1013_ = v___y_1026_;
v___y_1014_ = v___y_1031_;
goto v___jp_1012_;
}
}
v___jp_1046_:
{
lean_object* v___x_1053_; lean_object* v_a_1054_; lean_object* v___x_1055_; 
v___x_1053_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_1047_, v___y_1050_);
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1054_);
lean_dec_ref(v___x_1053_);
v___x_1055_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___x_1045_, v___y_1050_);
if (v___y_1048_ == 0)
{
lean_object* v_a_1056_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_a_1056_);
lean_dec_ref(v___x_1055_);
v___y_1007_ = v_a_1054_;
v_proof_1008_ = v_a_1056_;
goto v___jp_1006_;
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1058_; 
v_a_1057_ = lean_ctor_get(v___x_1055_, 0);
lean_inc_n(v_a_1057_, 2);
lean_dec_ref(v___x_1055_);
v___x_1058_ = l_Lean_Meta_mkEqOfHEq(v_a_1057_, v___x_993_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_dec(v_a_1057_);
v___y_1013_ = v_a_1054_;
v___y_1014_ = v___x_1058_;
goto v___jp_1012_;
}
else
{
lean_object* v_a_1059_; uint8_t v___x_1060_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_a_1059_);
v___x_1060_ = l_Lean_Exception_isInterrupt(v_a_1059_);
if (v___x_1060_ == 0)
{
uint8_t v___x_1061_; 
lean_inc(v_a_1059_);
v___x_1061_ = l_Lean_Exception_isRuntime(v_a_1059_);
v___y_1025_ = v___y_1049_;
v___y_1026_ = v_a_1054_;
v___y_1027_ = v___y_1051_;
v___y_1028_ = v_a_1059_;
v___y_1029_ = v_a_1057_;
v___y_1030_ = v___y_1052_;
v___y_1031_ = v___x_1058_;
v___y_1032_ = v___y_1050_;
v___y_1033_ = v___x_1061_;
goto v___jp_1024_;
}
else
{
v___y_1025_ = v___y_1049_;
v___y_1026_ = v_a_1054_;
v___y_1027_ = v___y_1051_;
v___y_1028_ = v_a_1059_;
v___y_1029_ = v_a_1057_;
v___y_1030_ = v___y_1052_;
v___y_1031_ = v___x_1058_;
v___y_1032_ = v___y_1050_;
v___y_1033_ = v___x_1060_;
goto v___jp_1024_;
}
}
}
}
v___jp_1062_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; 
v___x_1070_ = lean_array_get_size(v_a_1069_);
v___x_1071_ = lean_unsigned_to_nat(0u);
v___x_1072_ = lean_nat_dec_eq(v___x_1070_, v___x_1071_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec_ref(v___y_1063_);
lean_dec_ref(v___x_1045_);
v___x_1073_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1074_ = l_Lean_MessageData_ofConstName(v___x_996_, v___x_1072_);
v___x_1075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = lean_array_to_list(v_a_1069_);
v___x_1079_ = lean_box(0);
v___x_1080_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_1078_, v___x_1079_);
v___x_1081_ = l_Lean_MessageData_ofList(v___x_1080_);
v___x_1082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1077_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1082_, v___y_1066_, v___y_1065_, v___y_1067_, v___y_1064_);
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1083_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1083_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
else
{
lean_dec_ref(v_a_1069_);
lean_dec(v___x_996_);
v___y_1047_ = v___y_1063_;
v___y_1048_ = v___y_1068_;
v___y_1049_ = v___y_1066_;
v___y_1050_ = v___y_1065_;
v___y_1051_ = v___y_1067_;
v___y_1052_ = v___y_1064_;
goto v___jp_1046_;
}
}
v___jp_1092_:
{
if (lean_obj_tag(v___y_1099_) == 0)
{
lean_object* v_a_1100_; 
v_a_1100_ = lean_ctor_get(v___y_1099_, 0);
lean_inc(v_a_1100_);
lean_dec_ref_known(v___y_1099_, 1);
v___y_1063_ = v___y_1093_;
v___y_1064_ = v___y_1094_;
v___y_1065_ = v___y_1096_;
v___y_1066_ = v___y_1095_;
v___y_1067_ = v___y_1097_;
v___y_1068_ = v___y_1098_;
v_a_1069_ = v_a_1100_;
goto v___jp_1062_;
}
else
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_dec_ref(v___y_1093_);
lean_dec_ref(v___x_1045_);
lean_dec(v___x_996_);
v_a_1101_ = lean_ctor_get(v___y_1099_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___y_1099_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___y_1099_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___y_1099_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
v___jp_1112_:
{
lean_object* v___x_1119_; size_t v_sz_1120_; lean_object* v___x_1121_; 
v___x_1119_ = lean_box(0);
v_sz_1120_ = lean_array_size(v___x_1111_);
v___x_1121_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1111_, v_sz_1120_, v___x_1110_, v___x_1119_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
lean_dec_ref_known(v___x_1121_, 1);
v___x_1122_ = lean_unsigned_to_nat(0u);
v___x_1123_ = lean_array_get_size(v___x_1111_);
v___x_1124_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1125_ = lean_nat_dec_lt(v___x_1122_, v___x_1123_);
if (v___x_1125_ == 0)
{
lean_dec_ref(v___x_1111_);
v___y_1063_ = v___y_1113_;
v___y_1064_ = v___y_1118_;
v___y_1065_ = v___y_1116_;
v___y_1066_ = v___y_1115_;
v___y_1067_ = v___y_1117_;
v___y_1068_ = v___y_1114_;
v_a_1069_ = v___x_1124_;
goto v___jp_1062_;
}
else
{
uint8_t v___x_1126_; 
v___x_1126_ = lean_nat_dec_le(v___x_1123_, v___x_1123_);
if (v___x_1126_ == 0)
{
if (v___x_1125_ == 0)
{
lean_dec_ref(v___x_1111_);
v___y_1063_ = v___y_1113_;
v___y_1064_ = v___y_1118_;
v___y_1065_ = v___y_1116_;
v___y_1066_ = v___y_1115_;
v___y_1067_ = v___y_1117_;
v___y_1068_ = v___y_1114_;
v_a_1069_ = v___x_1124_;
goto v___jp_1062_;
}
else
{
size_t v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = lean_usize_of_nat(v___x_1123_);
v___x_1128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1111_, v___x_1110_, v___x_1127_, v___x_1124_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec_ref(v___x_1111_);
v___y_1093_ = v___y_1113_;
v___y_1094_ = v___y_1118_;
v___y_1095_ = v___y_1115_;
v___y_1096_ = v___y_1116_;
v___y_1097_ = v___y_1117_;
v___y_1098_ = v___y_1114_;
v___y_1099_ = v___x_1128_;
goto v___jp_1092_;
}
}
else
{
size_t v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = lean_usize_of_nat(v___x_1123_);
v___x_1130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1111_, v___x_1110_, v___x_1129_, v___x_1124_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec_ref(v___x_1111_);
v___y_1093_ = v___y_1113_;
v___y_1094_ = v___y_1118_;
v___y_1095_ = v___y_1115_;
v___y_1096_ = v___y_1116_;
v___y_1097_ = v___y_1117_;
v___y_1098_ = v___y_1114_;
v___y_1099_ = v___x_1130_;
goto v___jp_1092_;
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec_ref(v___y_1113_);
lean_dec_ref(v___x_1111_);
lean_dec_ref(v___x_1045_);
lean_dec(v___x_996_);
v_a_1131_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1121_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1121_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
v___jp_1139_:
{
lean_object* v___x_1143_; 
lean_inc_ref(v_fst_1141_);
lean_inc_ref(v_e_997_);
v___x_1143_ = l_Lean_Meta_isExprDefEq(v_e_997_, v_fst_1141_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; uint8_t v___x_1145_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___x_1143_, 1);
v___x_1145_ = lean_unbox(v_a_1144_);
lean_dec(v_a_1144_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
lean_dec_ref(v_snd_1142_);
lean_dec_ref(v___x_1111_);
lean_dec_ref(v___x_1045_);
v___x_1146_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1147_ = l_Lean_MessageData_ofExpr(v_fst_1141_);
v___x_1148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1146_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1148_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = l_Lean_MessageData_ofConstName(v___x_996_, v___y_998_);
v___x_1152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1150_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___x_1153_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1152_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = l_Lean_MessageData_ofExpr(v_e_997_);
v___x_1156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1154_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_1158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1156_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1158_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1159_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1159_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
else
{
lean_dec_ref(v_fst_1141_);
lean_dec_ref(v_e_997_);
v___y_1113_ = v_snd_1142_;
v___y_1114_ = v_fst_1140_;
v___y_1115_ = v___y_1001_;
v___y_1116_ = v___y_1002_;
v___y_1117_ = v___y_1003_;
v___y_1118_ = v___y_1004_;
goto v___jp_1112_;
}
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
lean_dec_ref(v_snd_1142_);
lean_dec_ref(v_fst_1141_);
lean_dec_ref(v___x_1111_);
lean_dec_ref(v___x_1045_);
lean_dec_ref(v_e_997_);
lean_dec(v___x_996_);
v_a_1168_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1143_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1143_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2___boxed(lean_object* v___x_1203_, lean_object* v___x_1204_, lean_object* v_fst_1205_, lean_object* v___x_1206_, lean_object* v_e_1207_, lean_object* v___y_1208_, lean_object* v_snd_1209_, lean_object* v_____r_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
uint8_t v___x_84716__boxed_1216_; uint8_t v___y_84720__boxed_1217_; lean_object* v_res_1218_; 
v___x_84716__boxed_1216_ = lean_unbox(v___x_1203_);
v___y_84720__boxed_1217_ = lean_unbox(v___y_1208_);
v_res_1218_ = l_Lean_Meta_rwMatcher___lam__2(v___x_84716__boxed_1216_, v___x_1204_, v_fst_1205_, v___x_1206_, v_e_1207_, v___y_84720__boxed_1217_, v_snd_1209_, v_____r_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec_ref(v_snd_1209_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3(uint8_t v___x_1219_, lean_object* v___x_1220_, lean_object* v_fst_1221_, lean_object* v___x_1222_, lean_object* v_e_1223_, uint8_t v___y_1224_, lean_object* v_snd_1225_, lean_object* v_____r_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v___y_1233_; lean_object* v_proof_1234_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; uint8_t v___y_1259_; lean_object* v___x_1271_; uint8_t v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1289_; lean_object* v___y_1290_; uint8_t v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v_a_1295_; lean_object* v___y_1319_; uint8_t v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; size_t v_sz_1335_; size_t v___x_1336_; lean_object* v___x_1337_; uint8_t v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; uint8_t v_fst_1366_; lean_object* v_fst_1367_; lean_object* v_snd_1368_; lean_object* v___x_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v___x_1271_ = l_Lean_mkAppN(v___x_1220_, v_fst_1221_);
v_sz_1335_ = lean_array_size(v_fst_1221_);
v___x_1336_ = ((size_t)0ULL);
v___x_1337_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_1335_, v___x_1336_, v_fst_1221_);
v___x_1402_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1403_ = lean_unsigned_to_nat(4u);
v___x_1404_ = l_Lean_Expr_isAppOfArity(v_snd_1225_, v___x_1402_, v___x_1403_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v___x_1405_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1406_ = lean_unsigned_to_nat(3u);
v___x_1407_ = l_Lean_Expr_isAppOfArity(v_snd_1225_, v___x_1405_, v___x_1406_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec_ref(v___x_1337_);
lean_dec_ref(v___x_1271_);
lean_dec_ref(v_e_1223_);
v___x_1408_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1409_ = l_Lean_MessageData_ofConstName(v___x_1222_, v___y_1224_);
v___x_1410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1408_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
v___x_1411_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1410_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
v___x_1413_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1412_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
else
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1422_ = l_Lean_Expr_appFn_x21(v_snd_1225_);
v___x_1423_ = l_Lean_Expr_appArg_x21(v___x_1422_);
lean_dec_ref(v___x_1422_);
v___x_1424_ = l_Lean_Expr_appArg_x21(v_snd_1225_);
v_fst_1366_ = v___y_1224_;
v_fst_1367_ = v___x_1423_;
v_snd_1368_ = v___x_1424_;
goto v___jp_1365_;
}
}
else
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1425_ = l_Lean_Expr_appFn_x21(v_snd_1225_);
v___x_1426_ = l_Lean_Expr_appFn_x21(v___x_1425_);
lean_dec_ref(v___x_1425_);
v___x_1427_ = l_Lean_Expr_appArg_x21(v___x_1426_);
lean_dec_ref(v___x_1426_);
v___x_1428_ = l_Lean_Expr_appArg_x21(v_snd_1225_);
v_fst_1366_ = v___x_1219_;
v_fst_1367_ = v___x_1427_;
v_snd_1368_ = v___x_1428_;
goto v___jp_1365_;
}
v___jp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1235_, 0, v_proof_1234_);
v___x_1236_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1236_, 0, v___y_1233_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
lean_ctor_set_uint8(v___x_1236_, sizeof(void*)*2, v___x_1219_);
v___x_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
return v___x_1237_;
}
v___jp_1238_:
{
if (lean_obj_tag(v___y_1240_) == 0)
{
lean_object* v_a_1241_; 
v_a_1241_ = lean_ctor_get(v___y_1240_, 0);
lean_inc(v_a_1241_);
lean_dec_ref_known(v___y_1240_, 1);
v___y_1233_ = v___y_1239_;
v_proof_1234_ = v_a_1241_;
goto v___jp_1232_;
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec_ref(v___y_1239_);
v_a_1242_ = lean_ctor_get(v___y_1240_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___y_1240_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___y_1240_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___y_1240_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
v___jp_1250_:
{
if (v___y_1259_ == 0)
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
lean_dec_ref(v___y_1255_);
v___x_1260_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1261_ = l_Lean_MessageData_ofExpr(v___y_1257_);
v___x_1262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1260_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1262_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
v___x_1265_ = l_Lean_Exception_toMessageData(v___y_1254_);
v___x_1266_ = l_Lean_indentD(v___x_1265_);
v___x_1267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1264_);
lean_ctor_set(v___x_1267_, 1, v___x_1266_);
v___x_1268_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1267_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
v___x_1270_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1269_, v___y_1253_, v___y_1252_, v___y_1251_, v___y_1258_);
v___y_1239_ = v___y_1256_;
v___y_1240_ = v___x_1270_;
goto v___jp_1238_;
}
else
{
lean_dec_ref(v___y_1257_);
lean_dec_ref(v___y_1254_);
v___y_1239_ = v___y_1256_;
v___y_1240_ = v___y_1255_;
goto v___jp_1238_;
}
}
v___jp_1272_:
{
lean_object* v___x_1279_; lean_object* v_a_1280_; lean_object* v___x_1281_; 
v___x_1279_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_1274_, v___y_1276_);
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref(v___x_1279_);
v___x_1281_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___x_1271_, v___y_1276_);
if (v___y_1273_ == 0)
{
lean_object* v_a_1282_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1282_);
lean_dec_ref(v___x_1281_);
v___y_1233_ = v_a_1280_;
v_proof_1234_ = v_a_1282_;
goto v___jp_1232_;
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1284_; 
v_a_1283_ = lean_ctor_get(v___x_1281_, 0);
lean_inc_n(v_a_1283_, 2);
lean_dec_ref(v___x_1281_);
v___x_1284_ = l_Lean_Meta_mkEqOfHEq(v_a_1283_, v___x_1219_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_dec(v_a_1283_);
v___y_1239_ = v_a_1280_;
v___y_1240_ = v___x_1284_;
goto v___jp_1238_;
}
else
{
lean_object* v_a_1285_; uint8_t v___x_1286_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
v___x_1286_ = l_Lean_Exception_isInterrupt(v_a_1285_);
if (v___x_1286_ == 0)
{
uint8_t v___x_1287_; 
lean_inc(v_a_1285_);
v___x_1287_ = l_Lean_Exception_isRuntime(v_a_1285_);
v___y_1251_ = v___y_1277_;
v___y_1252_ = v___y_1276_;
v___y_1253_ = v___y_1275_;
v___y_1254_ = v_a_1285_;
v___y_1255_ = v___x_1284_;
v___y_1256_ = v_a_1280_;
v___y_1257_ = v_a_1283_;
v___y_1258_ = v___y_1278_;
v___y_1259_ = v___x_1287_;
goto v___jp_1250_;
}
else
{
v___y_1251_ = v___y_1277_;
v___y_1252_ = v___y_1276_;
v___y_1253_ = v___y_1275_;
v___y_1254_ = v_a_1285_;
v___y_1255_ = v___x_1284_;
v___y_1256_ = v_a_1280_;
v___y_1257_ = v_a_1283_;
v___y_1258_ = v___y_1278_;
v___y_1259_ = v___x_1286_;
goto v___jp_1250_;
}
}
}
}
v___jp_1288_:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1296_ = lean_array_get_size(v_a_1295_);
v___x_1297_ = lean_unsigned_to_nat(0u);
v___x_1298_ = lean_nat_dec_eq(v___x_1296_, v___x_1297_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
lean_dec_ref(v___y_1290_);
lean_dec_ref(v___x_1271_);
v___x_1299_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1300_ = l_Lean_MessageData_ofConstName(v___x_1222_, v___x_1298_);
v___x_1301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1299_);
lean_ctor_set(v___x_1301_, 1, v___x_1300_);
v___x_1302_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1301_);
lean_ctor_set(v___x_1303_, 1, v___x_1302_);
v___x_1304_ = lean_array_to_list(v_a_1295_);
v___x_1305_ = lean_box(0);
v___x_1306_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_1304_, v___x_1305_);
v___x_1307_ = l_Lean_MessageData_ofList(v___x_1306_);
v___x_1308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1303_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
v___x_1309_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1308_, v___y_1289_, v___y_1293_, v___y_1294_, v___y_1292_);
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1309_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1309_);
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
else
{
lean_dec_ref(v_a_1295_);
lean_dec(v___x_1222_);
v___y_1273_ = v___y_1291_;
v___y_1274_ = v___y_1290_;
v___y_1275_ = v___y_1289_;
v___y_1276_ = v___y_1293_;
v___y_1277_ = v___y_1294_;
v___y_1278_ = v___y_1292_;
goto v___jp_1272_;
}
}
v___jp_1318_:
{
if (lean_obj_tag(v___y_1325_) == 0)
{
lean_object* v_a_1326_; 
v_a_1326_ = lean_ctor_get(v___y_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref_known(v___y_1325_, 1);
v___y_1289_ = v___y_1319_;
v___y_1290_ = v___y_1321_;
v___y_1291_ = v___y_1320_;
v___y_1292_ = v___y_1322_;
v___y_1293_ = v___y_1323_;
v___y_1294_ = v___y_1324_;
v_a_1295_ = v_a_1326_;
goto v___jp_1288_;
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec_ref(v___y_1321_);
lean_dec_ref(v___x_1271_);
lean_dec(v___x_1222_);
v_a_1327_ = lean_ctor_get(v___y_1325_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___y_1325_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___y_1325_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___y_1325_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
v___jp_1338_:
{
lean_object* v___x_1345_; size_t v_sz_1346_; lean_object* v___x_1347_; 
v___x_1345_ = lean_box(0);
v_sz_1346_ = lean_array_size(v___x_1337_);
v___x_1347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1337_, v_sz_1346_, v___x_1336_, v___x_1345_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
lean_dec_ref_known(v___x_1347_, 1);
v___x_1348_ = lean_unsigned_to_nat(0u);
v___x_1349_ = lean_array_get_size(v___x_1337_);
v___x_1350_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1351_ = lean_nat_dec_lt(v___x_1348_, v___x_1349_);
if (v___x_1351_ == 0)
{
lean_dec_ref(v___x_1337_);
v___y_1289_ = v___y_1341_;
v___y_1290_ = v___y_1340_;
v___y_1291_ = v___y_1339_;
v___y_1292_ = v___y_1344_;
v___y_1293_ = v___y_1342_;
v___y_1294_ = v___y_1343_;
v_a_1295_ = v___x_1350_;
goto v___jp_1288_;
}
else
{
uint8_t v___x_1352_; 
v___x_1352_ = lean_nat_dec_le(v___x_1349_, v___x_1349_);
if (v___x_1352_ == 0)
{
if (v___x_1351_ == 0)
{
lean_dec_ref(v___x_1337_);
v___y_1289_ = v___y_1341_;
v___y_1290_ = v___y_1340_;
v___y_1291_ = v___y_1339_;
v___y_1292_ = v___y_1344_;
v___y_1293_ = v___y_1342_;
v___y_1294_ = v___y_1343_;
v_a_1295_ = v___x_1350_;
goto v___jp_1288_;
}
else
{
size_t v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = lean_usize_of_nat(v___x_1349_);
v___x_1354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1337_, v___x_1336_, v___x_1353_, v___x_1350_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
lean_dec_ref(v___x_1337_);
v___y_1319_ = v___y_1341_;
v___y_1320_ = v___y_1339_;
v___y_1321_ = v___y_1340_;
v___y_1322_ = v___y_1344_;
v___y_1323_ = v___y_1342_;
v___y_1324_ = v___y_1343_;
v___y_1325_ = v___x_1354_;
goto v___jp_1318_;
}
}
else
{
size_t v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = lean_usize_of_nat(v___x_1349_);
v___x_1356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1337_, v___x_1336_, v___x_1355_, v___x_1350_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
lean_dec_ref(v___x_1337_);
v___y_1319_ = v___y_1341_;
v___y_1320_ = v___y_1339_;
v___y_1321_ = v___y_1340_;
v___y_1322_ = v___y_1344_;
v___y_1323_ = v___y_1342_;
v___y_1324_ = v___y_1343_;
v___y_1325_ = v___x_1356_;
goto v___jp_1318_;
}
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec_ref(v___y_1340_);
lean_dec_ref(v___x_1337_);
lean_dec_ref(v___x_1271_);
lean_dec(v___x_1222_);
v_a_1357_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1347_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1347_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
v___jp_1365_:
{
lean_object* v___x_1369_; 
lean_inc_ref(v_fst_1367_);
lean_inc_ref(v_e_1223_);
v___x_1369_ = l_Lean_Meta_isExprDefEq(v_e_1223_, v_fst_1367_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; uint8_t v___x_1371_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref_known(v___x_1369_, 1);
v___x_1371_ = lean_unbox(v_a_1370_);
lean_dec(v_a_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_dec_ref(v_snd_1368_);
lean_dec_ref(v___x_1337_);
lean_dec_ref(v___x_1271_);
v___x_1372_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1373_ = l_Lean_MessageData_ofExpr(v_fst_1367_);
v___x_1374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1372_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
v___x_1375_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___x_1374_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
v___x_1377_ = l_Lean_MessageData_ofConstName(v___x_1222_, v___y_1224_);
v___x_1378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1376_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
v___x_1379_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1378_);
lean_ctor_set(v___x_1380_, 1, v___x_1379_);
v___x_1381_ = l_Lean_MessageData_ofExpr(v_e_1223_);
v___x_1382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1380_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
v___x_1383_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_1384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1382_);
lean_ctor_set(v___x_1384_, 1, v___x_1383_);
v___x_1385_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1384_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1385_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1385_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
else
{
lean_dec_ref(v_fst_1367_);
lean_dec_ref(v_e_1223_);
v___y_1339_ = v_fst_1366_;
v___y_1340_ = v_snd_1368_;
v___y_1341_ = v___y_1227_;
v___y_1342_ = v___y_1228_;
v___y_1343_ = v___y_1229_;
v___y_1344_ = v___y_1230_;
goto v___jp_1338_;
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_dec_ref(v_snd_1368_);
lean_dec_ref(v_fst_1367_);
lean_dec_ref(v___x_1337_);
lean_dec_ref(v___x_1271_);
lean_dec_ref(v_e_1223_);
lean_dec(v___x_1222_);
v_a_1394_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1369_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1369_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3___boxed(lean_object* v___x_1429_, lean_object* v___x_1430_, lean_object* v_fst_1431_, lean_object* v___x_1432_, lean_object* v_e_1433_, lean_object* v___y_1434_, lean_object* v_snd_1435_, lean_object* v_____r_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
uint8_t v___x_85226__boxed_1442_; uint8_t v___y_85230__boxed_1443_; lean_object* v_res_1444_; 
v___x_85226__boxed_1442_ = lean_unbox(v___x_1429_);
v___y_85230__boxed_1443_ = lean_unbox(v___y_1434_);
v_res_1444_ = l_Lean_Meta_rwMatcher___lam__3(v___x_85226__boxed_1442_, v___x_1430_, v_fst_1431_, v___x_1432_, v_e_1433_, v___y_85230__boxed_1443_, v_snd_1435_, v_____r_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec_ref(v_snd_1435_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4(uint8_t v___x_1445_, lean_object* v___x_1446_, lean_object* v_fst_1447_, lean_object* v___x_1448_, lean_object* v_e_1449_, uint8_t v___y_1450_, lean_object* v_snd_1451_, lean_object* v_____r_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v___y_1459_; lean_object* v_proof_1460_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; uint8_t v___y_1485_; lean_object* v___x_1497_; uint8_t v___y_1499_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; uint8_t v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v_a_1521_; lean_object* v___y_1545_; lean_object* v___y_1546_; uint8_t v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; size_t v_sz_1561_; size_t v___x_1562_; lean_object* v___x_1563_; uint8_t v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; uint8_t v_fst_1592_; lean_object* v_fst_1593_; lean_object* v_snd_1594_; lean_object* v___x_1628_; lean_object* v___x_1629_; uint8_t v___x_1630_; 
v___x_1497_ = l_Lean_mkAppN(v___x_1446_, v_fst_1447_);
v_sz_1561_ = lean_array_size(v_fst_1447_);
v___x_1562_ = ((size_t)0ULL);
v___x_1563_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_1561_, v___x_1562_, v_fst_1447_);
v___x_1628_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1629_ = lean_unsigned_to_nat(4u);
v___x_1630_ = l_Lean_Expr_isAppOfArity(v_snd_1451_, v___x_1628_, v___x_1629_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; lean_object* v___x_1632_; uint8_t v___x_1633_; 
v___x_1631_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1632_ = lean_unsigned_to_nat(3u);
v___x_1633_ = l_Lean_Expr_isAppOfArity(v_snd_1451_, v___x_1631_, v___x_1632_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec_ref(v___x_1563_);
lean_dec_ref(v___x_1497_);
lean_dec_ref(v_e_1449_);
v___x_1634_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1635_ = l_Lean_MessageData_ofConstName(v___x_1448_, v___y_1450_);
v___x_1636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1634_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1636_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
v___x_1639_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1638_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1648_ = l_Lean_Expr_appFn_x21(v_snd_1451_);
v___x_1649_ = l_Lean_Expr_appArg_x21(v___x_1648_);
lean_dec_ref(v___x_1648_);
v___x_1650_ = l_Lean_Expr_appArg_x21(v_snd_1451_);
v_fst_1592_ = v___y_1450_;
v_fst_1593_ = v___x_1649_;
v_snd_1594_ = v___x_1650_;
goto v___jp_1591_;
}
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1651_ = l_Lean_Expr_appFn_x21(v_snd_1451_);
v___x_1652_ = l_Lean_Expr_appFn_x21(v___x_1651_);
lean_dec_ref(v___x_1651_);
v___x_1653_ = l_Lean_Expr_appArg_x21(v___x_1652_);
lean_dec_ref(v___x_1652_);
v___x_1654_ = l_Lean_Expr_appArg_x21(v_snd_1451_);
v_fst_1592_ = v___x_1445_;
v_fst_1593_ = v___x_1653_;
v_snd_1594_ = v___x_1654_;
goto v___jp_1591_;
}
v___jp_1458_:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1461_, 0, v_proof_1460_);
v___x_1462_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1462_, 0, v___y_1459_);
lean_ctor_set(v___x_1462_, 1, v___x_1461_);
lean_ctor_set_uint8(v___x_1462_, sizeof(void*)*2, v___x_1445_);
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
return v___x_1463_;
}
v___jp_1464_:
{
if (lean_obj_tag(v___y_1466_) == 0)
{
lean_object* v_a_1467_; 
v_a_1467_ = lean_ctor_get(v___y_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref_known(v___y_1466_, 1);
v___y_1459_ = v___y_1465_;
v_proof_1460_ = v_a_1467_;
goto v___jp_1458_;
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_dec_ref(v___y_1465_);
v_a_1468_ = lean_ctor_get(v___y_1466_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___y_1466_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___y_1466_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___y_1466_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
v___jp_1476_:
{
if (v___y_1485_ == 0)
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
lean_dec_ref(v___y_1481_);
v___x_1486_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1487_ = l_Lean_MessageData_ofExpr(v___y_1479_);
v___x_1488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1486_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1488_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
v___x_1491_ = l_Lean_Exception_toMessageData(v___y_1483_);
v___x_1492_ = l_Lean_indentD(v___x_1491_);
v___x_1493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1493_, 0, v___x_1490_);
lean_ctor_set(v___x_1493_, 1, v___x_1492_);
v___x_1494_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1493_);
lean_ctor_set(v___x_1495_, 1, v___x_1494_);
v___x_1496_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1495_, v___y_1480_, v___y_1478_, v___y_1484_, v___y_1477_);
v___y_1465_ = v___y_1482_;
v___y_1466_ = v___x_1496_;
goto v___jp_1464_;
}
else
{
lean_dec_ref(v___y_1483_);
lean_dec_ref(v___y_1479_);
v___y_1465_ = v___y_1482_;
v___y_1466_ = v___y_1481_;
goto v___jp_1464_;
}
}
v___jp_1498_:
{
lean_object* v___x_1505_; lean_object* v_a_1506_; lean_object* v___x_1507_; 
v___x_1505_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_1500_, v___y_1502_);
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_a_1506_);
lean_dec_ref(v___x_1505_);
v___x_1507_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___x_1497_, v___y_1502_);
if (v___y_1499_ == 0)
{
lean_object* v_a_1508_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_a_1508_);
lean_dec_ref(v___x_1507_);
v___y_1459_ = v_a_1506_;
v_proof_1460_ = v_a_1508_;
goto v___jp_1458_;
}
else
{
lean_object* v_a_1509_; lean_object* v___x_1510_; 
v_a_1509_ = lean_ctor_get(v___x_1507_, 0);
lean_inc_n(v_a_1509_, 2);
lean_dec_ref(v___x_1507_);
v___x_1510_ = l_Lean_Meta_mkEqOfHEq(v_a_1509_, v___x_1445_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_dec(v_a_1509_);
v___y_1465_ = v_a_1506_;
v___y_1466_ = v___x_1510_;
goto v___jp_1464_;
}
else
{
lean_object* v_a_1511_; uint8_t v___x_1512_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_a_1511_);
v___x_1512_ = l_Lean_Exception_isInterrupt(v_a_1511_);
if (v___x_1512_ == 0)
{
uint8_t v___x_1513_; 
lean_inc(v_a_1511_);
v___x_1513_ = l_Lean_Exception_isRuntime(v_a_1511_);
v___y_1477_ = v___y_1504_;
v___y_1478_ = v___y_1502_;
v___y_1479_ = v_a_1509_;
v___y_1480_ = v___y_1501_;
v___y_1481_ = v___x_1510_;
v___y_1482_ = v_a_1506_;
v___y_1483_ = v_a_1511_;
v___y_1484_ = v___y_1503_;
v___y_1485_ = v___x_1513_;
goto v___jp_1476_;
}
else
{
v___y_1477_ = v___y_1504_;
v___y_1478_ = v___y_1502_;
v___y_1479_ = v_a_1509_;
v___y_1480_ = v___y_1501_;
v___y_1481_ = v___x_1510_;
v___y_1482_ = v_a_1506_;
v___y_1483_ = v_a_1511_;
v___y_1484_ = v___y_1503_;
v___y_1485_ = v___x_1512_;
goto v___jp_1476_;
}
}
}
}
v___jp_1514_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; uint8_t v___x_1524_; 
v___x_1522_ = lean_array_get_size(v_a_1521_);
v___x_1523_ = lean_unsigned_to_nat(0u);
v___x_1524_ = lean_nat_dec_eq(v___x_1522_, v___x_1523_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
lean_dec_ref(v___y_1517_);
lean_dec_ref(v___x_1497_);
v___x_1525_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1526_ = l_Lean_MessageData_ofConstName(v___x_1448_, v___x_1524_);
v___x_1527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1525_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
v___x_1528_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1527_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
v___x_1530_ = lean_array_to_list(v_a_1521_);
v___x_1531_ = lean_box(0);
v___x_1532_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_1530_, v___x_1531_);
v___x_1533_ = l_Lean_MessageData_ofList(v___x_1532_);
v___x_1534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1529_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
v___x_1535_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1534_, v___y_1516_, v___y_1519_, v___y_1520_, v___y_1515_);
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1535_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1535_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1536_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
else
{
lean_dec_ref(v_a_1521_);
lean_dec(v___x_1448_);
v___y_1499_ = v___y_1518_;
v___y_1500_ = v___y_1517_;
v___y_1501_ = v___y_1516_;
v___y_1502_ = v___y_1519_;
v___y_1503_ = v___y_1520_;
v___y_1504_ = v___y_1515_;
goto v___jp_1498_;
}
}
v___jp_1544_:
{
if (lean_obj_tag(v___y_1551_) == 0)
{
lean_object* v_a_1552_; 
v_a_1552_ = lean_ctor_get(v___y_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref_known(v___y_1551_, 1);
v___y_1515_ = v___y_1546_;
v___y_1516_ = v___y_1545_;
v___y_1517_ = v___y_1548_;
v___y_1518_ = v___y_1547_;
v___y_1519_ = v___y_1549_;
v___y_1520_ = v___y_1550_;
v_a_1521_ = v_a_1552_;
goto v___jp_1514_;
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec_ref(v___y_1548_);
lean_dec_ref(v___x_1497_);
lean_dec(v___x_1448_);
v_a_1553_ = lean_ctor_get(v___y_1551_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___y_1551_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___y_1551_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___y_1551_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
v___jp_1564_:
{
lean_object* v___x_1571_; size_t v_sz_1572_; lean_object* v___x_1573_; 
v___x_1571_ = lean_box(0);
v_sz_1572_ = lean_array_size(v___x_1563_);
v___x_1573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1563_, v_sz_1572_, v___x_1562_, v___x_1571_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; 
lean_dec_ref_known(v___x_1573_, 1);
v___x_1574_ = lean_unsigned_to_nat(0u);
v___x_1575_ = lean_array_get_size(v___x_1563_);
v___x_1576_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1577_ = lean_nat_dec_lt(v___x_1574_, v___x_1575_);
if (v___x_1577_ == 0)
{
lean_dec_ref(v___x_1563_);
v___y_1515_ = v___y_1570_;
v___y_1516_ = v___y_1567_;
v___y_1517_ = v___y_1566_;
v___y_1518_ = v___y_1565_;
v___y_1519_ = v___y_1568_;
v___y_1520_ = v___y_1569_;
v_a_1521_ = v___x_1576_;
goto v___jp_1514_;
}
else
{
uint8_t v___x_1578_; 
v___x_1578_ = lean_nat_dec_le(v___x_1575_, v___x_1575_);
if (v___x_1578_ == 0)
{
if (v___x_1577_ == 0)
{
lean_dec_ref(v___x_1563_);
v___y_1515_ = v___y_1570_;
v___y_1516_ = v___y_1567_;
v___y_1517_ = v___y_1566_;
v___y_1518_ = v___y_1565_;
v___y_1519_ = v___y_1568_;
v___y_1520_ = v___y_1569_;
v_a_1521_ = v___x_1576_;
goto v___jp_1514_;
}
else
{
size_t v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = lean_usize_of_nat(v___x_1575_);
v___x_1580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1563_, v___x_1562_, v___x_1579_, v___x_1576_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec_ref(v___x_1563_);
v___y_1545_ = v___y_1567_;
v___y_1546_ = v___y_1570_;
v___y_1547_ = v___y_1565_;
v___y_1548_ = v___y_1566_;
v___y_1549_ = v___y_1568_;
v___y_1550_ = v___y_1569_;
v___y_1551_ = v___x_1580_;
goto v___jp_1544_;
}
}
else
{
size_t v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = lean_usize_of_nat(v___x_1575_);
v___x_1582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___x_1563_, v___x_1562_, v___x_1581_, v___x_1576_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
lean_dec_ref(v___x_1563_);
v___y_1545_ = v___y_1567_;
v___y_1546_ = v___y_1570_;
v___y_1547_ = v___y_1565_;
v___y_1548_ = v___y_1566_;
v___y_1549_ = v___y_1568_;
v___y_1550_ = v___y_1569_;
v___y_1551_ = v___x_1582_;
goto v___jp_1544_;
}
}
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_dec_ref(v___y_1566_);
lean_dec_ref(v___x_1563_);
lean_dec_ref(v___x_1497_);
lean_dec(v___x_1448_);
v_a_1583_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1573_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1573_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
v___jp_1591_:
{
lean_object* v___x_1595_; 
lean_inc_ref(v_fst_1593_);
lean_inc_ref(v_e_1449_);
v___x_1595_ = l_Lean_Meta_isExprDefEq(v_e_1449_, v_fst_1593_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; uint8_t v___x_1597_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref_known(v___x_1595_, 1);
v___x_1597_ = lean_unbox(v_a_1596_);
lean_dec(v_a_1596_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
lean_dec_ref(v_snd_1594_);
lean_dec_ref(v___x_1563_);
lean_dec_ref(v___x_1497_);
v___x_1598_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1599_ = l_Lean_MessageData_ofExpr(v_fst_1593_);
v___x_1600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1598_);
lean_ctor_set(v___x_1600_, 1, v___x_1599_);
v___x_1601_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1600_);
lean_ctor_set(v___x_1602_, 1, v___x_1601_);
v___x_1603_ = l_Lean_MessageData_ofConstName(v___x_1448_, v___y_1450_);
v___x_1604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1602_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
v___x_1605_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1604_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v___x_1607_ = l_Lean_MessageData_ofExpr(v_e_1449_);
v___x_1608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1606_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
v___x_1609_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_1610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1608_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
v___x_1611_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1610_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1611_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1611_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
else
{
lean_dec_ref(v_fst_1593_);
lean_dec_ref(v_e_1449_);
v___y_1565_ = v_fst_1592_;
v___y_1566_ = v_snd_1594_;
v___y_1567_ = v___y_1453_;
v___y_1568_ = v___y_1454_;
v___y_1569_ = v___y_1455_;
v___y_1570_ = v___y_1456_;
goto v___jp_1564_;
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec_ref(v_snd_1594_);
lean_dec_ref(v_fst_1593_);
lean_dec_ref(v___x_1563_);
lean_dec_ref(v___x_1497_);
lean_dec_ref(v_e_1449_);
lean_dec(v___x_1448_);
v_a_1620_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1595_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1595_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4___boxed(lean_object* v___x_1655_, lean_object* v___x_1656_, lean_object* v_fst_1657_, lean_object* v___x_1658_, lean_object* v_e_1659_, lean_object* v___y_1660_, lean_object* v_snd_1661_, lean_object* v_____r_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
uint8_t v___x_85711__boxed_1668_; uint8_t v___y_85715__boxed_1669_; lean_object* v_res_1670_; 
v___x_85711__boxed_1668_ = lean_unbox(v___x_1655_);
v___y_85715__boxed_1669_ = lean_unbox(v___y_1660_);
v_res_1670_ = l_Lean_Meta_rwMatcher___lam__4(v___x_85711__boxed_1668_, v___x_1656_, v_fst_1657_, v___x_1658_, v_e_1659_, v___y_85715__boxed_1669_, v_snd_1661_, v_____r_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec_ref(v_snd_1661_);
return v_res_1670_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1671_; double v___x_1672_; 
v___x_1671_ = lean_unsigned_to_nat(0u);
v___x_1672_ = lean_float_of_nat(v___x_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(lean_object* v_cls_1676_, lean_object* v_msg_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v_ref_1683_; lean_object* v___x_1684_; lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1729_; 
v_ref_1683_ = lean_ctor_get(v___y_1680_, 2);
v___x_1684_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1687_ = v___x_1684_;
v_isShared_1688_ = v_isSharedCheck_1729_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1684_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1729_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1689_; lean_object* v_traceState_1690_; lean_object* v_env_1691_; lean_object* v_nextMacroScope_1692_; lean_object* v_ngen_1693_; lean_object* v_auxDeclNGen_1694_; lean_object* v_cache_1695_; lean_object* v_messages_1696_; lean_object* v_infoState_1697_; lean_object* v_snapshotTasks_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1728_; 
v___x_1689_ = lean_st_ref_take(v___y_1681_);
v_traceState_1690_ = lean_ctor_get(v___x_1689_, 4);
v_env_1691_ = lean_ctor_get(v___x_1689_, 0);
v_nextMacroScope_1692_ = lean_ctor_get(v___x_1689_, 1);
v_ngen_1693_ = lean_ctor_get(v___x_1689_, 2);
v_auxDeclNGen_1694_ = lean_ctor_get(v___x_1689_, 3);
v_cache_1695_ = lean_ctor_get(v___x_1689_, 5);
v_messages_1696_ = lean_ctor_get(v___x_1689_, 6);
v_infoState_1697_ = lean_ctor_get(v___x_1689_, 7);
v_snapshotTasks_1698_ = lean_ctor_get(v___x_1689_, 8);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1700_ = v___x_1689_;
v_isShared_1701_ = v_isSharedCheck_1728_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_snapshotTasks_1698_);
lean_inc(v_infoState_1697_);
lean_inc(v_messages_1696_);
lean_inc(v_cache_1695_);
lean_inc(v_traceState_1690_);
lean_inc(v_auxDeclNGen_1694_);
lean_inc(v_ngen_1693_);
lean_inc(v_nextMacroScope_1692_);
lean_inc(v_env_1691_);
lean_dec(v___x_1689_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1728_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
uint64_t v_tid_1702_; lean_object* v_traces_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1727_; 
v_tid_1702_ = lean_ctor_get_uint64(v_traceState_1690_, sizeof(void*)*1);
v_traces_1703_ = lean_ctor_get(v_traceState_1690_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_traceState_1690_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1705_ = v_traceState_1690_;
v_isShared_1706_ = v_isSharedCheck_1727_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_traces_1703_);
lean_dec(v_traceState_1690_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1727_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1707_; double v___x_1708_; uint8_t v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1717_; 
v___x_1707_ = lean_box(0);
v___x_1708_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0);
v___x_1709_ = 0;
v___x_1710_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1));
v___x_1711_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1711_, 0, v_cls_1676_);
lean_ctor_set(v___x_1711_, 1, v___x_1707_);
lean_ctor_set(v___x_1711_, 2, v___x_1710_);
lean_ctor_set_float(v___x_1711_, sizeof(void*)*3, v___x_1708_);
lean_ctor_set_float(v___x_1711_, sizeof(void*)*3 + 8, v___x_1708_);
lean_ctor_set_uint8(v___x_1711_, sizeof(void*)*3 + 16, v___x_1709_);
v___x_1712_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__2));
v___x_1713_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1711_);
lean_ctor_set(v___x_1713_, 1, v_a_1685_);
lean_ctor_set(v___x_1713_, 2, v___x_1712_);
lean_inc(v_ref_1683_);
v___x_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1714_, 0, v_ref_1683_);
lean_ctor_set(v___x_1714_, 1, v___x_1713_);
v___x_1715_ = l_Lean_PersistentArray_push___redArg(v_traces_1703_, v___x_1714_);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v___x_1715_);
v___x_1717_ = v___x_1705_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1715_);
lean_ctor_set_uint64(v_reuseFailAlloc_1726_, sizeof(void*)*1, v_tid_1702_);
v___x_1717_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
lean_object* v___x_1719_; 
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 4, v___x_1717_);
v___x_1719_ = v___x_1700_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_env_1691_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_nextMacroScope_1692_);
lean_ctor_set(v_reuseFailAlloc_1725_, 2, v_ngen_1693_);
lean_ctor_set(v_reuseFailAlloc_1725_, 3, v_auxDeclNGen_1694_);
lean_ctor_set(v_reuseFailAlloc_1725_, 4, v___x_1717_);
lean_ctor_set(v_reuseFailAlloc_1725_, 5, v_cache_1695_);
lean_ctor_set(v_reuseFailAlloc_1725_, 6, v_messages_1696_);
lean_ctor_set(v_reuseFailAlloc_1725_, 7, v_infoState_1697_);
lean_ctor_set(v_reuseFailAlloc_1725_, 8, v_snapshotTasks_1698_);
v___x_1719_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1720_ = lean_st_ref_put(v___y_1681_, v___x_1719_);
v___x_1721_ = lean_box(0);
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 0, v___x_1721_);
v___x_1723_ = v___x_1687_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1721_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___boxed(lean_object* v_cls_1730_, lean_object* v_msg_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v_cls_1730_, v_msg_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(lean_object* v_a_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_Meta_reduceRecMatcher_x3f(v_a_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1758_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1747_ = v___x_1744_;
v_isShared_1748_ = v_isSharedCheck_1758_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1744_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1758_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
if (lean_obj_tag(v_a_1745_) == 1)
{
lean_object* v_val_1749_; lean_object* v___x_1750_; 
lean_del_object(v___x_1747_);
lean_dec_ref(v_a_1738_);
v_val_1749_ = lean_ctor_get(v_a_1745_, 0);
lean_inc(v_val_1749_);
lean_dec_ref_known(v_a_1745_, 1);
v___x_1750_ = l_Lean_Expr_headBeta(v_val_1749_);
v_a_1738_ = v___x_1750_;
goto _start;
}
else
{
lean_object* v___x_1752_; uint8_t v___x_1753_; 
lean_dec(v_a_1745_);
lean_inc_ref(v_a_1738_);
v___x_1752_ = l_Lean_Expr_headBeta(v_a_1738_);
v___x_1753_ = lean_expr_eqv(v_a_1738_, v___x_1752_);
if (v___x_1753_ == 0)
{
lean_del_object(v___x_1747_);
lean_dec_ref(v_a_1738_);
v_a_1738_ = v___x_1752_;
goto _start;
}
else
{
lean_object* v___x_1756_; 
lean_dec_ref(v___x_1752_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v_a_1738_);
v___x_1756_ = v___x_1747_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1738_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
lean_dec_ref(v_a_1738_);
v_a_1759_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1744_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1744_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg___boxed(lean_object* v_a_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(v_a_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(lean_object* v_opts_1774_, lean_object* v_opt_1775_){
_start:
{
lean_object* v_name_1776_; lean_object* v_defValue_1777_; lean_object* v_map_1778_; lean_object* v___x_1779_; 
v_name_1776_ = lean_ctor_get(v_opt_1775_, 0);
v_defValue_1777_ = lean_ctor_get(v_opt_1775_, 1);
v_map_1778_ = lean_ctor_get(v_opts_1774_, 0);
v___x_1779_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1778_, v_name_1776_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_inc(v_defValue_1777_);
return v_defValue_1777_;
}
else
{
lean_object* v_val_1780_; 
v_val_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_val_1780_);
lean_dec_ref_known(v___x_1779_, 1);
if (lean_obj_tag(v_val_1780_) == 3)
{
lean_object* v_v_1781_; 
v_v_1781_ = lean_ctor_get(v_val_1780_, 0);
lean_inc(v_v_1781_);
lean_dec_ref_known(v_val_1780_, 1);
return v_v_1781_;
}
else
{
lean_dec(v_val_1780_);
lean_inc(v_defValue_1777_);
return v_defValue_1777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16___boxed(lean_object* v_opts_1782_, lean_object* v_opt_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_1782_, v_opt_1783_);
lean_dec_ref(v_opt_1783_);
lean_dec_ref(v_opts_1782_);
return v_res_1784_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(lean_object* v_e_1785_){
_start:
{
if (lean_obj_tag(v_e_1785_) == 0)
{
uint8_t v___x_1786_; 
v___x_1786_ = 2;
return v___x_1786_;
}
else
{
uint8_t v___x_1787_; 
v___x_1787_ = 0;
return v___x_1787_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___boxed(lean_object* v_e_1788_){
_start:
{
uint8_t v_res_1789_; lean_object* v_r_1790_; 
v_res_1789_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(v_e_1788_);
lean_dec_ref(v_e_1788_);
v_r_1790_ = lean_box(v_res_1789_);
return v_r_1790_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(lean_object* v_x_1791_){
_start:
{
if (lean_obj_tag(v_x_1791_) == 0)
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
v_a_1793_ = lean_ctor_get(v_x_1791_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_x_1791_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v_x_1791_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v_x_1791_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
lean_ctor_set_tag(v___x_1795_, 1);
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
v_a_1801_ = lean_ctor_get(v_x_1791_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v_x_1791_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v_x_1791_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v_x_1791_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
lean_ctor_set_tag(v___x_1803_, 0);
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg___boxed(lean_object* v_x_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(v_x_1809_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15(size_t v_sz_1812_, size_t v_i_1813_, lean_object* v_bs_1814_){
_start:
{
uint8_t v___x_1815_; 
v___x_1815_ = lean_usize_dec_lt(v_i_1813_, v_sz_1812_);
if (v___x_1815_ == 0)
{
return v_bs_1814_;
}
else
{
lean_object* v_v_1816_; lean_object* v_msg_1817_; lean_object* v___x_1818_; lean_object* v_bs_x27_1819_; size_t v___x_1820_; size_t v___x_1821_; lean_object* v___x_1822_; 
v_v_1816_ = lean_array_uget_borrowed(v_bs_1814_, v_i_1813_);
v_msg_1817_ = lean_ctor_get(v_v_1816_, 1);
lean_inc_ref(v_msg_1817_);
v___x_1818_ = lean_unsigned_to_nat(0u);
v_bs_x27_1819_ = lean_array_uset(v_bs_1814_, v_i_1813_, v___x_1818_);
v___x_1820_ = ((size_t)1ULL);
v___x_1821_ = lean_usize_add(v_i_1813_, v___x_1820_);
v___x_1822_ = lean_array_uset(v_bs_x27_1819_, v_i_1813_, v_msg_1817_);
v_i_1813_ = v___x_1821_;
v_bs_1814_ = v___x_1822_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15___boxed(lean_object* v_sz_1824_, lean_object* v_i_1825_, lean_object* v_bs_1826_){
_start:
{
size_t v_sz_boxed_1827_; size_t v_i_boxed_1828_; lean_object* v_res_1829_; 
v_sz_boxed_1827_ = lean_unbox_usize(v_sz_1824_);
lean_dec(v_sz_1824_);
v_i_boxed_1828_ = lean_unbox_usize(v_i_1825_);
lean_dec(v_i_1825_);
v_res_1829_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15(v_sz_boxed_1827_, v_i_boxed_1828_, v_bs_1826_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(lean_object* v_oldTraces_1830_, lean_object* v_data_1831_, lean_object* v_ref_1832_, lean_object* v_msg_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_toCold_1839_; lean_object* v_currRecDepth_1840_; lean_object* v_ref_1841_; uint8_t v_diag_1842_; uint8_t v_suppressElabErrors_1843_; lean_object* v___x_1844_; lean_object* v_traceState_1845_; lean_object* v_traces_1846_; lean_object* v_ref_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; size_t v_sz_1850_; size_t v___x_1851_; lean_object* v___x_1852_; lean_object* v_msg_1853_; lean_object* v___x_1854_; lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1892_; 
v_toCold_1839_ = lean_ctor_get(v___y_1836_, 0);
v_currRecDepth_1840_ = lean_ctor_get(v___y_1836_, 1);
v_ref_1841_ = lean_ctor_get(v___y_1836_, 2);
v_diag_1842_ = lean_ctor_get_uint8(v___y_1836_, sizeof(void*)*3);
v_suppressElabErrors_1843_ = lean_ctor_get_uint8(v___y_1836_, sizeof(void*)*3 + 1);
v___x_1844_ = lean_st_ref_get(v___y_1837_);
v_traceState_1845_ = lean_ctor_get(v___x_1844_, 4);
lean_inc_ref(v_traceState_1845_);
lean_dec(v___x_1844_);
v_traces_1846_ = lean_ctor_get(v_traceState_1845_, 0);
lean_inc_ref(v_traces_1846_);
lean_dec_ref(v_traceState_1845_);
v_ref_1847_ = l_Lean_replaceRef(v_ref_1832_, v_ref_1841_);
lean_inc(v_currRecDepth_1840_);
lean_inc_ref(v_toCold_1839_);
v___x_1848_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1848_, 0, v_toCold_1839_);
lean_ctor_set(v___x_1848_, 1, v_currRecDepth_1840_);
lean_ctor_set(v___x_1848_, 2, v_ref_1847_);
lean_ctor_set_uint8(v___x_1848_, sizeof(void*)*3, v_diag_1842_);
lean_ctor_set_uint8(v___x_1848_, sizeof(void*)*3 + 1, v_suppressElabErrors_1843_);
v___x_1849_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1846_);
lean_dec_ref(v_traces_1846_);
v_sz_1850_ = lean_array_size(v___x_1849_);
v___x_1851_ = ((size_t)0ULL);
v___x_1852_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15(v_sz_1850_, v___x_1851_, v___x_1849_);
v_msg_1853_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1853_, 0, v_data_1831_);
lean_ctor_set(v_msg_1853_, 1, v_msg_1833_);
lean_ctor_set(v_msg_1853_, 2, v___x_1852_);
v___x_1854_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_1853_, v___y_1834_, v___y_1835_, v___x_1848_, v___y_1837_);
lean_dec_ref_known(v___x_1848_, 3);
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1857_ = v___x_1854_;
v_isShared_1858_ = v_isSharedCheck_1892_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1854_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1892_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1859_; lean_object* v_traceState_1860_; lean_object* v_env_1861_; lean_object* v_nextMacroScope_1862_; lean_object* v_ngen_1863_; lean_object* v_auxDeclNGen_1864_; lean_object* v_cache_1865_; lean_object* v_messages_1866_; lean_object* v_infoState_1867_; lean_object* v_snapshotTasks_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1891_; 
v___x_1859_ = lean_st_ref_take(v___y_1837_);
v_traceState_1860_ = lean_ctor_get(v___x_1859_, 4);
v_env_1861_ = lean_ctor_get(v___x_1859_, 0);
v_nextMacroScope_1862_ = lean_ctor_get(v___x_1859_, 1);
v_ngen_1863_ = lean_ctor_get(v___x_1859_, 2);
v_auxDeclNGen_1864_ = lean_ctor_get(v___x_1859_, 3);
v_cache_1865_ = lean_ctor_get(v___x_1859_, 5);
v_messages_1866_ = lean_ctor_get(v___x_1859_, 6);
v_infoState_1867_ = lean_ctor_get(v___x_1859_, 7);
v_snapshotTasks_1868_ = lean_ctor_get(v___x_1859_, 8);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1870_ = v___x_1859_;
v_isShared_1871_ = v_isSharedCheck_1891_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_snapshotTasks_1868_);
lean_inc(v_infoState_1867_);
lean_inc(v_messages_1866_);
lean_inc(v_cache_1865_);
lean_inc(v_traceState_1860_);
lean_inc(v_auxDeclNGen_1864_);
lean_inc(v_ngen_1863_);
lean_inc(v_nextMacroScope_1862_);
lean_inc(v_env_1861_);
lean_dec(v___x_1859_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1891_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
uint64_t v_tid_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1889_; 
v_tid_1872_ = lean_ctor_get_uint64(v_traceState_1860_, sizeof(void*)*1);
v_isSharedCheck_1889_ = !lean_is_exclusive(v_traceState_1860_);
if (v_isSharedCheck_1889_ == 0)
{
lean_object* v_unused_1890_; 
v_unused_1890_ = lean_ctor_get(v_traceState_1860_, 0);
lean_dec(v_unused_1890_);
v___x_1874_ = v_traceState_1860_;
v_isShared_1875_ = v_isSharedCheck_1889_;
goto v_resetjp_1873_;
}
else
{
lean_dec(v_traceState_1860_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1889_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1879_; 
v___x_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1876_, 0, v_ref_1832_);
lean_ctor_set(v___x_1876_, 1, v_a_1855_);
v___x_1877_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1830_, v___x_1876_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v___x_1877_);
v___x_1879_ = v___x_1874_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1877_);
lean_ctor_set_uint64(v_reuseFailAlloc_1888_, sizeof(void*)*1, v_tid_1872_);
v___x_1879_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
lean_object* v___x_1881_; 
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 4, v___x_1879_);
v___x_1881_ = v___x_1870_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_env_1861_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v_nextMacroScope_1862_);
lean_ctor_set(v_reuseFailAlloc_1887_, 2, v_ngen_1863_);
lean_ctor_set(v_reuseFailAlloc_1887_, 3, v_auxDeclNGen_1864_);
lean_ctor_set(v_reuseFailAlloc_1887_, 4, v___x_1879_);
lean_ctor_set(v_reuseFailAlloc_1887_, 5, v_cache_1865_);
lean_ctor_set(v_reuseFailAlloc_1887_, 6, v_messages_1866_);
lean_ctor_set(v_reuseFailAlloc_1887_, 7, v_infoState_1867_);
lean_ctor_set(v_reuseFailAlloc_1887_, 8, v_snapshotTasks_1868_);
v___x_1881_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1882_ = lean_st_ref_put(v___y_1837_, v___x_1881_);
v___x_1883_ = lean_box(0);
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 0, v___x_1883_);
v___x_1885_ = v___x_1857_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1883_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13___boxed(lean_object* v_oldTraces_1893_, lean_object* v_data_1894_, lean_object* v_ref_1895_, lean_object* v_msg_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(v_oldTraces_1893_, v_data_1894_, v_ref_1895_, v_msg_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
return v_res_1902_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1(void){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__0));
v___x_1905_ = l_Lean_stringToMessageData(v___x_1904_);
return v___x_1905_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2(void){
_start:
{
lean_object* v___x_1906_; double v___x_1907_; 
v___x_1906_ = lean_unsigned_to_nat(1000u);
v___x_1907_ = lean_float_of_nat(v___x_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(lean_object* v_cls_1908_, uint8_t v_collapsed_1909_, lean_object* v_tag_1910_, lean_object* v_opts_1911_, uint8_t v_clsEnabled_1912_, lean_object* v_oldTraces_1913_, lean_object* v_msg_1914_, lean_object* v_resStartStop_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v_fst_1921_; lean_object* v_snd_1922_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v_data_1926_; lean_object* v_fst_1937_; lean_object* v_snd_1938_; lean_object* v___x_1939_; uint8_t v___x_1940_; lean_object* v___y_1942_; lean_object* v_a_1943_; uint8_t v___y_1958_; double v___y_1989_; 
v_fst_1921_ = lean_ctor_get(v_resStartStop_1915_, 0);
lean_inc(v_fst_1921_);
v_snd_1922_ = lean_ctor_get(v_resStartStop_1915_, 1);
lean_inc(v_snd_1922_);
lean_dec_ref(v_resStartStop_1915_);
v_fst_1937_ = lean_ctor_get(v_snd_1922_, 0);
lean_inc(v_fst_1937_);
v_snd_1938_ = lean_ctor_get(v_snd_1922_, 1);
lean_inc(v_snd_1938_);
lean_dec(v_snd_1922_);
v___x_1939_ = l_Lean_trace_profiler;
v___x_1940_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_opts_1911_, v___x_1939_);
if (v___x_1940_ == 0)
{
v___y_1958_ = v___x_1940_;
goto v___jp_1957_;
}
else
{
lean_object* v___x_1994_; uint8_t v___x_1995_; 
v___x_1994_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1995_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_opts_1911_, v___x_1994_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; lean_object* v___x_1997_; double v___x_1998_; double v___x_1999_; double v___x_2000_; 
v___x_1996_ = l_Lean_trace_profiler_threshold;
v___x_1997_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_1911_, v___x_1996_);
v___x_1998_ = lean_float_of_nat(v___x_1997_);
v___x_1999_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2);
v___x_2000_ = lean_float_div(v___x_1998_, v___x_1999_);
v___y_1989_ = v___x_2000_;
goto v___jp_1988_;
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2002_; double v___x_2003_; 
v___x_2001_ = l_Lean_trace_profiler_threshold;
v___x_2002_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_1911_, v___x_2001_);
v___x_2003_ = lean_float_of_nat(v___x_2002_);
v___y_1989_ = v___x_2003_;
goto v___jp_1988_;
}
}
v___jp_1923_:
{
lean_object* v___x_1927_; 
lean_inc(v___y_1925_);
v___x_1927_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(v_oldTraces_1913_, v_data_1926_, v___y_1925_, v___y_1924_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v___x_1928_; 
lean_dec_ref_known(v___x_1927_, 1);
v___x_1928_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(v_fst_1921_);
return v___x_1928_;
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec(v_fst_1921_);
v_a_1929_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1927_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1927_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
v___jp_1941_:
{
uint8_t v_result_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; double v___x_1947_; lean_object* v_data_1948_; 
v_result_1944_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(v_fst_1921_);
v___x_1945_ = lean_box(v_result_1944_);
v___x_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1945_);
v___x_1947_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0);
lean_inc_ref(v_tag_1910_);
lean_inc_ref(v___x_1946_);
lean_inc(v_cls_1908_);
v_data_1948_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1948_, 0, v_cls_1908_);
lean_ctor_set(v_data_1948_, 1, v___x_1946_);
lean_ctor_set(v_data_1948_, 2, v_tag_1910_);
lean_ctor_set_float(v_data_1948_, sizeof(void*)*3, v___x_1947_);
lean_ctor_set_float(v_data_1948_, sizeof(void*)*3 + 8, v___x_1947_);
lean_ctor_set_uint8(v_data_1948_, sizeof(void*)*3 + 16, v_collapsed_1909_);
if (v___x_1940_ == 0)
{
lean_dec_ref_known(v___x_1946_, 1);
lean_dec(v_snd_1938_);
lean_dec(v_fst_1937_);
lean_dec_ref(v_tag_1910_);
lean_dec(v_cls_1908_);
v___y_1924_ = v_a_1943_;
v___y_1925_ = v___y_1942_;
v_data_1926_ = v_data_1948_;
goto v___jp_1923_;
}
else
{
lean_object* v_data_1949_; double v___x_1950_; double v___x_1951_; 
lean_dec_ref_known(v_data_1948_, 3);
v_data_1949_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1949_, 0, v_cls_1908_);
lean_ctor_set(v_data_1949_, 1, v___x_1946_);
lean_ctor_set(v_data_1949_, 2, v_tag_1910_);
v___x_1950_ = lean_unbox_float(v_fst_1937_);
lean_dec(v_fst_1937_);
lean_ctor_set_float(v_data_1949_, sizeof(void*)*3, v___x_1950_);
v___x_1951_ = lean_unbox_float(v_snd_1938_);
lean_dec(v_snd_1938_);
lean_ctor_set_float(v_data_1949_, sizeof(void*)*3 + 8, v___x_1951_);
lean_ctor_set_uint8(v_data_1949_, sizeof(void*)*3 + 16, v_collapsed_1909_);
v___y_1924_ = v_a_1943_;
v___y_1925_ = v___y_1942_;
v_data_1926_ = v_data_1949_;
goto v___jp_1923_;
}
}
v___jp_1952_:
{
lean_object* v_ref_1953_; lean_object* v___x_1954_; 
v_ref_1953_ = lean_ctor_get(v___y_1918_, 2);
lean_inc(v___y_1919_);
lean_inc_ref(v___y_1918_);
lean_inc(v___y_1917_);
lean_inc_ref(v___y_1916_);
lean_inc(v_fst_1921_);
v___x_1954_ = lean_apply_6(v_msg_1914_, v_fst_1921_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, lean_box(0));
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_a_1955_);
lean_dec_ref_known(v___x_1954_, 1);
v___y_1942_ = v_ref_1953_;
v_a_1943_ = v_a_1955_;
goto v___jp_1941_;
}
else
{
lean_object* v___x_1956_; 
lean_dec_ref_known(v___x_1954_, 1);
v___x_1956_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1);
v___y_1942_ = v_ref_1953_;
v_a_1943_ = v___x_1956_;
goto v___jp_1941_;
}
}
v___jp_1957_:
{
if (v_clsEnabled_1912_ == 0)
{
if (v___y_1958_ == 0)
{
lean_object* v___x_1959_; lean_object* v_traceState_1960_; lean_object* v_env_1961_; lean_object* v_nextMacroScope_1962_; lean_object* v_ngen_1963_; lean_object* v_auxDeclNGen_1964_; lean_object* v_cache_1965_; lean_object* v_messages_1966_; lean_object* v_infoState_1967_; lean_object* v_snapshotTasks_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1987_; 
lean_dec(v_snd_1938_);
lean_dec(v_fst_1937_);
lean_dec_ref(v_msg_1914_);
lean_dec_ref(v_tag_1910_);
lean_dec(v_cls_1908_);
v___x_1959_ = lean_st_ref_take(v___y_1919_);
v_traceState_1960_ = lean_ctor_get(v___x_1959_, 4);
v_env_1961_ = lean_ctor_get(v___x_1959_, 0);
v_nextMacroScope_1962_ = lean_ctor_get(v___x_1959_, 1);
v_ngen_1963_ = lean_ctor_get(v___x_1959_, 2);
v_auxDeclNGen_1964_ = lean_ctor_get(v___x_1959_, 3);
v_cache_1965_ = lean_ctor_get(v___x_1959_, 5);
v_messages_1966_ = lean_ctor_get(v___x_1959_, 6);
v_infoState_1967_ = lean_ctor_get(v___x_1959_, 7);
v_snapshotTasks_1968_ = lean_ctor_get(v___x_1959_, 8);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1970_ = v___x_1959_;
v_isShared_1971_ = v_isSharedCheck_1987_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_snapshotTasks_1968_);
lean_inc(v_infoState_1967_);
lean_inc(v_messages_1966_);
lean_inc(v_cache_1965_);
lean_inc(v_traceState_1960_);
lean_inc(v_auxDeclNGen_1964_);
lean_inc(v_ngen_1963_);
lean_inc(v_nextMacroScope_1962_);
lean_inc(v_env_1961_);
lean_dec(v___x_1959_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1987_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
uint64_t v_tid_1972_; lean_object* v_traces_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1986_; 
v_tid_1972_ = lean_ctor_get_uint64(v_traceState_1960_, sizeof(void*)*1);
v_traces_1973_ = lean_ctor_get(v_traceState_1960_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_traceState_1960_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1975_ = v_traceState_1960_;
v_isShared_1976_ = v_isSharedCheck_1986_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_traces_1973_);
lean_dec(v_traceState_1960_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1986_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1977_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1913_, v_traces_1973_);
lean_dec_ref(v_traces_1973_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v___x_1977_);
v___x_1979_ = v___x_1975_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1977_);
lean_ctor_set_uint64(v_reuseFailAlloc_1985_, sizeof(void*)*1, v_tid_1972_);
v___x_1979_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1981_; 
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 4, v___x_1979_);
v___x_1981_ = v___x_1970_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_env_1961_);
lean_ctor_set(v_reuseFailAlloc_1984_, 1, v_nextMacroScope_1962_);
lean_ctor_set(v_reuseFailAlloc_1984_, 2, v_ngen_1963_);
lean_ctor_set(v_reuseFailAlloc_1984_, 3, v_auxDeclNGen_1964_);
lean_ctor_set(v_reuseFailAlloc_1984_, 4, v___x_1979_);
lean_ctor_set(v_reuseFailAlloc_1984_, 5, v_cache_1965_);
lean_ctor_set(v_reuseFailAlloc_1984_, 6, v_messages_1966_);
lean_ctor_set(v_reuseFailAlloc_1984_, 7, v_infoState_1967_);
lean_ctor_set(v_reuseFailAlloc_1984_, 8, v_snapshotTasks_1968_);
v___x_1981_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = lean_st_ref_put(v___y_1919_, v___x_1981_);
v___x_1983_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(v_fst_1921_);
return v___x_1983_;
}
}
}
}
}
else
{
goto v___jp_1952_;
}
}
else
{
goto v___jp_1952_;
}
}
v___jp_1988_:
{
double v___x_1990_; double v___x_1991_; double v___x_1992_; uint8_t v___x_1993_; 
v___x_1990_ = lean_unbox_float(v_snd_1938_);
v___x_1991_ = lean_unbox_float(v_fst_1937_);
v___x_1992_ = lean_float_sub(v___x_1990_, v___x_1991_);
v___x_1993_ = lean_float_decLt(v___y_1989_, v___x_1992_);
v___y_1958_ = v___x_1993_;
goto v___jp_1957_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___boxed(lean_object* v_cls_2004_, lean_object* v_collapsed_2005_, lean_object* v_tag_2006_, lean_object* v_opts_2007_, lean_object* v_clsEnabled_2008_, lean_object* v_oldTraces_2009_, lean_object* v_msg_2010_, lean_object* v_resStartStop_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
uint8_t v_collapsed_boxed_2017_; uint8_t v_clsEnabled_boxed_2018_; lean_object* v_res_2019_; 
v_collapsed_boxed_2017_ = lean_unbox(v_collapsed_2005_);
v_clsEnabled_boxed_2018_ = lean_unbox(v_clsEnabled_2008_);
v_res_2019_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v_cls_2004_, v_collapsed_boxed_2017_, v_tag_2006_, v_opts_2007_, v_clsEnabled_boxed_2018_, v_oldTraces_2009_, v_msg_2010_, v_resStartStop_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec_ref(v_opts_2007_);
return v_res_2019_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__3(void){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__2));
v___x_2025_ = l_Lean_stringToMessageData(v___x_2024_);
return v___x_2025_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__5(void){
_start:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__4));
v___x_2028_ = l_Lean_stringToMessageData(v___x_2027_);
return v___x_2028_;
}
}
static double _init_l_Lean_Meta_rwMatcher___closed__6(void){
_start:
{
lean_object* v___x_2029_; double v___x_2030_; 
v___x_2029_ = lean_unsigned_to_nat(1000000000u);
v___x_2030_ = lean_float_of_nat(v___x_2029_);
return v___x_2030_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__8(void){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__7));
v___x_2033_ = l_Lean_stringToMessageData(v___x_2032_);
return v___x_2033_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__13(void){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2041_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2042_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
v___x_2043_ = l_Lean_Name_append(v___x_2042_, v___x_2041_);
return v___x_2043_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__15(void){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__14));
v___x_2046_ = l_Lean_stringToMessageData(v___x_2045_);
return v___x_2046_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__17(void){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__16));
v___x_2049_ = l_Lean_stringToMessageData(v___x_2048_);
return v___x_2049_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__19(void){
_start:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__18));
v___x_2052_ = l_Lean_stringToMessageData(v___x_2051_);
return v___x_2052_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__21(void){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__20));
v___x_2055_ = l_Lean_stringToMessageData(v___x_2054_);
return v___x_2055_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__22(void){
_start:
{
lean_object* v___x_2056_; lean_object* v_dummy_2057_; 
v___x_2056_ = lean_box(0);
v_dummy_2057_ = l_Lean_Expr_sort___override(v___x_2056_);
return v_dummy_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher(lean_object* v_altIdx_2067_, lean_object* v_e_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_){
_start:
{
lean_object* v___y_2075_; lean_object* v___y_2094_; uint8_t v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___y_2102_; uint8_t v___y_2103_; uint8_t v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v_a_2136_; uint8_t v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2144_; uint8_t v___y_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; uint8_t v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; uint8_t v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v_a_2158_; lean_object* v___y_2168_; uint8_t v___y_2169_; lean_object* v___y_2170_; uint8_t v___y_2171_; lean_object* v___y_2172_; lean_object* v___y_2173_; lean_object* v___y_2174_; uint8_t v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v_a_2179_; lean_object* v___y_2182_; uint8_t v___y_2183_; lean_object* v___y_2184_; uint8_t v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; uint8_t v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; uint8_t v___y_2204_; lean_object* v___y_2205_; lean_object* v___y_2206_; lean_object* v___y_2207_; uint8_t v___y_2208_; lean_object* v___y_2209_; lean_object* v___y_2210_; uint8_t v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v_a_2215_; lean_object* v___y_2228_; uint8_t v___y_2229_; lean_object* v___y_2230_; uint8_t v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; uint8_t v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v_a_2239_; lean_object* v___y_2242_; uint8_t v___y_2243_; lean_object* v___y_2244_; uint8_t v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; uint8_t v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; uint8_t v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; uint8_t v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; uint8_t v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; uint8_t v___y_2274_; lean_object* v___y_2275_; uint8_t v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; uint8_t v___y_2344_; uint8_t v___y_2349_; uint8_t v___y_2354_; lean_object* v___y_2355_; lean_object* v_proof_2356_; uint8_t v___y_2361_; lean_object* v___y_2362_; lean_object* v___y_2363_; uint8_t v___y_2364_; lean_object* v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; uint8_t v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; uint8_t v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; uint8_t v___y_2384_; uint8_t v___y_2397_; uint8_t v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; uint8_t v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2419_; lean_object* v___y_2420_; uint8_t v___y_2421_; lean_object* v___y_2422_; uint8_t v___y_2423_; lean_object* v___y_2424_; uint8_t v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v_a_2431_; lean_object* v___y_2448_; lean_object* v___y_2449_; uint8_t v___y_2450_; uint8_t v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; uint8_t v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; uint8_t v___y_2464_; uint8_t v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; uint8_t v___y_2468_; lean_object* v___y_2469_; size_t v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; uint8_t v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; uint8_t v___y_2495_; size_t v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; uint8_t v_fst_2500_; lean_object* v_fst_2501_; lean_object* v_snd_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___x_2526_; uint8_t v___y_2528_; lean_object* v___x_2721_; uint8_t v___x_2722_; 
v___x_2526_ = lean_box(0);
v___x_2721_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__25));
v___x_2722_ = l_Lean_Expr_isAppOf(v_e_2068_, v___x_2721_);
if (v___x_2722_ == 0)
{
lean_object* v___x_2723_; uint8_t v___x_2724_; 
v___x_2723_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__27));
v___x_2724_ = l_Lean_Expr_isAppOf(v_e_2068_, v___x_2723_);
v___y_2528_ = v___x_2724_;
goto v___jp_2527_;
}
else
{
v___y_2528_ = v___x_2722_;
goto v___jp_2527_;
}
v___jp_2074_:
{
if (lean_obj_tag(v___y_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2084_; 
v_a_2076_ = lean_ctor_get(v___y_2075_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___y_2075_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2078_ = v___y_2075_;
v_isShared_2079_ = v_isSharedCheck_2084_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___y_2075_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2084_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v_a_2080_; lean_object* v___x_2082_; 
v_a_2080_ = lean_ctor_get(v_a_2076_, 0);
lean_inc(v_a_2080_);
lean_dec(v_a_2076_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v_a_2080_);
v___x_2082_ = v___x_2078_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2080_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
v_a_2085_ = lean_ctor_get(v___y_2075_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___y_2075_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___y_2075_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___y_2075_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
v___jp_2093_:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2095_ = lean_box(0);
lean_inc(v_a_2072_);
lean_inc_ref(v_a_2071_);
lean_inc(v_a_2070_);
lean_inc_ref(v_a_2069_);
v___x_2096_ = lean_apply_6(v___y_2094_, v___x_2095_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, lean_box(0));
v___y_2075_ = v___x_2096_;
goto v___jp_2074_;
}
v___jp_2097_:
{
if (v___y_2103_ == 0)
{
lean_object* v_toCold_2104_; lean_object* v_options_2105_; uint8_t v_hasTrace_2106_; 
v_toCold_2104_ = lean_ctor_get(v_a_2071_, 0);
v_options_2105_ = lean_ctor_get(v_toCold_2104_, 2);
v_hasTrace_2106_ = lean_ctor_get_uint8(v_options_2105_, sizeof(void*)*1);
if (v_hasTrace_2106_ == 0)
{
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2099_);
v___y_2094_ = v___y_2100_;
goto v___jp_2093_;
}
else
{
lean_object* v_inheritedTraceOptions_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; uint8_t v___x_2110_; 
v_inheritedTraceOptions_2107_ = lean_ctor_get(v_toCold_2104_, 11);
v___x_2108_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2099_);
v___x_2109_ = l_Lean_Name_append(v___x_2108_, v___y_2099_);
v___x_2110_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2107_, v_options_2105_, v___x_2109_);
lean_dec(v___x_2109_);
if (v___x_2110_ == 0)
{
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2099_);
v___y_2094_ = v___y_2100_;
goto v___jp_2093_;
}
else
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2111_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__3, &l_Lean_Meta_rwMatcher___closed__3_once, _init_l_Lean_Meta_rwMatcher___closed__3);
v___x_2112_ = l_Lean_MessageData_ofConstName(v___y_2102_, v___y_2098_);
v___x_2113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2111_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
v___x_2114_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__5, &l_Lean_Meta_rwMatcher___closed__5_once, _init_l_Lean_Meta_rwMatcher___closed__5);
v___x_2115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2113_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
v___x_2116_ = l_Lean_Exception_toMessageData(v___y_2101_);
v___x_2117_ = l_Lean_indentD(v___x_2116_);
v___x_2118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2115_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
v___x_2119_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2099_, v___x_2118_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v___x_2121_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2120_);
lean_dec_ref_known(v___x_2119_, 1);
lean_inc(v_a_2072_);
lean_inc_ref(v_a_2071_);
lean_inc(v_a_2070_);
lean_inc_ref(v_a_2069_);
v___x_2121_ = lean_apply_6(v___y_2100_, v_a_2120_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, lean_box(0));
v___y_2075_ = v___x_2121_;
goto v___jp_2074_;
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec_ref(v___y_2100_);
v_a_2122_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2119_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2119_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
}
}
else
{
lean_object* v___x_2130_; 
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
v___x_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2130_, 0, v___y_2101_);
return v___x_2130_;
}
}
v___jp_2131_:
{
uint8_t v___x_2137_; 
v___x_2137_ = l_Lean_Exception_isInterrupt(v_a_2136_);
if (v___x_2137_ == 0)
{
uint8_t v___x_2138_; 
lean_inc_ref(v_a_2136_);
v___x_2138_ = l_Lean_Exception_isRuntime(v_a_2136_);
v___y_2098_ = v___y_2132_;
v___y_2099_ = v___y_2133_;
v___y_2100_ = v___y_2134_;
v___y_2101_ = v_a_2136_;
v___y_2102_ = v___y_2135_;
v___y_2103_ = v___x_2138_;
goto v___jp_2097_;
}
else
{
v___y_2098_ = v___y_2132_;
v___y_2099_ = v___y_2133_;
v___y_2100_ = v___y_2134_;
v___y_2101_ = v_a_2136_;
v___y_2102_ = v___y_2135_;
v___y_2103_ = v___x_2137_;
goto v___jp_2097_;
}
}
v___jp_2139_:
{
if (lean_obj_tag(v___y_2144_) == 0)
{
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v___y_2141_);
return v___y_2144_;
}
else
{
lean_object* v_a_2145_; 
v_a_2145_ = lean_ctor_get(v___y_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___y_2144_, 1);
v___y_2132_ = v___y_2140_;
v___y_2133_ = v___y_2141_;
v___y_2134_ = v___y_2142_;
v___y_2135_ = v___y_2143_;
v_a_2136_ = v_a_2145_;
goto v___jp_2131_;
}
}
v___jp_2146_:
{
lean_object* v___x_2159_; double v___x_2160_; double v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2159_ = lean_io_get_num_heartbeats();
v___x_2160_ = lean_float_of_nat(v___y_2156_);
v___x_2161_ = lean_float_of_nat(v___x_2159_);
v___x_2162_ = lean_box_float(v___x_2160_);
v___x_2163_ = lean_box_float(v___x_2161_);
v___x_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2162_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
v___x_2165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2165_, 0, v_a_2158_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
lean_inc_ref(v___y_2155_);
lean_inc(v___y_2149_);
v___x_2166_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v___y_2149_, v___y_2154_, v___y_2155_, v___y_2148_, v___y_2151_, v___y_2153_, v___y_2152_, v___x_2165_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
v___y_2140_ = v___y_2147_;
v___y_2141_ = v___y_2149_;
v___y_2142_ = v___y_2150_;
v___y_2143_ = v___y_2157_;
v___y_2144_ = v___x_2166_;
goto v___jp_2139_;
}
v___jp_2167_:
{
lean_object* v___x_2180_; 
v___x_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2180_, 0, v_a_2179_);
v___y_2147_ = v___y_2169_;
v___y_2148_ = v___y_2168_;
v___y_2149_ = v___y_2170_;
v___y_2150_ = v___y_2172_;
v___y_2151_ = v___y_2171_;
v___y_2152_ = v___y_2174_;
v___y_2153_ = v___y_2173_;
v___y_2154_ = v___y_2175_;
v___y_2155_ = v___y_2176_;
v___y_2156_ = v___y_2177_;
v___y_2157_ = v___y_2178_;
v_a_2158_ = v___x_2180_;
goto v___jp_2146_;
}
v___jp_2181_:
{
if (lean_obj_tag(v___y_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
v_a_2194_ = lean_ctor_get(v___y_2193_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___y_2193_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___y_2193_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___y_2193_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
lean_ctor_set_tag(v___x_2196_, 1);
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
v___y_2147_ = v___y_2183_;
v___y_2148_ = v___y_2182_;
v___y_2149_ = v___y_2184_;
v___y_2150_ = v___y_2186_;
v___y_2151_ = v___y_2185_;
v___y_2152_ = v___y_2188_;
v___y_2153_ = v___y_2187_;
v___y_2154_ = v___y_2189_;
v___y_2155_ = v___y_2190_;
v___y_2156_ = v___y_2191_;
v___y_2157_ = v___y_2192_;
v_a_2158_ = v___x_2199_;
goto v___jp_2146_;
}
}
}
else
{
lean_object* v_a_2202_; 
v_a_2202_ = lean_ctor_get(v___y_2193_, 0);
lean_inc(v_a_2202_);
lean_dec_ref_known(v___y_2193_, 1);
v___y_2168_ = v___y_2182_;
v___y_2169_ = v___y_2183_;
v___y_2170_ = v___y_2184_;
v___y_2171_ = v___y_2185_;
v___y_2172_ = v___y_2186_;
v___y_2173_ = v___y_2187_;
v___y_2174_ = v___y_2188_;
v___y_2175_ = v___y_2189_;
v___y_2176_ = v___y_2190_;
v___y_2177_ = v___y_2191_;
v___y_2178_ = v___y_2192_;
v_a_2179_ = v_a_2202_;
goto v___jp_2167_;
}
}
v___jp_2203_:
{
lean_object* v___x_2216_; double v___x_2217_; double v___x_2218_; double v___x_2219_; double v___x_2220_; double v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2216_ = lean_io_mono_nanos_now();
v___x_2217_ = lean_float_of_nat(v___y_2212_);
v___x_2218_ = lean_float_once(&l_Lean_Meta_rwMatcher___closed__6, &l_Lean_Meta_rwMatcher___closed__6_once, _init_l_Lean_Meta_rwMatcher___closed__6);
v___x_2219_ = lean_float_div(v___x_2217_, v___x_2218_);
v___x_2220_ = lean_float_of_nat(v___x_2216_);
v___x_2221_ = lean_float_div(v___x_2220_, v___x_2218_);
v___x_2222_ = lean_box_float(v___x_2219_);
v___x_2223_ = lean_box_float(v___x_2221_);
v___x_2224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2222_);
lean_ctor_set(v___x_2224_, 1, v___x_2223_);
v___x_2225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2225_, 0, v_a_2215_);
lean_ctor_set(v___x_2225_, 1, v___x_2224_);
lean_inc_ref(v___y_2213_);
lean_inc(v___y_2206_);
v___x_2226_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v___y_2206_, v___y_2211_, v___y_2213_, v___y_2205_, v___y_2208_, v___y_2210_, v___y_2209_, v___x_2225_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
v___y_2140_ = v___y_2204_;
v___y_2141_ = v___y_2206_;
v___y_2142_ = v___y_2207_;
v___y_2143_ = v___y_2214_;
v___y_2144_ = v___x_2226_;
goto v___jp_2139_;
}
v___jp_2227_:
{
lean_object* v___x_2240_; 
v___x_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2240_, 0, v_a_2239_);
v___y_2204_ = v___y_2229_;
v___y_2205_ = v___y_2228_;
v___y_2206_ = v___y_2230_;
v___y_2207_ = v___y_2232_;
v___y_2208_ = v___y_2231_;
v___y_2209_ = v___y_2234_;
v___y_2210_ = v___y_2233_;
v___y_2211_ = v___y_2236_;
v___y_2212_ = v___y_2235_;
v___y_2213_ = v___y_2237_;
v___y_2214_ = v___y_2238_;
v_a_2215_ = v___x_2240_;
goto v___jp_2203_;
}
v___jp_2241_:
{
if (lean_obj_tag(v___y_2253_) == 0)
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
v_a_2254_ = lean_ctor_get(v___y_2253_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___y_2253_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___y_2253_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___y_2253_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
lean_ctor_set_tag(v___x_2256_, 1);
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2254_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
v___y_2204_ = v___y_2243_;
v___y_2205_ = v___y_2242_;
v___y_2206_ = v___y_2244_;
v___y_2207_ = v___y_2246_;
v___y_2208_ = v___y_2245_;
v___y_2209_ = v___y_2248_;
v___y_2210_ = v___y_2247_;
v___y_2211_ = v___y_2250_;
v___y_2212_ = v___y_2249_;
v___y_2213_ = v___y_2251_;
v___y_2214_ = v___y_2252_;
v_a_2215_ = v___x_2259_;
goto v___jp_2203_;
}
}
}
else
{
lean_object* v_a_2262_; 
v_a_2262_ = lean_ctor_get(v___y_2253_, 0);
lean_inc(v_a_2262_);
lean_dec_ref_known(v___y_2253_, 1);
v___y_2228_ = v___y_2242_;
v___y_2229_ = v___y_2243_;
v___y_2230_ = v___y_2244_;
v___y_2231_ = v___y_2245_;
v___y_2232_ = v___y_2246_;
v___y_2233_ = v___y_2247_;
v___y_2234_ = v___y_2248_;
v___y_2235_ = v___y_2249_;
v___y_2236_ = v___y_2250_;
v___y_2237_ = v___y_2251_;
v___y_2238_ = v___y_2252_;
v_a_2239_ = v_a_2262_;
goto v___jp_2227_;
}
}
v___jp_2263_:
{
lean_object* v___x_2279_; lean_object* v_a_2280_; lean_object* v___x_2281_; uint8_t v___x_2282_; 
v___x_2279_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg(v_a_2072_);
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref(v___x_2279_);
v___x_2281_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2282_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v___y_2271_, v___x_2281_);
if (v___x_2282_ == 0)
{
lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2283_ = lean_io_mono_nanos_now();
lean_inc(v_a_2072_);
lean_inc_ref(v_a_2071_);
lean_inc(v_a_2070_);
lean_inc_ref(v_a_2069_);
v___x_2284_ = lean_infer_type(v___y_2273_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; uint8_t v___x_2286_; lean_object* v___x_2287_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2285_);
lean_dec_ref_known(v___x_2284_, 1);
v___x_2286_ = 0;
v___x_2287_ = l_Lean_Meta_forallMetaTelescope(v_a_2285_, v___x_2286_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v_snd_2289_; lean_object* v_fst_2290_; lean_object* v_snd_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2309_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref_known(v___x_2287_, 1);
v_snd_2289_ = lean_ctor_get(v_a_2288_, 1);
lean_inc(v_snd_2289_);
v_fst_2290_ = lean_ctor_get(v_a_2288_, 0);
lean_inc(v_fst_2290_);
lean_dec(v_a_2288_);
v_snd_2291_ = lean_ctor_get(v_snd_2289_, 1);
v_isSharedCheck_2309_ = !lean_is_exclusive(v_snd_2289_);
if (v_isSharedCheck_2309_ == 0)
{
lean_object* v_unused_2310_; 
v_unused_2310_ = lean_ctor_get(v_snd_2289_, 0);
lean_dec(v_unused_2310_);
v___x_2293_ = v_snd_2289_;
v_isShared_2294_ = v_isSharedCheck_2309_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_snd_2291_);
lean_dec(v_snd_2289_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2309_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; uint8_t v___x_2297_; 
v___x_2295_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2272_);
v___x_2296_ = l_Lean_Name_append(v___x_2295_, v___y_2272_);
v___x_2297_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2269_, v___y_2271_, v___x_2296_);
lean_dec(v___x_2296_);
if (v___x_2297_ == 0)
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
lean_del_object(v___x_2293_);
v___x_2298_ = lean_box(0);
v___x_2299_ = l_Lean_Meta_rwMatcher___lam__2(v___y_2267_, v___y_2265_, v_fst_2290_, v___y_2268_, v_e_2068_, v___y_2264_, v_snd_2291_, v___x_2298_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
lean_dec(v_snd_2291_);
v___y_2242_ = v___y_2271_;
v___y_2243_ = v___y_2270_;
v___y_2244_ = v___y_2272_;
v___y_2245_ = v___y_2274_;
v___y_2246_ = v___y_2275_;
v___y_2247_ = v_a_2280_;
v___y_2248_ = v___y_2266_;
v___y_2249_ = v___x_2283_;
v___y_2250_ = v___y_2276_;
v___y_2251_ = v___y_2277_;
v___y_2252_ = v___y_2278_;
v___y_2253_ = v___x_2299_;
goto v___jp_2241_;
}
else
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2303_; 
v___x_2300_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2291_);
v___x_2301_ = l_Lean_indentExpr(v_snd_2291_);
if (v_isShared_2294_ == 0)
{
lean_ctor_set_tag(v___x_2293_, 7);
lean_ctor_set(v___x_2293_, 1, v___x_2301_);
lean_ctor_set(v___x_2293_, 0, v___x_2300_);
v___x_2303_ = v___x_2293_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v___x_2301_);
v___x_2303_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
lean_object* v___x_2304_; 
lean_inc(v___y_2272_);
v___x_2304_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2272_, v___x_2303_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; lean_object* v___x_2306_; 
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2305_);
lean_dec_ref_known(v___x_2304_, 1);
v___x_2306_ = l_Lean_Meta_rwMatcher___lam__2(v___y_2267_, v___y_2265_, v_fst_2290_, v___y_2268_, v_e_2068_, v___y_2264_, v_snd_2291_, v_a_2305_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
lean_dec(v_snd_2291_);
v___y_2242_ = v___y_2271_;
v___y_2243_ = v___y_2270_;
v___y_2244_ = v___y_2272_;
v___y_2245_ = v___y_2274_;
v___y_2246_ = v___y_2275_;
v___y_2247_ = v_a_2280_;
v___y_2248_ = v___y_2266_;
v___y_2249_ = v___x_2283_;
v___y_2250_ = v___y_2276_;
v___y_2251_ = v___y_2277_;
v___y_2252_ = v___y_2278_;
v___y_2253_ = v___x_2306_;
goto v___jp_2241_;
}
else
{
lean_object* v_a_2307_; 
lean_dec(v_snd_2291_);
lean_dec(v_fst_2290_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2265_);
lean_dec_ref(v_e_2068_);
v_a_2307_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v___x_2304_, 1);
v___y_2228_ = v___y_2271_;
v___y_2229_ = v___y_2270_;
v___y_2230_ = v___y_2272_;
v___y_2231_ = v___y_2274_;
v___y_2232_ = v___y_2275_;
v___y_2233_ = v_a_2280_;
v___y_2234_ = v___y_2266_;
v___y_2235_ = v___x_2283_;
v___y_2236_ = v___y_2276_;
v___y_2237_ = v___y_2277_;
v___y_2238_ = v___y_2278_;
v_a_2239_ = v_a_2307_;
goto v___jp_2227_;
}
}
}
}
}
else
{
lean_object* v_a_2311_; 
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2265_);
lean_dec_ref(v_e_2068_);
v_a_2311_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2311_);
lean_dec_ref_known(v___x_2287_, 1);
v___y_2228_ = v___y_2271_;
v___y_2229_ = v___y_2270_;
v___y_2230_ = v___y_2272_;
v___y_2231_ = v___y_2274_;
v___y_2232_ = v___y_2275_;
v___y_2233_ = v_a_2280_;
v___y_2234_ = v___y_2266_;
v___y_2235_ = v___x_2283_;
v___y_2236_ = v___y_2276_;
v___y_2237_ = v___y_2277_;
v___y_2238_ = v___y_2278_;
v_a_2239_ = v_a_2311_;
goto v___jp_2227_;
}
}
else
{
lean_object* v_a_2312_; 
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2265_);
lean_dec_ref(v_e_2068_);
v_a_2312_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2312_);
lean_dec_ref_known(v___x_2284_, 1);
v___y_2228_ = v___y_2271_;
v___y_2229_ = v___y_2270_;
v___y_2230_ = v___y_2272_;
v___y_2231_ = v___y_2274_;
v___y_2232_ = v___y_2275_;
v___y_2233_ = v_a_2280_;
v___y_2234_ = v___y_2266_;
v___y_2235_ = v___x_2283_;
v___y_2236_ = v___y_2276_;
v___y_2237_ = v___y_2277_;
v___y_2238_ = v___y_2278_;
v_a_2239_ = v_a_2312_;
goto v___jp_2227_;
}
}
else
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2072_);
lean_inc_ref(v_a_2071_);
lean_inc(v_a_2070_);
lean_inc_ref(v_a_2069_);
v___x_2314_ = lean_infer_type(v___y_2273_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; uint8_t v___x_2316_; lean_object* v___x_2317_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2315_);
lean_dec_ref_known(v___x_2314_, 1);
v___x_2316_ = 0;
v___x_2317_ = l_Lean_Meta_forallMetaTelescope(v_a_2315_, v___x_2316_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v_snd_2319_; lean_object* v_fst_2320_; lean_object* v_snd_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2339_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2318_);
lean_dec_ref_known(v___x_2317_, 1);
v_snd_2319_ = lean_ctor_get(v_a_2318_, 1);
lean_inc(v_snd_2319_);
v_fst_2320_ = lean_ctor_get(v_a_2318_, 0);
lean_inc(v_fst_2320_);
lean_dec(v_a_2318_);
v_snd_2321_ = lean_ctor_get(v_snd_2319_, 1);
v_isSharedCheck_2339_ = !lean_is_exclusive(v_snd_2319_);
if (v_isSharedCheck_2339_ == 0)
{
lean_object* v_unused_2340_; 
v_unused_2340_ = lean_ctor_get(v_snd_2319_, 0);
lean_dec(v_unused_2340_);
v___x_2323_ = v_snd_2319_;
v_isShared_2324_ = v_isSharedCheck_2339_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_snd_2321_);
lean_dec(v_snd_2319_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2339_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; uint8_t v___x_2327_; 
v___x_2325_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2272_);
v___x_2326_ = l_Lean_Name_append(v___x_2325_, v___y_2272_);
v___x_2327_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2269_, v___y_2271_, v___x_2326_);
lean_dec(v___x_2326_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
lean_del_object(v___x_2323_);
v___x_2328_ = lean_box(0);
v___x_2329_ = l_Lean_Meta_rwMatcher___lam__3(v___y_2267_, v___y_2265_, v_fst_2320_, v___y_2268_, v_e_2068_, v___y_2264_, v_snd_2321_, v___x_2328_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
lean_dec(v_snd_2321_);
v___y_2182_ = v___y_2271_;
v___y_2183_ = v___y_2270_;
v___y_2184_ = v___y_2272_;
v___y_2185_ = v___y_2274_;
v___y_2186_ = v___y_2275_;
v___y_2187_ = v_a_2280_;
v___y_2188_ = v___y_2266_;
v___y_2189_ = v___y_2276_;
v___y_2190_ = v___y_2277_;
v___y_2191_ = v___x_2313_;
v___y_2192_ = v___y_2278_;
v___y_2193_ = v___x_2329_;
goto v___jp_2181_;
}
else
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2333_; 
v___x_2330_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2321_);
v___x_2331_ = l_Lean_indentExpr(v_snd_2321_);
if (v_isShared_2324_ == 0)
{
lean_ctor_set_tag(v___x_2323_, 7);
lean_ctor_set(v___x_2323_, 1, v___x_2331_);
lean_ctor_set(v___x_2323_, 0, v___x_2330_);
v___x_2333_ = v___x_2323_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2330_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2334_; 
lean_inc(v___y_2272_);
v___x_2334_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2272_, v___x_2333_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v___x_2336_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2334_, 1);
v___x_2336_ = l_Lean_Meta_rwMatcher___lam__3(v___y_2267_, v___y_2265_, v_fst_2320_, v___y_2268_, v_e_2068_, v___y_2264_, v_snd_2321_, v_a_2335_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
lean_dec(v_snd_2321_);
v___y_2182_ = v___y_2271_;
v___y_2183_ = v___y_2270_;
v___y_2184_ = v___y_2272_;
v___y_2185_ = v___y_2274_;
v___y_2186_ = v___y_2275_;
v___y_2187_ = v_a_2280_;
v___y_2188_ = v___y_2266_;
v___y_2189_ = v___y_2276_;
v___y_2190_ = v___y_2277_;
v___y_2191_ = v___x_2313_;
v___y_2192_ = v___y_2278_;
v___y_2193_ = v___x_2336_;
goto v___jp_2181_;
}
else
{
lean_object* v_a_2337_; 
lean_dec(v_snd_2321_);
lean_dec(v_fst_2320_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2265_);
lean_dec_ref(v_e_2068_);
v_a_2337_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2334_, 1);
v___y_2168_ = v___y_2271_;
v___y_2169_ = v___y_2270_;
v___y_2170_ = v___y_2272_;
v___y_2171_ = v___y_2274_;
v___y_2172_ = v___y_2275_;
v___y_2173_ = v_a_2280_;
v___y_2174_ = v___y_2266_;
v___y_2175_ = v___y_2276_;
v___y_2176_ = v___y_2277_;
v___y_2177_ = v___x_2313_;
v___y_2178_ = v___y_2278_;
v_a_2179_ = v_a_2337_;
goto v___jp_2167_;
}
}
}
}
}
else
{
lean_object* v_a_2341_; 
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2265_);
lean_dec_ref(v_e_2068_);
v_a_2341_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2341_);
lean_dec_ref_known(v___x_2317_, 1);
v___y_2168_ = v___y_2271_;
v___y_2169_ = v___y_2270_;
v___y_2170_ = v___y_2272_;
v___y_2171_ = v___y_2274_;
v___y_2172_ = v___y_2275_;
v___y_2173_ = v_a_2280_;
v___y_2174_ = v___y_2266_;
v___y_2175_ = v___y_2276_;
v___y_2176_ = v___y_2277_;
v___y_2177_ = v___x_2313_;
v___y_2178_ = v___y_2278_;
v_a_2179_ = v_a_2341_;
goto v___jp_2167_;
}
}
else
{
lean_object* v_a_2342_; 
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2265_);
lean_dec_ref(v_e_2068_);
v_a_2342_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2342_);
lean_dec_ref_known(v___x_2314_, 1);
v___y_2168_ = v___y_2271_;
v___y_2169_ = v___y_2270_;
v___y_2170_ = v___y_2272_;
v___y_2171_ = v___y_2274_;
v___y_2172_ = v___y_2275_;
v___y_2173_ = v_a_2280_;
v___y_2174_ = v___y_2266_;
v___y_2175_ = v___y_2276_;
v___y_2176_ = v___y_2277_;
v___y_2177_ = v___x_2313_;
v___y_2178_ = v___y_2278_;
v_a_2179_ = v_a_2342_;
goto v___jp_2167_;
}
}
}
v___jp_2343_:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2345_ = lean_box(0);
v___x_2346_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2346_, 0, v_e_2068_);
lean_ctor_set(v___x_2346_, 1, v___x_2345_);
lean_ctor_set_uint8(v___x_2346_, sizeof(void*)*2, v___y_2344_);
v___x_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2346_);
return v___x_2347_;
}
v___jp_2348_:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2350_ = lean_box(0);
v___x_2351_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2351_, 0, v_e_2068_);
lean_ctor_set(v___x_2351_, 1, v___x_2350_);
lean_ctor_set_uint8(v___x_2351_, sizeof(void*)*2, v___y_2349_);
v___x_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
return v___x_2352_;
}
v___jp_2353_:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2357_, 0, v_proof_2356_);
v___x_2358_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2358_, 0, v___y_2355_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
lean_ctor_set_uint8(v___x_2358_, sizeof(void*)*2, v___y_2354_);
v___x_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
return v___x_2359_;
}
v___jp_2360_:
{
if (lean_obj_tag(v___y_2367_) == 0)
{
lean_object* v_a_2368_; 
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
v_a_2368_ = lean_ctor_get(v___y_2367_, 0);
lean_inc(v_a_2368_);
lean_dec_ref_known(v___y_2367_, 1);
v___y_2354_ = v___y_2364_;
v___y_2355_ = v___y_2365_;
v_proof_2356_ = v_a_2368_;
goto v___jp_2353_;
}
else
{
lean_object* v_a_2369_; 
lean_dec_ref(v___y_2365_);
v_a_2369_ = lean_ctor_get(v___y_2367_, 0);
lean_inc(v_a_2369_);
lean_dec_ref_known(v___y_2367_, 1);
v___y_2132_ = v___y_2361_;
v___y_2133_ = v___y_2362_;
v___y_2134_ = v___y_2363_;
v___y_2135_ = v___y_2366_;
v_a_2136_ = v_a_2369_;
goto v___jp_2131_;
}
}
v___jp_2370_:
{
if (v___y_2384_ == 0)
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
lean_dec_ref(v___y_2381_);
v___x_2385_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_2386_ = l_Lean_MessageData_ofExpr(v___y_2373_);
v___x_2387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2385_);
lean_ctor_set(v___x_2387_, 1, v___x_2386_);
v___x_2388_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_2389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2387_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
v___x_2390_ = l_Lean_Exception_toMessageData(v___y_2375_);
v___x_2391_ = l_Lean_indentD(v___x_2390_);
v___x_2392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2389_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
v___x_2393_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_2394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2392_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
v___x_2395_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2394_, v___y_2378_, v___y_2376_, v___y_2372_, v___y_2382_);
v___y_2361_ = v___y_2371_;
v___y_2362_ = v___y_2377_;
v___y_2363_ = v___y_2379_;
v___y_2364_ = v___y_2380_;
v___y_2365_ = v___y_2374_;
v___y_2366_ = v___y_2383_;
v___y_2367_ = v___x_2395_;
goto v___jp_2360_;
}
else
{
lean_dec_ref(v___y_2375_);
lean_dec_ref(v___y_2373_);
v___y_2361_ = v___y_2371_;
v___y_2362_ = v___y_2377_;
v___y_2363_ = v___y_2379_;
v___y_2364_ = v___y_2380_;
v___y_2365_ = v___y_2374_;
v___y_2366_ = v___y_2383_;
v___y_2367_ = v___y_2381_;
goto v___jp_2360_;
}
}
v___jp_2396_:
{
lean_object* v___x_2409_; lean_object* v_a_2410_; lean_object* v___x_2411_; 
v___x_2409_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_2402_, v___y_2406_);
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_a_2410_);
lean_dec_ref(v___x_2409_);
v___x_2411_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_2403_, v___y_2406_);
if (v___y_2398_ == 0)
{
lean_object* v_a_2412_; 
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2412_);
lean_dec_ref(v___x_2411_);
v___y_2354_ = v___y_2401_;
v___y_2355_ = v_a_2410_;
v_proof_2356_ = v_a_2412_;
goto v___jp_2353_;
}
else
{
lean_object* v_a_2413_; lean_object* v___x_2414_; 
v_a_2413_ = lean_ctor_get(v___x_2411_, 0);
lean_inc_n(v_a_2413_, 2);
lean_dec_ref(v___x_2411_);
v___x_2414_ = l_Lean_Meta_mkEqOfHEq(v_a_2413_, v___y_2401_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_dec(v_a_2413_);
v___y_2361_ = v___y_2397_;
v___y_2362_ = v___y_2399_;
v___y_2363_ = v___y_2400_;
v___y_2364_ = v___y_2401_;
v___y_2365_ = v_a_2410_;
v___y_2366_ = v___y_2404_;
v___y_2367_ = v___x_2414_;
goto v___jp_2360_;
}
else
{
lean_object* v_a_2415_; uint8_t v___x_2416_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_a_2415_);
v___x_2416_ = l_Lean_Exception_isInterrupt(v_a_2415_);
if (v___x_2416_ == 0)
{
uint8_t v___x_2417_; 
lean_inc(v_a_2415_);
v___x_2417_ = l_Lean_Exception_isRuntime(v_a_2415_);
v___y_2371_ = v___y_2397_;
v___y_2372_ = v___y_2407_;
v___y_2373_ = v_a_2413_;
v___y_2374_ = v_a_2410_;
v___y_2375_ = v_a_2415_;
v___y_2376_ = v___y_2406_;
v___y_2377_ = v___y_2399_;
v___y_2378_ = v___y_2405_;
v___y_2379_ = v___y_2400_;
v___y_2380_ = v___y_2401_;
v___y_2381_ = v___x_2414_;
v___y_2382_ = v___y_2408_;
v___y_2383_ = v___y_2404_;
v___y_2384_ = v___x_2417_;
goto v___jp_2370_;
}
else
{
v___y_2371_ = v___y_2397_;
v___y_2372_ = v___y_2407_;
v___y_2373_ = v_a_2413_;
v___y_2374_ = v_a_2410_;
v___y_2375_ = v_a_2415_;
v___y_2376_ = v___y_2406_;
v___y_2377_ = v___y_2399_;
v___y_2378_ = v___y_2405_;
v___y_2379_ = v___y_2400_;
v___y_2380_ = v___y_2401_;
v___y_2381_ = v___x_2414_;
v___y_2382_ = v___y_2408_;
v___y_2383_ = v___y_2404_;
v___y_2384_ = v___x_2416_;
goto v___jp_2370_;
}
}
}
}
v___jp_2418_:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; uint8_t v___x_2434_; 
v___x_2432_ = lean_array_get_size(v_a_2431_);
v___x_2433_ = lean_unsigned_to_nat(0u);
v___x_2434_ = lean_nat_dec_eq(v___x_2432_, v___x_2433_);
if (v___x_2434_ == 0)
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v_a_2446_; 
lean_dec_ref(v___y_2429_);
lean_dec_ref(v___y_2427_);
v___x_2435_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
lean_inc(v___y_2430_);
v___x_2436_ = l_Lean_MessageData_ofConstName(v___y_2430_, v___x_2434_);
v___x_2437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2435_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
v___x_2438_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_2439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2437_);
lean_ctor_set(v___x_2439_, 1, v___x_2438_);
v___x_2440_ = lean_array_to_list(v_a_2431_);
v___x_2441_ = lean_box(0);
v___x_2442_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_2440_, v___x_2441_);
v___x_2443_ = l_Lean_MessageData_ofList(v___x_2442_);
v___x_2444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2439_);
lean_ctor_set(v___x_2444_, 1, v___x_2443_);
v___x_2445_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2444_, v___y_2426_, v___y_2419_, v___y_2428_, v___y_2420_);
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_a_2446_);
lean_dec_ref(v___x_2445_);
v___y_2132_ = v___y_2421_;
v___y_2133_ = v___y_2422_;
v___y_2134_ = v___y_2424_;
v___y_2135_ = v___y_2430_;
v_a_2136_ = v_a_2446_;
goto v___jp_2131_;
}
else
{
lean_dec_ref(v_a_2431_);
v___y_2397_ = v___y_2421_;
v___y_2398_ = v___y_2423_;
v___y_2399_ = v___y_2422_;
v___y_2400_ = v___y_2424_;
v___y_2401_ = v___y_2425_;
v___y_2402_ = v___y_2427_;
v___y_2403_ = v___y_2429_;
v___y_2404_ = v___y_2430_;
v___y_2405_ = v___y_2426_;
v___y_2406_ = v___y_2419_;
v___y_2407_ = v___y_2428_;
v___y_2408_ = v___y_2420_;
goto v___jp_2396_;
}
}
v___jp_2447_:
{
if (lean_obj_tag(v___y_2460_) == 0)
{
lean_object* v_a_2461_; 
v_a_2461_ = lean_ctor_get(v___y_2460_, 0);
lean_inc(v_a_2461_);
lean_dec_ref_known(v___y_2460_, 1);
v___y_2419_ = v___y_2448_;
v___y_2420_ = v___y_2449_;
v___y_2421_ = v___y_2450_;
v___y_2422_ = v___y_2452_;
v___y_2423_ = v___y_2451_;
v___y_2424_ = v___y_2453_;
v___y_2425_ = v___y_2455_;
v___y_2426_ = v___y_2454_;
v___y_2427_ = v___y_2456_;
v___y_2428_ = v___y_2457_;
v___y_2429_ = v___y_2458_;
v___y_2430_ = v___y_2459_;
v_a_2431_ = v_a_2461_;
goto v___jp_2418_;
}
else
{
lean_object* v_a_2462_; 
lean_dec_ref(v___y_2458_);
lean_dec_ref(v___y_2456_);
v_a_2462_ = lean_ctor_get(v___y_2460_, 0);
lean_inc(v_a_2462_);
lean_dec_ref_known(v___y_2460_, 1);
v___y_2132_ = v___y_2450_;
v___y_2133_ = v___y_2452_;
v___y_2134_ = v___y_2453_;
v___y_2135_ = v___y_2459_;
v_a_2136_ = v_a_2462_;
goto v___jp_2131_;
}
}
v___jp_2463_:
{
lean_object* v___x_2478_; size_t v_sz_2479_; lean_object* v___x_2480_; 
v___x_2478_ = lean_box(0);
v_sz_2479_ = lean_array_size(v___y_2471_);
v___x_2480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___y_2471_, v_sz_2479_, v___y_2470_, v___x_2478_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; uint8_t v___x_2484_; 
lean_dec_ref_known(v___x_2480_, 1);
v___x_2481_ = lean_unsigned_to_nat(0u);
v___x_2482_ = lean_array_get_size(v___y_2471_);
v___x_2483_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_2484_ = lean_nat_dec_lt(v___x_2481_, v___x_2482_);
if (v___x_2484_ == 0)
{
lean_dec_ref(v___y_2471_);
v___y_2419_ = v___y_2475_;
v___y_2420_ = v___y_2477_;
v___y_2421_ = v___y_2464_;
v___y_2422_ = v___y_2466_;
v___y_2423_ = v___y_2465_;
v___y_2424_ = v___y_2467_;
v___y_2425_ = v___y_2468_;
v___y_2426_ = v___y_2474_;
v___y_2427_ = v___y_2469_;
v___y_2428_ = v___y_2476_;
v___y_2429_ = v___y_2472_;
v___y_2430_ = v___y_2473_;
v_a_2431_ = v___x_2483_;
goto v___jp_2418_;
}
else
{
uint8_t v___x_2485_; 
v___x_2485_ = lean_nat_dec_le(v___x_2482_, v___x_2482_);
if (v___x_2485_ == 0)
{
if (v___x_2484_ == 0)
{
lean_dec_ref(v___y_2471_);
v___y_2419_ = v___y_2475_;
v___y_2420_ = v___y_2477_;
v___y_2421_ = v___y_2464_;
v___y_2422_ = v___y_2466_;
v___y_2423_ = v___y_2465_;
v___y_2424_ = v___y_2467_;
v___y_2425_ = v___y_2468_;
v___y_2426_ = v___y_2474_;
v___y_2427_ = v___y_2469_;
v___y_2428_ = v___y_2476_;
v___y_2429_ = v___y_2472_;
v___y_2430_ = v___y_2473_;
v_a_2431_ = v___x_2483_;
goto v___jp_2418_;
}
else
{
size_t v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = lean_usize_of_nat(v___x_2482_);
v___x_2487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___y_2471_, v___y_2470_, v___x_2486_, v___x_2483_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
lean_dec_ref(v___y_2471_);
v___y_2448_ = v___y_2475_;
v___y_2449_ = v___y_2477_;
v___y_2450_ = v___y_2464_;
v___y_2451_ = v___y_2465_;
v___y_2452_ = v___y_2466_;
v___y_2453_ = v___y_2467_;
v___y_2454_ = v___y_2474_;
v___y_2455_ = v___y_2468_;
v___y_2456_ = v___y_2469_;
v___y_2457_ = v___y_2476_;
v___y_2458_ = v___y_2472_;
v___y_2459_ = v___y_2473_;
v___y_2460_ = v___x_2487_;
goto v___jp_2447_;
}
}
else
{
size_t v___x_2488_; lean_object* v___x_2489_; 
v___x_2488_ = lean_usize_of_nat(v___x_2482_);
v___x_2489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___y_2471_, v___y_2470_, v___x_2488_, v___x_2483_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
lean_dec_ref(v___y_2471_);
v___y_2448_ = v___y_2475_;
v___y_2449_ = v___y_2477_;
v___y_2450_ = v___y_2464_;
v___y_2451_ = v___y_2465_;
v___y_2452_ = v___y_2466_;
v___y_2453_ = v___y_2467_;
v___y_2454_ = v___y_2474_;
v___y_2455_ = v___y_2468_;
v___y_2456_ = v___y_2469_;
v___y_2457_ = v___y_2476_;
v___y_2458_ = v___y_2472_;
v___y_2459_ = v___y_2473_;
v___y_2460_ = v___x_2489_;
goto v___jp_2447_;
}
}
}
else
{
lean_object* v_a_2490_; 
lean_dec_ref(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec_ref(v___y_2469_);
v_a_2490_ = lean_ctor_get(v___x_2480_, 0);
lean_inc(v_a_2490_);
lean_dec_ref_known(v___x_2480_, 1);
v___y_2132_ = v___y_2464_;
v___y_2133_ = v___y_2466_;
v___y_2134_ = v___y_2467_;
v___y_2135_ = v___y_2473_;
v_a_2136_ = v_a_2490_;
goto v___jp_2131_;
}
}
v___jp_2491_:
{
lean_object* v___x_2507_; 
lean_inc_ref(v_fst_2501_);
lean_inc_ref(v_e_2068_);
v___x_2507_ = l_Lean_Meta_isExprDefEq(v_e_2068_, v_fst_2501_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; uint8_t v___x_2509_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_a_2508_);
lean_dec_ref_known(v___x_2507_, 1);
v___x_2509_ = lean_unbox(v_a_2508_);
lean_dec(v_a_2508_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v_a_2524_; 
lean_dec_ref(v_snd_2502_);
lean_dec_ref(v___y_2498_);
lean_dec_ref(v___y_2497_);
v___x_2510_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_2511_ = l_Lean_MessageData_ofExpr(v_fst_2501_);
v___x_2512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2510_);
lean_ctor_set(v___x_2512_, 1, v___x_2511_);
v___x_2513_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_2514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2512_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
lean_inc(v___y_2499_);
v___x_2515_ = l_Lean_MessageData_ofConstName(v___y_2499_, v___y_2492_);
v___x_2516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2514_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
v___x_2517_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_2518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2516_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = l_Lean_MessageData_ofExpr(v_e_2068_);
v___x_2520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2518_);
lean_ctor_set(v___x_2520_, 1, v___x_2519_);
v___x_2521_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_2522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2520_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
v___x_2523_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2522_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2524_);
lean_dec_ref(v___x_2523_);
v___y_2132_ = v___y_2492_;
v___y_2133_ = v___y_2493_;
v___y_2134_ = v___y_2494_;
v___y_2135_ = v___y_2499_;
v_a_2136_ = v_a_2524_;
goto v___jp_2131_;
}
else
{
lean_dec_ref(v_fst_2501_);
lean_dec_ref(v_e_2068_);
v___y_2464_ = v___y_2492_;
v___y_2465_ = v_fst_2500_;
v___y_2466_ = v___y_2493_;
v___y_2467_ = v___y_2494_;
v___y_2468_ = v___y_2495_;
v___y_2469_ = v_snd_2502_;
v___y_2470_ = v___y_2496_;
v___y_2471_ = v___y_2497_;
v___y_2472_ = v___y_2498_;
v___y_2473_ = v___y_2499_;
v___y_2474_ = v___y_2503_;
v___y_2475_ = v___y_2504_;
v___y_2476_ = v___y_2505_;
v___y_2477_ = v___y_2506_;
goto v___jp_2463_;
}
}
else
{
lean_object* v_a_2525_; 
lean_dec_ref(v_snd_2502_);
lean_dec_ref(v_fst_2501_);
lean_dec_ref(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec_ref(v_e_2068_);
v_a_2525_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_a_2525_);
lean_dec_ref_known(v___x_2507_, 1);
v___y_2132_ = v___y_2492_;
v___y_2133_ = v___y_2493_;
v___y_2134_ = v___y_2494_;
v___y_2135_ = v___y_2499_;
v_a_2136_ = v_a_2525_;
goto v___jp_2131_;
}
}
v___jp_2527_:
{
uint8_t v___x_2529_; 
v___x_2529_ = 1;
if (v___y_2528_ == 0)
{
lean_object* v___x_2530_; lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2701_; 
v___x_2530_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(v_e_2068_, v_a_2072_);
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2533_ = v___x_2530_;
v_isShared_2534_ = v_isSharedCheck_2701_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2530_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2701_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
uint8_t v___x_2535_; 
v___x_2535_ = lean_unbox(v_a_2531_);
lean_dec(v_a_2531_);
if (v___x_2535_ == 0)
{
lean_object* v_toCold_2536_; lean_object* v_options_2537_; uint8_t v_hasTrace_2538_; 
lean_del_object(v___x_2533_);
lean_dec(v_altIdx_2067_);
v_toCold_2536_ = lean_ctor_get(v_a_2071_, 0);
v_options_2537_ = lean_ctor_get(v_toCold_2536_, 2);
v_hasTrace_2538_ = lean_ctor_get_uint8(v_options_2537_, sizeof(void*)*1);
if (v_hasTrace_2538_ == 0)
{
v___y_2349_ = v___x_2529_;
goto v___jp_2348_;
}
else
{
lean_object* v_inheritedTraceOptions_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; uint8_t v___x_2542_; 
v_inheritedTraceOptions_2539_ = lean_ctor_get(v_toCold_2536_, 11);
v___x_2540_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2541_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2542_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2539_, v_options_2537_, v___x_2541_);
if (v___x_2542_ == 0)
{
v___y_2349_ = v___x_2529_;
goto v___jp_2348_;
}
else
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2543_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__15, &l_Lean_Meta_rwMatcher___closed__15_once, _init_l_Lean_Meta_rwMatcher___closed__15);
lean_inc_ref(v_e_2068_);
v___x_2544_ = l_Lean_indentExpr(v_e_2068_);
v___x_2545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2543_);
lean_ctor_set(v___x_2545_, 1, v___x_2544_);
v___x_2546_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2540_, v___x_2545_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_dec_ref_known(v___x_2546_, 1);
v___y_2349_ = v___x_2529_;
goto v___jp_2348_;
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
lean_dec_ref(v_e_2068_);
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2549_ = v___x_2546_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2546_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_a_2547_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
}
}
else
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2555_ = l_Lean_Expr_getAppFn(v_e_2068_);
v___x_2556_ = l_Lean_Expr_constName_x21(v___x_2555_);
lean_inc(v_a_2072_);
lean_inc_ref(v_a_2071_);
lean_inc(v_a_2070_);
lean_inc_ref(v_a_2069_);
lean_inc(v___x_2556_);
v___x_2557_ = lean_get_congr_match_equations_for(v___x_2556_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2558_; lean_object* v___x_2559_; uint8_t v___x_2560_; 
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_a_2558_);
lean_dec_ref_known(v___x_2557_, 1);
v___x_2559_ = lean_array_get_size(v_a_2558_);
v___x_2560_ = lean_nat_dec_lt(v_altIdx_2067_, v___x_2559_);
if (v___x_2560_ == 0)
{
lean_object* v_toCold_2561_; lean_object* v_options_2562_; uint8_t v_hasTrace_2563_; 
lean_dec(v_a_2558_);
lean_dec_ref(v___x_2555_);
v_toCold_2561_ = lean_ctor_get(v_a_2071_, 0);
v_options_2562_ = lean_ctor_get(v_toCold_2561_, 2);
v_hasTrace_2563_ = lean_ctor_get_uint8(v_options_2562_, sizeof(void*)*1);
if (v_hasTrace_2563_ == 0)
{
lean_dec(v___x_2556_);
lean_del_object(v___x_2533_);
lean_dec(v_altIdx_2067_);
v___y_2344_ = v___x_2529_;
goto v___jp_2343_;
}
else
{
lean_object* v_inheritedTraceOptions_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; 
v_inheritedTraceOptions_2564_ = lean_ctor_get(v_toCold_2561_, 11);
v___x_2565_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2566_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2567_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2564_, v_options_2562_, v___x_2566_);
if (v___x_2567_ == 0)
{
lean_dec(v___x_2556_);
lean_del_object(v___x_2533_);
lean_dec(v_altIdx_2067_);
v___y_2344_ = v___x_2529_;
goto v___jp_2343_;
}
else
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2571_; 
v___x_2568_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__17, &l_Lean_Meta_rwMatcher___closed__17_once, _init_l_Lean_Meta_rwMatcher___closed__17);
v___x_2569_ = l_Nat_reprFast(v_altIdx_2067_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set_tag(v___x_2533_, 3);
lean_ctor_set(v___x_2533_, 0, v___x_2569_);
v___x_2571_ = v___x_2533_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v___x_2569_);
v___x_2571_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2572_ = l_Lean_MessageData_ofFormat(v___x_2571_);
v___x_2573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2568_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__19, &l_Lean_Meta_rwMatcher___closed__19_once, _init_l_Lean_Meta_rwMatcher___closed__19);
v___x_2575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2573_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
v___x_2576_ = l_Nat_reprFast(v___x_2559_);
v___x_2577_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
v___x_2578_ = l_Lean_MessageData_ofFormat(v___x_2577_);
v___x_2579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2575_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
v___x_2580_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__21, &l_Lean_Meta_rwMatcher___closed__21_once, _init_l_Lean_Meta_rwMatcher___closed__21);
v___x_2581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2579_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
v___x_2582_ = l_Lean_MessageData_ofConstName(v___x_2556_, v___x_2560_);
v___x_2583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2581_);
lean_ctor_set(v___x_2583_, 1, v___x_2582_);
v___x_2584_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2565_, v___x_2583_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_dec_ref_known(v___x_2584_, 1);
v___y_2344_ = v___x_2529_;
goto v___jp_2343_;
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
lean_dec_ref(v_e_2068_);
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
}
else
{
lean_object* v_toCold_2594_; lean_object* v_options_2595_; lean_object* v_inheritedTraceOptions_2596_; uint8_t v_hasTrace_2597_; lean_object* v_nargs_2598_; lean_object* v___x_2599_; lean_object* v___f_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v_dummy_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
lean_dec(v___x_2556_);
lean_del_object(v___x_2533_);
v_toCold_2594_ = lean_ctor_get(v_a_2071_, 0);
v_options_2595_ = lean_ctor_get(v_toCold_2594_, 2);
v_inheritedTraceOptions_2596_ = lean_ctor_get(v_toCold_2594_, 11);
v_hasTrace_2597_ = lean_ctor_get_uint8(v_options_2595_, sizeof(void*)*1);
v_nargs_2598_ = l_Lean_Expr_getAppNumArgs(v_e_2068_);
v___x_2599_ = lean_box(v___x_2529_);
lean_inc_ref_n(v_e_2068_, 2);
v___f_2600_ = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2600_, 0, v_e_2068_);
lean_closure_set(v___f_2600_, 1, v___x_2599_);
v___x_2601_ = lean_array_get(v___x_2526_, v_a_2558_, v_altIdx_2067_);
lean_dec(v_altIdx_2067_);
lean_dec(v_a_2558_);
v___x_2602_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2603_ = l_Lean_Expr_constLevels_x21(v___x_2555_);
lean_dec_ref(v___x_2555_);
lean_inc(v___x_2601_);
v___x_2604_ = l_Lean_mkConst(v___x_2601_, v___x_2603_);
v_dummy_2605_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__22, &l_Lean_Meta_rwMatcher___closed__22_once, _init_l_Lean_Meta_rwMatcher___closed__22);
lean_inc(v_nargs_2598_);
v___x_2606_ = lean_mk_array(v_nargs_2598_, v_dummy_2605_);
v___x_2607_ = lean_unsigned_to_nat(1u);
v___x_2608_ = lean_nat_sub(v_nargs_2598_, v___x_2607_);
lean_dec(v_nargs_2598_);
v___x_2609_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2068_, v___x_2606_, v___x_2608_);
v___x_2610_ = l_Lean_mkAppN(v___x_2604_, v___x_2609_);
lean_dec_ref(v___x_2609_);
if (v_hasTrace_2597_ == 0)
{
lean_object* v___x_2611_; 
lean_inc(v_a_2072_);
lean_inc_ref(v_a_2071_);
lean_inc(v_a_2070_);
lean_inc_ref(v_a_2069_);
lean_inc_ref(v___x_2610_);
v___x_2611_ = lean_infer_type(v___x_2610_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; uint8_t v___x_2613_; lean_object* v___x_2614_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_a_2612_);
lean_dec_ref_known(v___x_2611_, 1);
v___x_2613_ = 0;
v___x_2614_ = l_Lean_Meta_forallMetaTelescope(v_a_2612_, v___x_2613_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v_snd_2616_; lean_object* v_fst_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2655_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2615_);
lean_dec_ref_known(v___x_2614_, 1);
v_snd_2616_ = lean_ctor_get(v_a_2615_, 1);
v_fst_2617_ = lean_ctor_get(v_a_2615_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v_a_2615_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2619_ = v_a_2615_;
v_isShared_2620_ = v_isSharedCheck_2655_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_snd_2616_);
lean_inc(v_fst_2617_);
lean_dec(v_a_2615_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2655_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v_snd_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2653_; 
v_snd_2621_ = lean_ctor_get(v_snd_2616_, 1);
v_isSharedCheck_2653_ = !lean_is_exclusive(v_snd_2616_);
if (v_isSharedCheck_2653_ == 0)
{
lean_object* v_unused_2654_; 
v_unused_2654_ = lean_ctor_get(v_snd_2616_, 0);
lean_dec(v_unused_2654_);
v___x_2623_ = v_snd_2616_;
v_isShared_2624_ = v_isSharedCheck_2653_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_snd_2621_);
lean_dec(v_snd_2616_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2653_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2625_; size_t v_sz_2626_; size_t v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; uint8_t v___x_2631_; 
v___x_2625_ = l_Lean_mkAppN(v___x_2610_, v_fst_2617_);
v_sz_2626_ = lean_array_size(v_fst_2617_);
v___x_2627_ = ((size_t)0ULL);
v___x_2628_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_2626_, v___x_2627_, v_fst_2617_);
v___x_2629_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_2630_ = lean_unsigned_to_nat(4u);
v___x_2631_ = l_Lean_Expr_isAppOfArity(v_snd_2621_, v___x_2629_, v___x_2630_);
if (v___x_2631_ == 0)
{
lean_object* v___x_2632_; lean_object* v___x_2633_; uint8_t v___x_2634_; 
v___x_2632_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_2633_ = lean_unsigned_to_nat(3u);
v___x_2634_ = l_Lean_Expr_isAppOfArity(v_snd_2621_, v___x_2632_, v___x_2633_);
if (v___x_2634_ == 0)
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2638_; 
lean_dec_ref(v___x_2628_);
lean_dec_ref(v___x_2625_);
lean_dec(v_snd_2621_);
lean_dec_ref(v_e_2068_);
v___x_2635_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
lean_inc(v___x_2601_);
v___x_2636_ = l_Lean_MessageData_ofConstName(v___x_2601_, v___y_2528_);
if (v_isShared_2624_ == 0)
{
lean_ctor_set_tag(v___x_2623_, 7);
lean_ctor_set(v___x_2623_, 1, v___x_2636_);
lean_ctor_set(v___x_2623_, 0, v___x_2635_);
v___x_2638_ = v___x_2623_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2635_);
lean_ctor_set(v_reuseFailAlloc_2645_, 1, v___x_2636_);
v___x_2638_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
lean_object* v___x_2639_; lean_object* v___x_2641_; 
v___x_2639_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
if (v_isShared_2620_ == 0)
{
lean_ctor_set_tag(v___x_2619_, 7);
lean_ctor_set(v___x_2619_, 1, v___x_2639_);
lean_ctor_set(v___x_2619_, 0, v___x_2638_);
v___x_2641_ = v___x_2619_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2638_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v___x_2639_);
v___x_2641_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
lean_object* v___x_2642_; lean_object* v_a_2643_; 
v___x_2642_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2641_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_a_2643_);
lean_dec_ref(v___x_2642_);
v___y_2132_ = v___y_2528_;
v___y_2133_ = v___x_2602_;
v___y_2134_ = v___f_2600_;
v___y_2135_ = v___x_2601_;
v_a_2136_ = v_a_2643_;
goto v___jp_2131_;
}
}
}
else
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
lean_del_object(v___x_2623_);
lean_del_object(v___x_2619_);
v___x_2646_ = l_Lean_Expr_appFn_x21(v_snd_2621_);
v___x_2647_ = l_Lean_Expr_appArg_x21(v___x_2646_);
lean_dec_ref(v___x_2646_);
v___x_2648_ = l_Lean_Expr_appArg_x21(v_snd_2621_);
lean_dec(v_snd_2621_);
v___y_2492_ = v___y_2528_;
v___y_2493_ = v___x_2602_;
v___y_2494_ = v___f_2600_;
v___y_2495_ = v___x_2529_;
v___y_2496_ = v___x_2627_;
v___y_2497_ = v___x_2628_;
v___y_2498_ = v___x_2625_;
v___y_2499_ = v___x_2601_;
v_fst_2500_ = v___y_2528_;
v_fst_2501_ = v___x_2647_;
v_snd_2502_ = v___x_2648_;
v___y_2503_ = v_a_2069_;
v___y_2504_ = v_a_2070_;
v___y_2505_ = v_a_2071_;
v___y_2506_ = v_a_2072_;
goto v___jp_2491_;
}
}
else
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
lean_del_object(v___x_2623_);
lean_del_object(v___x_2619_);
v___x_2649_ = l_Lean_Expr_appFn_x21(v_snd_2621_);
v___x_2650_ = l_Lean_Expr_appFn_x21(v___x_2649_);
lean_dec_ref(v___x_2649_);
v___x_2651_ = l_Lean_Expr_appArg_x21(v___x_2650_);
lean_dec_ref(v___x_2650_);
v___x_2652_ = l_Lean_Expr_appArg_x21(v_snd_2621_);
lean_dec(v_snd_2621_);
v___y_2492_ = v___y_2528_;
v___y_2493_ = v___x_2602_;
v___y_2494_ = v___f_2600_;
v___y_2495_ = v___x_2529_;
v___y_2496_ = v___x_2627_;
v___y_2497_ = v___x_2628_;
v___y_2498_ = v___x_2625_;
v___y_2499_ = v___x_2601_;
v_fst_2500_ = v___x_2529_;
v_fst_2501_ = v___x_2651_;
v_snd_2502_ = v___x_2652_;
v___y_2503_ = v_a_2069_;
v___y_2504_ = v_a_2070_;
v___y_2505_ = v_a_2071_;
v___y_2506_ = v_a_2072_;
goto v___jp_2491_;
}
}
}
}
else
{
lean_object* v_a_2656_; 
lean_dec_ref(v___x_2610_);
lean_dec_ref(v_e_2068_);
v_a_2656_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2656_);
lean_dec_ref_known(v___x_2614_, 1);
v___y_2132_ = v___y_2528_;
v___y_2133_ = v___x_2602_;
v___y_2134_ = v___f_2600_;
v___y_2135_ = v___x_2601_;
v_a_2136_ = v_a_2656_;
goto v___jp_2131_;
}
}
else
{
lean_object* v_a_2657_; 
lean_dec_ref(v___x_2610_);
lean_dec_ref(v_e_2068_);
v_a_2657_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___x_2611_, 1);
v___y_2132_ = v___y_2528_;
v___y_2133_ = v___x_2602_;
v___y_2134_ = v___f_2600_;
v___y_2135_ = v___x_2601_;
v_a_2136_ = v_a_2657_;
goto v___jp_2131_;
}
}
else
{
lean_object* v___x_2658_; lean_object* v___f_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; uint8_t v___x_2662_; 
v___x_2658_ = lean_box(v___y_2528_);
lean_inc_ref(v_e_2068_);
lean_inc(v___x_2601_);
v___f_2659_ = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__1___boxed), 9, 3);
lean_closure_set(v___f_2659_, 0, v___x_2601_);
lean_closure_set(v___f_2659_, 1, v___x_2658_);
lean_closure_set(v___f_2659_, 2, v_e_2068_);
v___x_2660_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1));
v___x_2661_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2662_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2596_, v_options_2595_, v___x_2661_);
if (v___x_2662_ == 0)
{
lean_object* v___x_2663_; uint8_t v___x_2664_; 
v___x_2663_ = l_Lean_trace_profiler;
v___x_2664_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_options_2595_, v___x_2663_);
if (v___x_2664_ == 0)
{
lean_object* v___x_2665_; 
lean_dec_ref(v___f_2659_);
lean_inc(v_a_2072_);
lean_inc_ref(v_a_2071_);
lean_inc(v_a_2070_);
lean_inc_ref(v_a_2069_);
lean_inc_ref(v___x_2610_);
v___x_2665_ = lean_infer_type(v___x_2610_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; uint8_t v___x_2667_; lean_object* v___x_2668_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_a_2666_);
lean_dec_ref_known(v___x_2665_, 1);
v___x_2667_ = 0;
v___x_2668_ = l_Lean_Meta_forallMetaTelescope(v_a_2666_, v___x_2667_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v_a_2669_; lean_object* v_snd_2670_; 
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2669_);
lean_dec_ref_known(v___x_2668_, 1);
v_snd_2670_ = lean_ctor_get(v_a_2669_, 1);
lean_inc(v_snd_2670_);
if (v___x_2662_ == 0)
{
lean_object* v_fst_2671_; lean_object* v_snd_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v_fst_2671_ = lean_ctor_get(v_a_2669_, 0);
lean_inc(v_fst_2671_);
lean_dec(v_a_2669_);
v_snd_2672_ = lean_ctor_get(v_snd_2670_, 1);
lean_inc(v_snd_2672_);
lean_dec(v_snd_2670_);
v___x_2673_ = lean_box(0);
lean_inc(v___x_2601_);
v___x_2674_ = l_Lean_Meta_rwMatcher___lam__4(v___x_2529_, v___x_2610_, v_fst_2671_, v___x_2601_, v_e_2068_, v___y_2528_, v_snd_2672_, v___x_2673_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
lean_dec(v_snd_2672_);
v___y_2140_ = v___y_2528_;
v___y_2141_ = v___x_2602_;
v___y_2142_ = v___f_2600_;
v___y_2143_ = v___x_2601_;
v___y_2144_ = v___x_2674_;
goto v___jp_2139_;
}
else
{
lean_object* v_fst_2675_; lean_object* v_snd_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2689_; 
v_fst_2675_ = lean_ctor_get(v_a_2669_, 0);
lean_inc(v_fst_2675_);
lean_dec(v_a_2669_);
v_snd_2676_ = lean_ctor_get(v_snd_2670_, 1);
v_isSharedCheck_2689_ = !lean_is_exclusive(v_snd_2670_);
if (v_isSharedCheck_2689_ == 0)
{
lean_object* v_unused_2690_; 
v_unused_2690_ = lean_ctor_get(v_snd_2670_, 0);
lean_dec(v_unused_2690_);
v___x_2678_ = v_snd_2670_;
v_isShared_2679_ = v_isSharedCheck_2689_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_snd_2676_);
lean_dec(v_snd_2670_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2689_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2683_; 
v___x_2680_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2676_);
v___x_2681_ = l_Lean_indentExpr(v_snd_2676_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set_tag(v___x_2678_, 7);
lean_ctor_set(v___x_2678_, 1, v___x_2681_);
lean_ctor_set(v___x_2678_, 0, v___x_2680_);
v___x_2683_ = v___x_2678_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2680_);
lean_ctor_set(v_reuseFailAlloc_2688_, 1, v___x_2681_);
v___x_2683_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
lean_object* v___x_2684_; 
v___x_2684_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2602_, v___x_2683_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_a_2685_; lean_object* v___x_2686_; 
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2685_);
lean_dec_ref_known(v___x_2684_, 1);
lean_inc(v___x_2601_);
v___x_2686_ = l_Lean_Meta_rwMatcher___lam__4(v___x_2529_, v___x_2610_, v_fst_2675_, v___x_2601_, v_e_2068_, v___y_2528_, v_snd_2676_, v_a_2685_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
lean_dec(v_snd_2676_);
v___y_2140_ = v___y_2528_;
v___y_2141_ = v___x_2602_;
v___y_2142_ = v___f_2600_;
v___y_2143_ = v___x_2601_;
v___y_2144_ = v___x_2686_;
goto v___jp_2139_;
}
else
{
lean_object* v_a_2687_; 
lean_dec(v_snd_2676_);
lean_dec(v_fst_2675_);
lean_dec_ref(v___x_2610_);
lean_dec_ref(v_e_2068_);
v_a_2687_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2687_);
lean_dec_ref_known(v___x_2684_, 1);
v___y_2132_ = v___y_2528_;
v___y_2133_ = v___x_2602_;
v___y_2134_ = v___f_2600_;
v___y_2135_ = v___x_2601_;
v_a_2136_ = v_a_2687_;
goto v___jp_2131_;
}
}
}
}
}
else
{
lean_object* v_a_2691_; 
lean_dec_ref(v___x_2610_);
lean_dec_ref(v_e_2068_);
v_a_2691_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2691_);
lean_dec_ref_known(v___x_2668_, 1);
v___y_2132_ = v___y_2528_;
v___y_2133_ = v___x_2602_;
v___y_2134_ = v___f_2600_;
v___y_2135_ = v___x_2601_;
v_a_2136_ = v_a_2691_;
goto v___jp_2131_;
}
}
else
{
lean_object* v_a_2692_; 
lean_dec_ref(v___x_2610_);
lean_dec_ref(v_e_2068_);
v_a_2692_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_a_2692_);
lean_dec_ref_known(v___x_2665_, 1);
v___y_2132_ = v___y_2528_;
v___y_2133_ = v___x_2602_;
v___y_2134_ = v___f_2600_;
v___y_2135_ = v___x_2601_;
v_a_2136_ = v_a_2692_;
goto v___jp_2131_;
}
}
else
{
lean_inc(v___x_2601_);
lean_inc_ref(v___x_2610_);
v___y_2264_ = v___y_2528_;
v___y_2265_ = v___x_2610_;
v___y_2266_ = v___f_2659_;
v___y_2267_ = v___x_2529_;
v___y_2268_ = v___x_2601_;
v___y_2269_ = v_inheritedTraceOptions_2596_;
v___y_2270_ = v___y_2528_;
v___y_2271_ = v_options_2595_;
v___y_2272_ = v___x_2602_;
v___y_2273_ = v___x_2610_;
v___y_2274_ = v___x_2662_;
v___y_2275_ = v___f_2600_;
v___y_2276_ = v___x_2529_;
v___y_2277_ = v___x_2660_;
v___y_2278_ = v___x_2601_;
goto v___jp_2263_;
}
}
else
{
lean_inc(v___x_2601_);
lean_inc_ref(v___x_2610_);
v___y_2264_ = v___y_2528_;
v___y_2265_ = v___x_2610_;
v___y_2266_ = v___f_2659_;
v___y_2267_ = v___x_2529_;
v___y_2268_ = v___x_2601_;
v___y_2269_ = v_inheritedTraceOptions_2596_;
v___y_2270_ = v___y_2528_;
v___y_2271_ = v_options_2595_;
v___y_2272_ = v___x_2602_;
v___y_2273_ = v___x_2610_;
v___y_2274_ = v___x_2662_;
v___y_2275_ = v___f_2600_;
v___y_2276_ = v___x_2529_;
v___y_2277_ = v___x_2660_;
v___y_2278_ = v___x_2601_;
goto v___jp_2263_;
}
}
}
}
else
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
lean_dec(v___x_2556_);
lean_dec_ref(v___x_2555_);
lean_del_object(v___x_2533_);
lean_dec_ref(v_e_2068_);
lean_dec(v_altIdx_2067_);
v_a_2693_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v___x_2557_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2557_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2693_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
}
}
else
{
lean_object* v___x_2702_; 
lean_dec(v_altIdx_2067_);
v___x_2702_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(v_e_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2712_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2705_ = v___x_2702_;
v_isShared_2706_ = v_isSharedCheck_2712_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2702_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2712_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2710_; 
v___x_2707_ = lean_box(0);
v___x_2708_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2708_, 0, v_a_2703_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
lean_ctor_set_uint8(v___x_2708_, sizeof(void*)*2, v___x_2529_);
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 0, v___x_2708_);
v___x_2710_ = v___x_2705_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2708_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
v_a_2713_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2715_ = v___x_2702_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2702_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2713_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___boxed(lean_object* v_altIdx_2725_, lean_object* v_e_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l_Lean_Meta_rwMatcher(v_altIdx_2725_, v_e_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_);
lean_dec(v_a_2730_);
lean_dec_ref(v_a_2729_);
lean_dec(v_a_2728_);
lean_dec_ref(v_a_2727_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(lean_object* v_mvarId_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_mvarId_2733_, v___y_2735_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___boxed(lean_object* v_mvarId_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(v_mvarId_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v_mvarId_2740_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5(lean_object* v_00_u03b1_2747_, lean_object* v_msg_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v_msg_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___boxed(lean_object* v_00_u03b1_2755_, lean_object* v_msg_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5(v_00_u03b1_2755_, v_msg_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14(lean_object* v_00_u03b1_2763_, lean_object* v_x_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
lean_object* v___x_2770_; 
v___x_2770_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(v_x_2764_);
return v___x_2770_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___boxed(lean_object* v_00_u03b1_2771_, lean_object* v_x_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14(v_00_u03b1_2771_, v_x_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12(lean_object* v_inst_2779_, lean_object* v_a_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___redArg(v_a_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12___boxed(lean_object* v_inst_2787_, lean_object* v_a_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__12(v_inst_2787_, v_a_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
return v_res_2794_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(lean_object* v_00_u03b2_2795_, lean_object* v_x_2796_, lean_object* v_x_2797_){
_start:
{
uint8_t v___x_2798_; 
v___x_2798_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_x_2796_, v_x_2797_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2799_, lean_object* v_x_2800_, lean_object* v_x_2801_){
_start:
{
uint8_t v_res_2802_; lean_object* v_r_2803_; 
v_res_2802_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(v_00_u03b2_2799_, v_x_2800_, v_x_2801_);
lean_dec(v_x_2801_);
lean_dec_ref(v_x_2800_);
v_r_2803_ = lean_box(v_res_2802_);
return v_r_2803_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5(lean_object* v_00_u03b2_2804_, lean_object* v_x_2805_, size_t v_x_2806_, lean_object* v_x_2807_){
_start:
{
uint8_t v___x_2808_; 
v___x_2808_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_2805_, v_x_2806_, v_x_2807_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b2_2809_, lean_object* v_x_2810_, lean_object* v_x_2811_, lean_object* v_x_2812_){
_start:
{
size_t v_x_88220__boxed_2813_; uint8_t v_res_2814_; lean_object* v_r_2815_; 
v_x_88220__boxed_2813_ = lean_unbox_usize(v_x_2811_);
lean_dec(v_x_2811_);
v_res_2814_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5(v_00_u03b2_2809_, v_x_2810_, v_x_88220__boxed_2813_, v_x_2812_);
lean_dec(v_x_2812_);
lean_dec_ref(v_x_2810_);
v_r_2815_ = lean_box(v_res_2814_);
return v_r_2815_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18(lean_object* v_00_u03b2_2816_, lean_object* v_keys_2817_, lean_object* v_vals_2818_, lean_object* v_heq_2819_, lean_object* v_i_2820_, lean_object* v_k_2821_){
_start:
{
uint8_t v___x_2822_; 
v___x_2822_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___redArg(v_keys_2817_, v_i_2820_, v_k_2821_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18___boxed(lean_object* v_00_u03b2_2823_, lean_object* v_keys_2824_, lean_object* v_vals_2825_, lean_object* v_heq_2826_, lean_object* v_i_2827_, lean_object* v_k_2828_){
_start:
{
uint8_t v_res_2829_; lean_object* v_r_2830_; 
v_res_2829_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__18(v_00_u03b2_2823_, v_keys_2824_, v_vals_2825_, v_heq_2826_, v_i_2827_, v_k_2828_);
lean_dec(v_k_2828_);
lean_dec_ref(v_vals_2825_);
lean_dec_ref(v_keys_2824_);
v_r_2830_ = lean_box(v_res_2829_);
return v_r_2830_;
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
