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
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_107821__boxed_537_; lean_object* v_res_538_; 
v___x_107821__boxed_537_ = lean_unbox(v___x_530_);
v_res_538_ = l_Lean_Meta_rwMatcher___lam__0(v_e_529_, v___x_107821__boxed_537_, v_____r_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
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
uint8_t v___y_107863__boxed_571_; lean_object* v_res_572_; 
v___y_107863__boxed_571_ = lean_unbox(v___y_563_);
v_res_572_ = l_Lean_Meta_rwMatcher___lam__1(v___x_562_, v___y_107863__boxed_571_, v_e_564_, v_x_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
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
v___x_670_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20___redArg(v_ks_668_, v___x_669_, v_x_654_);
return v___x_670_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_671_, lean_object* v_x_672_, lean_object* v_x_673_){
_start:
{
size_t v_x_107996__boxed_674_; uint8_t v_res_675_; lean_object* v_r_676_; 
v_x_107996__boxed_674_ = lean_unbox_usize(v_x_672_);
lean_dec(v_x_672_);
v_res_675_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_671_, v_x_107996__boxed_674_, v_x_673_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12(uint8_t v___x_699_, lean_object* v_as_700_, size_t v_i_701_, size_t v_stop_702_, lean_object* v_b_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_a_710_; uint8_t v___x_714_; 
v___x_714_ = lean_usize_dec_eq(v_i_701_, v_stop_702_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; uint8_t v_a_719_; lean_object* v___x_720_; 
v___x_715_ = lean_array_uget_borrowed(v_as_700_, v_i_701_);
v___x_720_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v___x_715_, v___y_705_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; uint8_t v___x_722_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_a_721_);
lean_dec_ref_known(v___x_720_, 1);
v___x_722_ = lean_unbox(v_a_721_);
lean_dec(v_a_721_);
if (v___x_722_ == 0)
{
goto v___jp_716_;
}
else
{
v_a_719_ = v___x_699_;
goto v___jp_718_;
}
}
else
{
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_723_; uint8_t v___x_724_; 
v_a_723_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_a_723_);
lean_dec_ref_known(v___x_720_, 1);
v___x_724_ = lean_unbox(v_a_723_);
lean_dec(v_a_723_);
v_a_719_ = v___x_724_;
goto v___jp_718_;
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec_ref(v_b_703_);
v_a_725_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_720_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_720_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
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
v___jp_718_:
{
if (v_a_719_ == 0)
{
v_a_710_ = v_b_703_;
goto v___jp_709_;
}
else
{
goto v___jp_716_;
}
}
}
else
{
lean_object* v___x_733_; 
v___x_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_733_, 0, v_b_703_);
return v___x_733_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12___boxed(lean_object* v___x_734_, lean_object* v_as_735_, lean_object* v_i_736_, lean_object* v_stop_737_, lean_object* v_b_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
uint8_t v___x_108062__boxed_744_; size_t v_i_boxed_745_; size_t v_stop_boxed_746_; lean_object* v_res_747_; 
v___x_108062__boxed_744_ = lean_unbox(v___x_734_);
v_i_boxed_745_ = lean_unbox_usize(v_i_736_);
lean_dec(v_i_736_);
v_stop_boxed_746_ = lean_unbox_usize(v_stop_737_);
lean_dec(v_stop_737_);
v_res_747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12(v___x_108062__boxed_744_, v_as_735_, v_i_boxed_745_, v_stop_boxed_746_, v_b_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec_ref(v_as_735_);
return v_res_747_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__0));
v___x_750_ = l_Lean_stringToMessageData(v___x_749_);
return v___x_750_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__2));
v___x_753_ = l_Lean_stringToMessageData(v___x_752_);
return v___x_753_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__4));
v___x_756_ = l_Lean_stringToMessageData(v___x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(lean_object* v_as_757_, size_t v_sz_758_, size_t v_i_759_, lean_object* v_b_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_a_767_; uint8_t v___x_771_; 
v___x_771_ = lean_usize_dec_lt(v_i_759_, v_sz_758_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; 
v___x_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_772_, 0, v_b_760_);
return v___x_772_;
}
else
{
lean_object* v_a_773_; lean_object* v___x_774_; 
v_a_773_ = lean_array_uget_borrowed(v_as_757_, v_i_759_);
v___x_774_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_a_773_, v___y_762_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v___x_776_; lean_object* v___y_778_; lean_object* v___y_780_; lean_object* v___y_781_; uint8_t v___y_782_; lean_object* v___y_798_; lean_object* v___y_800_; lean_object* v___y_801_; uint8_t v___y_802_; lean_object* v___y_818_; uint8_t v___x_819_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_775_);
lean_dec_ref_known(v___x_774_, 1);
v___x_776_ = lean_box(0);
v___x_819_ = lean_unbox(v_a_775_);
lean_dec(v_a_775_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; 
lean_inc(v_a_773_);
v___x_820_ = l_Lean_MVarId_getType(v_a_773_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; uint8_t v___x_822_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc_n(v_a_821_, 2);
lean_dec_ref_known(v___x_820_, 1);
v___x_822_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_a_821_);
if (v___x_822_ == 0)
{
uint8_t v___x_823_; 
v___x_823_ = l_Lean_Expr_isEq(v_a_821_);
if (v___x_823_ == 0)
{
uint8_t v___x_824_; 
v___x_824_ = l_Lean_Expr_isHEq(v_a_821_);
lean_dec(v_a_821_);
if (v___x_824_ == 0)
{
v_a_767_ = v___x_776_;
goto v___jp_766_;
}
else
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_Meta_saveState___redArg(v___y_762_, v___y_764_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___x_827_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_a_826_);
lean_dec_ref_known(v___x_825_, 1);
lean_inc(v_a_773_);
v___x_827_ = l_Lean_MVarId_assumption(v_a_773_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_dec(v_a_826_);
v___y_798_ = v___x_827_;
goto v___jp_797_;
}
else
{
lean_object* v_a_828_; uint8_t v___y_830_; uint8_t v___x_846_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
v___x_846_ = l_Lean_Exception_isInterrupt(v_a_828_);
if (v___x_846_ == 0)
{
uint8_t v___x_847_; 
v___x_847_ = l_Lean_Exception_isRuntime(v_a_828_);
v___y_830_ = v___x_847_;
goto v___jp_829_;
}
else
{
lean_dec(v_a_828_);
v___y_830_ = v___x_846_;
goto v___jp_829_;
}
v___jp_829_:
{
if (v___y_830_ == 0)
{
lean_object* v___x_831_; 
lean_dec_ref_known(v___x_827_, 1);
v___x_831_ = l_Lean_Meta_SavedState_restore___redArg(v_a_826_, v___y_762_, v___y_764_);
lean_dec(v_a_826_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v___x_832_; 
lean_dec_ref_known(v___x_831_, 1);
v___x_832_ = l_Lean_Meta_saveState___redArg(v___y_762_, v___y_764_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v___x_834_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
lean_dec_ref_known(v___x_832_, 1);
lean_inc(v_a_773_);
v___x_834_ = l_Lean_MVarId_hrefl(v_a_773_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_dec(v_a_833_);
v___y_798_ = v___x_834_;
goto v___jp_797_;
}
else
{
lean_object* v_a_835_; uint8_t v___x_836_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_a_835_);
v___x_836_ = l_Lean_Exception_isInterrupt(v_a_835_);
if (v___x_836_ == 0)
{
uint8_t v___x_837_; 
v___x_837_ = l_Lean_Exception_isRuntime(v_a_835_);
v___y_800_ = v___x_834_;
v___y_801_ = v_a_833_;
v___y_802_ = v___x_837_;
goto v___jp_799_;
}
else
{
lean_dec(v_a_835_);
v___y_800_ = v___x_834_;
v___y_801_ = v_a_833_;
v___y_802_ = v___x_836_;
goto v___jp_799_;
}
}
}
else
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
v_a_838_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_832_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_832_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
else
{
v___y_798_ = v___x_831_;
goto v___jp_797_;
}
}
else
{
lean_dec(v_a_826_);
v___y_798_ = v___x_827_;
goto v___jp_797_;
}
}
}
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
v_a_848_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_825_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_825_);
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
lean_object* v___x_856_; 
lean_dec(v_a_821_);
v___x_856_ = l_Lean_Meta_saveState___redArg(v___y_762_, v___y_764_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_858_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
lean_dec_ref_known(v___x_856_, 1);
lean_inc(v_a_773_);
v___x_858_ = l_Lean_MVarId_assumption(v_a_773_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_dec(v_a_857_);
v___y_778_ = v___x_858_;
goto v___jp_777_;
}
else
{
lean_object* v_a_859_; uint8_t v___y_861_; uint8_t v___x_877_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
v___x_877_ = l_Lean_Exception_isInterrupt(v_a_859_);
if (v___x_877_ == 0)
{
uint8_t v___x_878_; 
v___x_878_ = l_Lean_Exception_isRuntime(v_a_859_);
v___y_861_ = v___x_878_;
goto v___jp_860_;
}
else
{
lean_dec(v_a_859_);
v___y_861_ = v___x_877_;
goto v___jp_860_;
}
v___jp_860_:
{
if (v___y_861_ == 0)
{
lean_object* v___x_862_; 
lean_dec_ref_known(v___x_858_, 1);
v___x_862_ = l_Lean_Meta_SavedState_restore___redArg(v_a_857_, v___y_762_, v___y_764_);
lean_dec(v_a_857_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v___x_863_; 
lean_dec_ref_known(v___x_862_, 1);
v___x_863_ = l_Lean_Meta_saveState___redArg(v___y_762_, v___y_764_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_865_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_a_864_);
lean_dec_ref_known(v___x_863_, 1);
lean_inc(v_a_773_);
v___x_865_ = l_Lean_MVarId_refl(v_a_773_, v___x_823_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_dec(v_a_864_);
v___y_778_ = v___x_865_;
goto v___jp_777_;
}
else
{
lean_object* v_a_866_; uint8_t v___x_867_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_866_);
v___x_867_ = l_Lean_Exception_isInterrupt(v_a_866_);
if (v___x_867_ == 0)
{
uint8_t v___x_868_; 
v___x_868_ = l_Lean_Exception_isRuntime(v_a_866_);
v___y_780_ = v___x_865_;
v___y_781_ = v_a_864_;
v___y_782_ = v___x_868_;
goto v___jp_779_;
}
else
{
lean_dec(v_a_866_);
v___y_780_ = v___x_865_;
v___y_781_ = v_a_864_;
v___y_782_ = v___x_867_;
goto v___jp_779_;
}
}
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
v_a_869_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_863_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_863_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
else
{
v___y_778_ = v___x_862_;
goto v___jp_777_;
}
}
else
{
lean_dec(v_a_857_);
v___y_778_ = v___x_858_;
goto v___jp_777_;
}
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
v_a_879_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_856_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_856_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
else
{
lean_object* v___x_887_; 
lean_dec(v_a_821_);
v___x_887_ = l_Lean_Meta_saveState___redArg(v___y_762_, v___y_764_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_889_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_a_888_);
lean_dec_ref_known(v___x_887_, 1);
lean_inc(v_a_773_);
v___x_889_ = l_Lean_MVarId_assumption(v_a_773_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_dec(v_a_888_);
v___y_818_ = v___x_889_;
goto v___jp_817_;
}
else
{
lean_object* v_a_890_; uint8_t v___y_892_; uint8_t v___x_907_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
v___x_907_ = l_Lean_Exception_isInterrupt(v_a_890_);
if (v___x_907_ == 0)
{
uint8_t v___x_908_; 
v___x_908_ = l_Lean_Exception_isRuntime(v_a_890_);
v___y_892_ = v___x_908_;
goto v___jp_891_;
}
else
{
lean_dec(v_a_890_);
v___y_892_ = v___x_907_;
goto v___jp_891_;
}
v___jp_891_:
{
if (v___y_892_ == 0)
{
lean_object* v___x_893_; 
lean_dec_ref_known(v___x_889_, 1);
v___x_893_ = l_Lean_Meta_SavedState_restore___redArg(v_a_888_, v___y_762_, v___y_764_);
lean_dec(v_a_888_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_905_; 
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_905_ == 0)
{
lean_object* v_unused_906_; 
v_unused_906_ = lean_ctor_get(v___x_893_, 0);
lean_dec(v_unused_906_);
v___x_895_ = v___x_893_;
v_isShared_896_ = v_isSharedCheck_905_;
goto v_resetjp_894_;
}
else
{
lean_dec(v___x_893_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_905_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_897_; lean_object* v___x_899_; 
v___x_897_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__5);
lean_inc(v_a_773_);
if (v_isShared_896_ == 0)
{
lean_ctor_set_tag(v___x_895_, 1);
lean_ctor_set(v___x_895_, 0, v_a_773_);
v___x_899_ = v___x_895_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_773_);
v___x_899_ = v_reuseFailAlloc_904_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_897_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_900_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_902_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
v___y_818_ = v___x_903_;
goto v___jp_817_;
}
}
}
else
{
v___y_818_ = v___x_893_;
goto v___jp_817_;
}
}
else
{
lean_dec(v_a_888_);
v___y_818_ = v___x_889_;
goto v___jp_817_;
}
}
}
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
v_a_909_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_887_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_887_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
v_a_917_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_820_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_820_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
else
{
v_a_767_ = v___x_776_;
goto v___jp_766_;
}
v___jp_777_:
{
if (lean_obj_tag(v___y_778_) == 0)
{
lean_dec_ref_known(v___y_778_, 1);
v_a_767_ = v___x_776_;
goto v___jp_766_;
}
else
{
return v___y_778_;
}
}
v___jp_779_:
{
if (v___y_782_ == 0)
{
lean_object* v___x_783_; 
lean_dec_ref(v___y_780_);
v___x_783_ = l_Lean_Meta_SavedState_restore___redArg(v___y_781_, v___y_762_, v___y_764_);
lean_dec_ref(v___y_781_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_795_; 
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; 
v_unused_796_ = lean_ctor_get(v___x_783_, 0);
lean_dec(v_unused_796_);
v___x_785_ = v___x_783_;
v_isShared_786_ = v_isSharedCheck_795_;
goto v_resetjp_784_;
}
else
{
lean_dec(v___x_783_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_795_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_787_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1);
lean_inc(v_a_773_);
if (v_isShared_786_ == 0)
{
lean_ctor_set_tag(v___x_785_, 1);
lean_ctor_set(v___x_785_, 0, v_a_773_);
v___x_789_ = v___x_785_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_773_);
v___x_789_ = v_reuseFailAlloc_794_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_787_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
v___x_791_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_790_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
v___x_793_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_792_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
v___y_778_ = v___x_793_;
goto v___jp_777_;
}
}
}
else
{
v___y_778_ = v___x_783_;
goto v___jp_777_;
}
}
else
{
lean_dec_ref(v___y_781_);
v___y_778_ = v___y_780_;
goto v___jp_777_;
}
}
v___jp_797_:
{
if (lean_obj_tag(v___y_798_) == 0)
{
lean_dec_ref_known(v___y_798_, 1);
v_a_767_ = v___x_776_;
goto v___jp_766_;
}
else
{
return v___y_798_;
}
}
v___jp_799_:
{
if (v___y_802_ == 0)
{
lean_object* v___x_803_; 
lean_dec_ref(v___y_800_);
v___x_803_ = l_Lean_Meta_SavedState_restore___redArg(v___y_801_, v___y_762_, v___y_764_);
lean_dec_ref(v___y_801_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_815_; 
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; 
v_unused_816_ = lean_ctor_get(v___x_803_, 0);
lean_dec(v_unused_816_);
v___x_805_ = v___x_803_;
v_isShared_806_ = v_isSharedCheck_815_;
goto v_resetjp_804_;
}
else
{
lean_dec(v___x_803_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_815_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_809_; 
v___x_807_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__1);
lean_inc(v_a_773_);
if (v_isShared_806_ == 0)
{
lean_ctor_set_tag(v___x_805_, 1);
lean_ctor_set(v___x_805_, 0, v_a_773_);
v___x_809_ = v___x_805_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_773_);
v___x_809_ = v_reuseFailAlloc_814_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_807_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_812_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
v___y_798_ = v___x_813_;
goto v___jp_797_;
}
}
}
else
{
v___y_798_ = v___x_803_;
goto v___jp_797_;
}
}
else
{
lean_dec_ref(v___y_801_);
v___y_798_ = v___y_800_;
goto v___jp_797_;
}
}
v___jp_817_:
{
if (lean_obj_tag(v___y_818_) == 0)
{
lean_dec_ref_known(v___y_818_, 1);
v_a_767_ = v___x_776_;
goto v___jp_766_;
}
else
{
return v___y_818_;
}
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
v_a_925_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_774_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_774_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
v___jp_766_:
{
size_t v___x_768_; size_t v___x_769_; 
v___x_768_ = ((size_t)1ULL);
v___x_769_ = lean_usize_add(v_i_759_, v___x_768_);
v_i_759_ = v___x_769_;
v_b_760_ = v_a_767_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___boxed(lean_object* v_as_933_, lean_object* v_sz_934_, lean_object* v_i_935_, lean_object* v_b_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
size_t v_sz_boxed_942_; size_t v_i_boxed_943_; lean_object* v_res_944_; 
v_sz_boxed_942_ = lean_unbox_usize(v_sz_934_);
lean_dec(v_sz_934_);
v_i_boxed_943_ = lean_unbox_usize(v_i_935_);
lean_dec(v_i_935_);
v_res_944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v_as_933_, v_sz_boxed_942_, v_i_boxed_943_, v_b_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec_ref(v_as_933_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
if (lean_obj_tag(v_a_945_) == 0)
{
lean_object* v___x_947_; 
v___x_947_ = l_List_reverse___redArg(v_a_946_);
return v___x_947_;
}
else
{
lean_object* v_head_948_; lean_object* v_tail_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_958_; 
v_head_948_ = lean_ctor_get(v_a_945_, 0);
v_tail_949_ = lean_ctor_get(v_a_945_, 1);
v_isSharedCheck_958_ = !lean_is_exclusive(v_a_945_);
if (v_isSharedCheck_958_ == 0)
{
v___x_951_ = v_a_945_;
v_isShared_952_ = v_isSharedCheck_958_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_tail_949_);
lean_inc(v_head_948_);
lean_dec(v_a_945_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_958_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_953_; lean_object* v___x_955_; 
v___x_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_953_, 0, v_head_948_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 1, v_a_946_);
lean_ctor_set(v___x_951_, 0, v___x_953_);
v___x_955_ = v___x_951_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_a_946_);
v___x_955_ = v_reuseFailAlloc_957_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
v_a_945_ = v_tail_949_;
v_a_946_ = v___x_955_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__1(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__0));
v___x_961_ = l_Lean_stringToMessageData(v___x_960_);
return v___x_961_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__3(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__2));
v___x_964_ = l_Lean_stringToMessageData(v___x_963_);
return v___x_964_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__5(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__4));
v___x_967_ = l_Lean_stringToMessageData(v___x_966_);
return v___x_967_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__7(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__6));
v___x_970_ = l_Lean_stringToMessageData(v___x_969_);
return v___x_970_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__9(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__8));
v___x_973_ = l_Lean_stringToMessageData(v___x_972_);
return v___x_973_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__12(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__11));
v___x_978_ = l_Lean_stringToMessageData(v___x_977_);
return v___x_978_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__14(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__13));
v___x_981_ = l_Lean_stringToMessageData(v___x_980_);
return v___x_981_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__16(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__15));
v___x_984_ = l_Lean_stringToMessageData(v___x_983_);
return v___x_984_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__22(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__21));
v___x_993_ = l_Lean_stringToMessageData(v___x_992_);
return v___x_993_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___lam__2___closed__24(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__23));
v___x_996_ = l_Lean_stringToMessageData(v___x_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2(uint8_t v___x_997_, lean_object* v___x_998_, lean_object* v_fst_999_, lean_object* v___x_1000_, uint8_t v___x_1001_, lean_object* v_e_1002_, lean_object* v_snd_1003_, lean_object* v_____r_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v___y_1011_; lean_object* v_proof_1012_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v___y_1036_; uint8_t v___y_1037_; lean_object* v___x_1049_; lean_object* v___y_1051_; uint8_t v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; uint8_t v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v_a_1073_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; uint8_t v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; size_t v_sz_1113_; size_t v___x_1114_; lean_object* v___x_1115_; lean_object* v___y_1117_; uint8_t v___y_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; uint8_t v___y_1149_; lean_object* v___y_1150_; uint8_t v_fst_1174_; lean_object* v_fst_1175_; lean_object* v_snd_1176_; lean_object* v___x_1188_; lean_object* v___x_1189_; uint8_t v___x_1190_; 
v___x_1049_ = l_Lean_mkAppN(v___x_998_, v_fst_999_);
v_sz_1113_ = lean_array_size(v_fst_999_);
v___x_1114_ = ((size_t)0ULL);
v___x_1115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_1113_, v___x_1114_, v_fst_999_);
v___x_1188_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1189_ = lean_unsigned_to_nat(4u);
v___x_1190_ = l_Lean_Expr_isAppOfArity(v_snd_1003_, v___x_1188_, v___x_1189_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1191_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1192_ = lean_unsigned_to_nat(3u);
v___x_1193_ = l_Lean_Expr_isAppOfArity(v_snd_1003_, v___x_1191_, v___x_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec_ref(v___x_1115_);
lean_dec_ref(v___x_1049_);
lean_dec_ref(v_e_1002_);
v___x_1194_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1195_ = l_Lean_MessageData_ofConstName(v___x_1000_, v___x_1001_);
v___x_1196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1194_);
lean_ctor_set(v___x_1196_, 1, v___x_1195_);
v___x_1197_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1196_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_1199_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1198_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1199_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1199_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1208_ = l_Lean_Expr_appFn_x21(v_snd_1003_);
v___x_1209_ = l_Lean_Expr_appArg_x21(v___x_1208_);
lean_dec_ref(v___x_1208_);
v___x_1210_ = l_Lean_Expr_appArg_x21(v_snd_1003_);
v_fst_1174_ = v___x_1001_;
v_fst_1175_ = v___x_1209_;
v_snd_1176_ = v___x_1210_;
goto v___jp_1173_;
}
}
else
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1211_ = l_Lean_Expr_appFn_x21(v_snd_1003_);
v___x_1212_ = l_Lean_Expr_appFn_x21(v___x_1211_);
lean_dec_ref(v___x_1211_);
v___x_1213_ = l_Lean_Expr_appArg_x21(v___x_1212_);
lean_dec_ref(v___x_1212_);
v___x_1214_ = l_Lean_Expr_appArg_x21(v_snd_1003_);
v_fst_1174_ = v___x_997_;
v_fst_1175_ = v___x_1213_;
v_snd_1176_ = v___x_1214_;
goto v___jp_1173_;
}
v___jp_1010_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1013_, 0, v_proof_1012_);
v___x_1014_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1014_, 0, v___y_1011_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
lean_ctor_set_uint8(v___x_1014_, sizeof(void*)*2, v___x_997_);
v___x_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
return v___x_1015_;
}
v___jp_1016_:
{
if (lean_obj_tag(v___y_1018_) == 0)
{
lean_object* v_a_1019_; 
v_a_1019_ = lean_ctor_get(v___y_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___y_1018_, 1);
v___y_1011_ = v___y_1017_;
v_proof_1012_ = v_a_1019_;
goto v___jp_1010_;
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
lean_dec_ref(v___y_1017_);
v_a_1020_ = lean_ctor_get(v___y_1018_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___y_1018_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___y_1018_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___y_1018_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
v___jp_1028_:
{
if (v___y_1037_ == 0)
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
lean_dec_ref(v___y_1032_);
v___x_1038_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1039_ = l_Lean_MessageData_ofExpr(v___y_1036_);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = l_Lean_Exception_toMessageData(v___y_1034_);
v___x_1044_ = l_Lean_indentD(v___x_1043_);
v___x_1045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1042_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1045_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1047_, v___y_1030_, v___y_1033_, v___y_1031_, v___y_1029_);
v___y_1017_ = v___y_1035_;
v___y_1018_ = v___x_1048_;
goto v___jp_1016_;
}
else
{
lean_dec_ref(v___y_1036_);
lean_dec_ref(v___y_1034_);
v___y_1017_ = v___y_1035_;
v___y_1018_ = v___y_1032_;
goto v___jp_1016_;
}
}
v___jp_1050_:
{
lean_object* v___x_1057_; lean_object* v_a_1058_; lean_object* v___x_1059_; 
v___x_1057_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_1051_, v___y_1054_);
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1058_);
lean_dec_ref(v___x_1057_);
v___x_1059_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___x_1049_, v___y_1054_);
if (v___y_1052_ == 0)
{
lean_object* v_a_1060_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref(v___x_1059_);
v___y_1011_ = v_a_1058_;
v_proof_1012_ = v_a_1060_;
goto v___jp_1010_;
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1062_; 
v_a_1061_ = lean_ctor_get(v___x_1059_, 0);
lean_inc_n(v_a_1061_, 2);
lean_dec_ref(v___x_1059_);
v___x_1062_ = l_Lean_Meta_mkEqOfHEq(v_a_1061_, v___x_997_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_dec(v_a_1061_);
v___y_1017_ = v_a_1058_;
v___y_1018_ = v___x_1062_;
goto v___jp_1016_;
}
else
{
lean_object* v_a_1063_; uint8_t v___x_1064_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
v___x_1064_ = l_Lean_Exception_isInterrupt(v_a_1063_);
if (v___x_1064_ == 0)
{
uint8_t v___x_1065_; 
lean_inc(v_a_1063_);
v___x_1065_ = l_Lean_Exception_isRuntime(v_a_1063_);
v___y_1029_ = v___y_1056_;
v___y_1030_ = v___y_1053_;
v___y_1031_ = v___y_1055_;
v___y_1032_ = v___x_1062_;
v___y_1033_ = v___y_1054_;
v___y_1034_ = v_a_1063_;
v___y_1035_ = v_a_1058_;
v___y_1036_ = v_a_1061_;
v___y_1037_ = v___x_1065_;
goto v___jp_1028_;
}
else
{
v___y_1029_ = v___y_1056_;
v___y_1030_ = v___y_1053_;
v___y_1031_ = v___y_1055_;
v___y_1032_ = v___x_1062_;
v___y_1033_ = v___y_1054_;
v___y_1034_ = v_a_1063_;
v___y_1035_ = v_a_1058_;
v___y_1036_ = v_a_1061_;
v___y_1037_ = v___x_1064_;
goto v___jp_1028_;
}
}
}
}
v___jp_1066_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1074_ = lean_array_get_size(v_a_1073_);
v___x_1075_ = lean_unsigned_to_nat(0u);
v___x_1076_ = lean_nat_dec_eq(v___x_1074_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_dec_ref(v___y_1069_);
lean_dec_ref(v___x_1049_);
v___x_1077_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1078_ = l_Lean_MessageData_ofConstName(v___x_1000_, v___x_1001_);
v___x_1079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1079_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = lean_array_to_list(v_a_1073_);
v___x_1083_ = lean_box(0);
v___x_1084_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_1082_, v___x_1083_);
v___x_1085_ = l_Lean_MessageData_ofList(v___x_1084_);
v___x_1086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1081_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1086_, v___y_1067_, v___y_1072_, v___y_1068_, v___y_1071_);
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1087_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1087_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
else
{
lean_dec_ref(v_a_1073_);
lean_dec(v___x_1000_);
v___y_1051_ = v___y_1069_;
v___y_1052_ = v___y_1070_;
v___y_1053_ = v___y_1067_;
v___y_1054_ = v___y_1072_;
v___y_1055_ = v___y_1068_;
v___y_1056_ = v___y_1071_;
goto v___jp_1050_;
}
}
v___jp_1096_:
{
if (lean_obj_tag(v___y_1103_) == 0)
{
lean_object* v_a_1104_; 
v_a_1104_ = lean_ctor_get(v___y_1103_, 0);
lean_inc(v_a_1104_);
lean_dec_ref_known(v___y_1103_, 1);
v___y_1067_ = v___y_1097_;
v___y_1068_ = v___y_1098_;
v___y_1069_ = v___y_1099_;
v___y_1070_ = v___y_1100_;
v___y_1071_ = v___y_1101_;
v___y_1072_ = v___y_1102_;
v_a_1073_ = v_a_1104_;
goto v___jp_1066_;
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec_ref(v___y_1099_);
lean_dec_ref(v___x_1049_);
lean_dec(v___x_1000_);
v_a_1105_ = lean_ctor_get(v___y_1103_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___y_1103_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___y_1103_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___y_1103_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
v___jp_1116_:
{
lean_object* v___x_1123_; size_t v_sz_1124_; lean_object* v___x_1125_; 
v___x_1123_ = lean_box(0);
v_sz_1124_ = lean_array_size(v___x_1115_);
v___x_1125_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1115_, v_sz_1124_, v___x_1114_, v___x_1123_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; 
lean_dec_ref_known(v___x_1125_, 1);
v___x_1126_ = lean_unsigned_to_nat(0u);
v___x_1127_ = lean_array_get_size(v___x_1115_);
v___x_1128_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1129_ = lean_nat_dec_lt(v___x_1126_, v___x_1127_);
if (v___x_1129_ == 0)
{
lean_dec_ref(v___x_1115_);
v___y_1067_ = v___y_1119_;
v___y_1068_ = v___y_1121_;
v___y_1069_ = v___y_1117_;
v___y_1070_ = v___y_1118_;
v___y_1071_ = v___y_1122_;
v___y_1072_ = v___y_1120_;
v_a_1073_ = v___x_1128_;
goto v___jp_1066_;
}
else
{
uint8_t v___x_1130_; 
v___x_1130_ = lean_nat_dec_le(v___x_1127_, v___x_1127_);
if (v___x_1130_ == 0)
{
if (v___x_1129_ == 0)
{
lean_dec_ref(v___x_1115_);
v___y_1067_ = v___y_1119_;
v___y_1068_ = v___y_1121_;
v___y_1069_ = v___y_1117_;
v___y_1070_ = v___y_1118_;
v___y_1071_ = v___y_1122_;
v___y_1072_ = v___y_1120_;
v_a_1073_ = v___x_1128_;
goto v___jp_1066_;
}
else
{
size_t v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_usize_of_nat(v___x_1127_);
v___x_1132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12(v___x_1001_, v___x_1115_, v___x_1114_, v___x_1131_, v___x_1128_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
lean_dec_ref(v___x_1115_);
v___y_1097_ = v___y_1119_;
v___y_1098_ = v___y_1121_;
v___y_1099_ = v___y_1117_;
v___y_1100_ = v___y_1118_;
v___y_1101_ = v___y_1122_;
v___y_1102_ = v___y_1120_;
v___y_1103_ = v___x_1132_;
goto v___jp_1096_;
}
}
else
{
size_t v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_usize_of_nat(v___x_1127_);
v___x_1134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12(v___x_1001_, v___x_1115_, v___x_1114_, v___x_1133_, v___x_1128_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
lean_dec_ref(v___x_1115_);
v___y_1097_ = v___y_1119_;
v___y_1098_ = v___y_1121_;
v___y_1099_ = v___y_1117_;
v___y_1100_ = v___y_1118_;
v___y_1101_ = v___y_1122_;
v___y_1102_ = v___y_1120_;
v___y_1103_ = v___x_1134_;
goto v___jp_1096_;
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec_ref(v___y_1117_);
lean_dec_ref(v___x_1115_);
lean_dec_ref(v___x_1049_);
lean_dec(v___x_1000_);
v_a_1135_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1125_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1125_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
v___jp_1143_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
lean_dec_ref(v___y_1146_);
v___x_1151_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1152_ = l_Lean_MessageData_ofExpr(v___y_1144_);
v___x_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1151_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = l_Lean_MessageData_ofConstName(v___x_1000_, v___x_1001_);
v___x_1157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = l_Lean_MessageData_ofExpr(v_e_1002_);
v___x_1161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1159_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v___x_1162_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_1163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1161_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___x_1164_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1163_, v___y_1150_, v___y_1147_, v___y_1145_, v___y_1148_);
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
v___jp_1173_:
{
lean_object* v___x_1177_; 
lean_inc_ref(v_fst_1175_);
lean_inc_ref(v_e_1002_);
v___x_1177_ = l_Lean_Meta_isExprDefEq(v_e_1002_, v_fst_1175_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; uint8_t v___x_1179_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref_known(v___x_1177_, 1);
v___x_1179_ = lean_unbox(v_a_1178_);
lean_dec(v_a_1178_);
if (v___x_1179_ == 0)
{
lean_dec_ref(v___x_1115_);
lean_dec_ref(v___x_1049_);
v___y_1144_ = v_fst_1175_;
v___y_1145_ = v___y_1007_;
v___y_1146_ = v_snd_1176_;
v___y_1147_ = v___y_1006_;
v___y_1148_ = v___y_1008_;
v___y_1149_ = v_fst_1174_;
v___y_1150_ = v___y_1005_;
goto v___jp_1143_;
}
else
{
if (v___x_1001_ == 0)
{
lean_dec_ref(v_fst_1175_);
lean_dec_ref(v_e_1002_);
v___y_1117_ = v_snd_1176_;
v___y_1118_ = v_fst_1174_;
v___y_1119_ = v___y_1005_;
v___y_1120_ = v___y_1006_;
v___y_1121_ = v___y_1007_;
v___y_1122_ = v___y_1008_;
goto v___jp_1116_;
}
else
{
lean_dec_ref(v___x_1115_);
lean_dec_ref(v___x_1049_);
v___y_1144_ = v_fst_1175_;
v___y_1145_ = v___y_1007_;
v___y_1146_ = v_snd_1176_;
v___y_1147_ = v___y_1006_;
v___y_1148_ = v___y_1008_;
v___y_1149_ = v_fst_1174_;
v___y_1150_ = v___y_1005_;
goto v___jp_1143_;
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec_ref(v_snd_1176_);
lean_dec_ref(v_fst_1175_);
lean_dec_ref(v___x_1115_);
lean_dec_ref(v___x_1049_);
lean_dec_ref(v_e_1002_);
lean_dec(v___x_1000_);
v_a_1180_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1177_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1177_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__2___boxed(lean_object* v___x_1215_, lean_object* v___x_1216_, lean_object* v_fst_1217_, lean_object* v___x_1218_, lean_object* v___x_1219_, lean_object* v_e_1220_, lean_object* v_snd_1221_, lean_object* v_____r_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
uint8_t v___x_108641__boxed_1228_; uint8_t v___x_108645__boxed_1229_; lean_object* v_res_1230_; 
v___x_108641__boxed_1228_ = lean_unbox(v___x_1215_);
v___x_108645__boxed_1229_ = lean_unbox(v___x_1219_);
v_res_1230_ = l_Lean_Meta_rwMatcher___lam__2(v___x_108641__boxed_1228_, v___x_1216_, v_fst_1217_, v___x_1218_, v___x_108645__boxed_1229_, v_e_1220_, v_snd_1221_, v_____r_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec_ref(v_snd_1221_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(uint8_t v___x_1231_, lean_object* v_as_1232_, size_t v_i_1233_, size_t v_stop_1234_, lean_object* v_b_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_a_1242_; uint8_t v___x_1246_; 
v___x_1246_ = lean_usize_dec_eq(v_i_1233_, v_stop_1234_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; uint8_t v_a_1249_; lean_object* v___x_1251_; 
v___x_1247_ = lean_array_uget_borrowed(v_as_1232_, v_i_1233_);
v___x_1251_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v___x_1247_, v___y_1237_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; uint8_t v___x_1253_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
lean_dec_ref_known(v___x_1251_, 1);
v___x_1253_ = lean_unbox(v_a_1252_);
lean_dec(v_a_1252_);
if (v___x_1253_ == 0)
{
v_a_1249_ = v___x_1231_;
goto v___jp_1248_;
}
else
{
v_a_1242_ = v_b_1235_;
goto v___jp_1241_;
}
}
else
{
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1254_; uint8_t v___x_1255_; 
v_a_1254_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1254_);
lean_dec_ref_known(v___x_1251_, 1);
v___x_1255_ = lean_unbox(v_a_1254_);
lean_dec(v_a_1254_);
v_a_1249_ = v___x_1255_;
goto v___jp_1248_;
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec_ref(v_b_1235_);
v_a_1256_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1251_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1251_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
v___jp_1248_:
{
if (v_a_1249_ == 0)
{
v_a_1242_ = v_b_1235_;
goto v___jp_1241_;
}
else
{
lean_object* v___x_1250_; 
lean_inc(v___x_1247_);
v___x_1250_ = lean_array_push(v_b_1235_, v___x_1247_);
v_a_1242_ = v___x_1250_;
goto v___jp_1241_;
}
}
}
else
{
lean_object* v___x_1264_; 
v___x_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1264_, 0, v_b_1235_);
return v___x_1264_;
}
v___jp_1241_:
{
size_t v___x_1243_; size_t v___x_1244_; 
v___x_1243_ = ((size_t)1ULL);
v___x_1244_ = lean_usize_add(v_i_1233_, v___x_1243_);
v_i_1233_ = v___x_1244_;
v_b_1235_ = v_a_1242_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13___boxed(lean_object* v___x_1265_, lean_object* v_as_1266_, lean_object* v_i_1267_, lean_object* v_stop_1268_, lean_object* v_b_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
uint8_t v___x_109126__boxed_1275_; size_t v_i_boxed_1276_; size_t v_stop_boxed_1277_; lean_object* v_res_1278_; 
v___x_109126__boxed_1275_ = lean_unbox(v___x_1265_);
v_i_boxed_1276_ = lean_unbox_usize(v_i_1267_);
lean_dec(v_i_1267_);
v_stop_boxed_1277_ = lean_unbox_usize(v_stop_1268_);
lean_dec(v_stop_1268_);
v_res_1278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(v___x_109126__boxed_1275_, v_as_1266_, v_i_boxed_1276_, v_stop_boxed_1277_, v_b_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec_ref(v_as_1266_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3(uint8_t v___x_1279_, lean_object* v___x_1280_, lean_object* v_fst_1281_, lean_object* v___x_1282_, uint8_t v___x_1283_, lean_object* v_e_1284_, uint8_t v___y_1285_, lean_object* v_snd_1286_, lean_object* v_____r_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___y_1294_; lean_object* v_proof_1295_; lean_object* v___y_1300_; lean_object* v___y_1301_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; uint8_t v___y_1320_; lean_object* v___x_1332_; uint8_t v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1350_; uint8_t v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v_a_1356_; lean_object* v___y_1380_; uint8_t v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; size_t v_sz_1396_; size_t v___x_1397_; lean_object* v___x_1398_; uint8_t v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; uint8_t v_fst_1427_; lean_object* v_fst_1428_; lean_object* v_snd_1429_; lean_object* v___x_1463_; lean_object* v___x_1464_; uint8_t v___x_1465_; 
v___x_1332_ = l_Lean_mkAppN(v___x_1280_, v_fst_1281_);
v_sz_1396_ = lean_array_size(v_fst_1281_);
v___x_1397_ = ((size_t)0ULL);
v___x_1398_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_1396_, v___x_1397_, v_fst_1281_);
v___x_1463_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1464_ = lean_unsigned_to_nat(4u);
v___x_1465_ = l_Lean_Expr_isAppOfArity(v_snd_1286_, v___x_1463_, v___x_1464_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; 
v___x_1466_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1467_ = lean_unsigned_to_nat(3u);
v___x_1468_ = l_Lean_Expr_isAppOfArity(v_snd_1286_, v___x_1466_, v___x_1467_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
lean_dec_ref(v___x_1398_);
lean_dec_ref(v___x_1332_);
lean_dec_ref(v_e_1284_);
v___x_1469_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1470_ = l_Lean_MessageData_ofConstName(v___x_1282_, v___x_1468_);
v___x_1471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1469_);
lean_ctor_set(v___x_1471_, 1, v___x_1470_);
v___x_1472_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1471_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
v___x_1474_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1473_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
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
else
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1483_ = l_Lean_Expr_appFn_x21(v_snd_1286_);
v___x_1484_ = l_Lean_Expr_appArg_x21(v___x_1483_);
lean_dec_ref(v___x_1483_);
v___x_1485_ = l_Lean_Expr_appArg_x21(v_snd_1286_);
v_fst_1427_ = v___x_1465_;
v_fst_1428_ = v___x_1484_;
v_snd_1429_ = v___x_1485_;
goto v___jp_1426_;
}
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1486_ = l_Lean_Expr_appFn_x21(v_snd_1286_);
v___x_1487_ = l_Lean_Expr_appFn_x21(v___x_1486_);
lean_dec_ref(v___x_1486_);
v___x_1488_ = l_Lean_Expr_appArg_x21(v___x_1487_);
lean_dec_ref(v___x_1487_);
v___x_1489_ = l_Lean_Expr_appArg_x21(v_snd_1286_);
v_fst_1427_ = v___x_1279_;
v_fst_1428_ = v___x_1488_;
v_snd_1429_ = v___x_1489_;
goto v___jp_1426_;
}
v___jp_1293_:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1296_, 0, v_proof_1295_);
v___x_1297_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1297_, 0, v___y_1294_);
lean_ctor_set(v___x_1297_, 1, v___x_1296_);
lean_ctor_set_uint8(v___x_1297_, sizeof(void*)*2, v___x_1279_);
v___x_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
return v___x_1298_;
}
v___jp_1299_:
{
if (lean_obj_tag(v___y_1301_) == 0)
{
lean_object* v_a_1302_; 
v_a_1302_ = lean_ctor_get(v___y_1301_, 0);
lean_inc(v_a_1302_);
lean_dec_ref_known(v___y_1301_, 1);
v___y_1294_ = v___y_1300_;
v_proof_1295_ = v_a_1302_;
goto v___jp_1293_;
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_dec_ref(v___y_1300_);
v_a_1303_ = lean_ctor_get(v___y_1301_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___y_1301_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___y_1301_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___y_1301_);
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
}
v___jp_1311_:
{
if (v___y_1320_ == 0)
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_dec_ref(v___y_1312_);
v___x_1321_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1322_ = l_Lean_MessageData_ofExpr(v___y_1317_);
v___x_1323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1321_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
v___x_1324_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1323_);
lean_ctor_set(v___x_1325_, 1, v___x_1324_);
v___x_1326_ = l_Lean_Exception_toMessageData(v___y_1316_);
v___x_1327_ = l_Lean_indentD(v___x_1326_);
v___x_1328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1325_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
v___x_1329_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1328_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
v___x_1331_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1330_, v___y_1319_, v___y_1315_, v___y_1318_, v___y_1313_);
v___y_1300_ = v___y_1314_;
v___y_1301_ = v___x_1331_;
goto v___jp_1299_;
}
else
{
lean_dec_ref(v___y_1317_);
lean_dec_ref(v___y_1316_);
v___y_1300_ = v___y_1314_;
v___y_1301_ = v___y_1312_;
goto v___jp_1299_;
}
}
v___jp_1333_:
{
lean_object* v___x_1340_; lean_object* v_a_1341_; lean_object* v___x_1342_; 
v___x_1340_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_1335_, v___y_1337_);
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1341_);
lean_dec_ref(v___x_1340_);
v___x_1342_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___x_1332_, v___y_1337_);
if (v___y_1334_ == 0)
{
lean_object* v_a_1343_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_a_1343_);
lean_dec_ref(v___x_1342_);
v___y_1294_ = v_a_1341_;
v_proof_1295_ = v_a_1343_;
goto v___jp_1293_;
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1345_; 
v_a_1344_ = lean_ctor_get(v___x_1342_, 0);
lean_inc_n(v_a_1344_, 2);
lean_dec_ref(v___x_1342_);
v___x_1345_ = l_Lean_Meta_mkEqOfHEq(v_a_1344_, v___x_1279_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_dec(v_a_1344_);
v___y_1300_ = v_a_1341_;
v___y_1301_ = v___x_1345_;
goto v___jp_1299_;
}
else
{
lean_object* v_a_1346_; uint8_t v___x_1347_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
v___x_1347_ = l_Lean_Exception_isInterrupt(v_a_1346_);
if (v___x_1347_ == 0)
{
uint8_t v___x_1348_; 
lean_inc(v_a_1346_);
v___x_1348_ = l_Lean_Exception_isRuntime(v_a_1346_);
v___y_1312_ = v___x_1345_;
v___y_1313_ = v___y_1339_;
v___y_1314_ = v_a_1341_;
v___y_1315_ = v___y_1337_;
v___y_1316_ = v_a_1346_;
v___y_1317_ = v_a_1344_;
v___y_1318_ = v___y_1338_;
v___y_1319_ = v___y_1336_;
v___y_1320_ = v___x_1348_;
goto v___jp_1311_;
}
else
{
v___y_1312_ = v___x_1345_;
v___y_1313_ = v___y_1339_;
v___y_1314_ = v_a_1341_;
v___y_1315_ = v___y_1337_;
v___y_1316_ = v_a_1346_;
v___y_1317_ = v_a_1344_;
v___y_1318_ = v___y_1338_;
v___y_1319_ = v___y_1336_;
v___y_1320_ = v___x_1347_;
goto v___jp_1311_;
}
}
}
}
v___jp_1349_:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; 
v___x_1357_ = lean_array_get_size(v_a_1356_);
v___x_1358_ = lean_unsigned_to_nat(0u);
v___x_1359_ = lean_nat_dec_eq(v___x_1357_, v___x_1358_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec_ref(v___y_1352_);
lean_dec_ref(v___x_1332_);
v___x_1360_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1361_ = l_Lean_MessageData_ofConstName(v___x_1282_, v___x_1359_);
v___x_1362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1360_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
v___x_1363_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1362_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
v___x_1365_ = lean_array_to_list(v_a_1356_);
v___x_1366_ = lean_box(0);
v___x_1367_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_1365_, v___x_1366_);
v___x_1368_ = l_Lean_MessageData_ofList(v___x_1367_);
v___x_1369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1364_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
v___x_1370_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1369_, v___y_1355_, v___y_1354_, v___y_1353_, v___y_1350_);
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1370_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1370_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
else
{
lean_dec_ref(v_a_1356_);
lean_dec(v___x_1282_);
v___y_1334_ = v___y_1351_;
v___y_1335_ = v___y_1352_;
v___y_1336_ = v___y_1355_;
v___y_1337_ = v___y_1354_;
v___y_1338_ = v___y_1353_;
v___y_1339_ = v___y_1350_;
goto v___jp_1333_;
}
}
v___jp_1379_:
{
if (lean_obj_tag(v___y_1386_) == 0)
{
lean_object* v_a_1387_; 
v_a_1387_ = lean_ctor_get(v___y_1386_, 0);
lean_inc(v_a_1387_);
lean_dec_ref_known(v___y_1386_, 1);
v___y_1350_ = v___y_1380_;
v___y_1351_ = v___y_1381_;
v___y_1352_ = v___y_1385_;
v___y_1353_ = v___y_1384_;
v___y_1354_ = v___y_1383_;
v___y_1355_ = v___y_1382_;
v_a_1356_ = v_a_1387_;
goto v___jp_1349_;
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
lean_dec_ref(v___y_1385_);
lean_dec_ref(v___x_1332_);
lean_dec(v___x_1282_);
v_a_1388_ = lean_ctor_get(v___y_1386_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___y_1386_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___y_1386_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___y_1386_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
v___jp_1399_:
{
lean_object* v___x_1406_; size_t v_sz_1407_; lean_object* v___x_1408_; 
v___x_1406_ = lean_box(0);
v_sz_1407_ = lean_array_size(v___x_1398_);
v___x_1408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1398_, v_sz_1407_, v___x_1397_, v___x_1406_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
lean_dec_ref_known(v___x_1408_, 1);
v___x_1409_ = lean_unsigned_to_nat(0u);
v___x_1410_ = lean_array_get_size(v___x_1398_);
v___x_1411_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1412_ = lean_nat_dec_lt(v___x_1409_, v___x_1410_);
if (v___x_1412_ == 0)
{
lean_dec_ref(v___x_1398_);
v___y_1350_ = v___y_1405_;
v___y_1351_ = v___y_1400_;
v___y_1352_ = v___y_1401_;
v___y_1353_ = v___y_1404_;
v___y_1354_ = v___y_1403_;
v___y_1355_ = v___y_1402_;
v_a_1356_ = v___x_1411_;
goto v___jp_1349_;
}
else
{
uint8_t v___x_1413_; 
v___x_1413_ = lean_nat_dec_le(v___x_1410_, v___x_1410_);
if (v___x_1413_ == 0)
{
if (v___x_1412_ == 0)
{
lean_dec_ref(v___x_1398_);
v___y_1350_ = v___y_1405_;
v___y_1351_ = v___y_1400_;
v___y_1352_ = v___y_1401_;
v___y_1353_ = v___y_1404_;
v___y_1354_ = v___y_1403_;
v___y_1355_ = v___y_1402_;
v_a_1356_ = v___x_1411_;
goto v___jp_1349_;
}
else
{
size_t v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = lean_usize_of_nat(v___x_1410_);
v___x_1415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(v___x_1283_, v___x_1398_, v___x_1397_, v___x_1414_, v___x_1411_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec_ref(v___x_1398_);
v___y_1380_ = v___y_1405_;
v___y_1381_ = v___y_1400_;
v___y_1382_ = v___y_1402_;
v___y_1383_ = v___y_1403_;
v___y_1384_ = v___y_1404_;
v___y_1385_ = v___y_1401_;
v___y_1386_ = v___x_1415_;
goto v___jp_1379_;
}
}
else
{
size_t v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = lean_usize_of_nat(v___x_1410_);
v___x_1417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__13(v___x_1283_, v___x_1398_, v___x_1397_, v___x_1416_, v___x_1411_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec_ref(v___x_1398_);
v___y_1380_ = v___y_1405_;
v___y_1381_ = v___y_1400_;
v___y_1382_ = v___y_1402_;
v___y_1383_ = v___y_1403_;
v___y_1384_ = v___y_1404_;
v___y_1385_ = v___y_1401_;
v___y_1386_ = v___x_1417_;
goto v___jp_1379_;
}
}
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec_ref(v___y_1401_);
lean_dec_ref(v___x_1398_);
lean_dec_ref(v___x_1332_);
lean_dec(v___x_1282_);
v_a_1418_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1408_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1408_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
v___jp_1426_:
{
lean_object* v___x_1430_; 
lean_inc_ref(v_fst_1428_);
lean_inc_ref(v_e_1284_);
v___x_1430_ = l_Lean_Meta_isExprDefEq(v_e_1284_, v_fst_1428_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; uint8_t v___x_1432_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v___x_1432_ = lean_unbox(v_a_1431_);
lean_dec(v_a_1431_);
if (v___x_1432_ == 0)
{
if (v___x_1283_ == 0)
{
lean_dec_ref(v_fst_1428_);
lean_dec_ref(v_e_1284_);
v___y_1400_ = v_fst_1427_;
v___y_1401_ = v_snd_1429_;
v___y_1402_ = v___y_1288_;
v___y_1403_ = v___y_1289_;
v___y_1404_ = v___y_1290_;
v___y_1405_ = v___y_1291_;
goto v___jp_1399_;
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec_ref(v_snd_1429_);
lean_dec_ref(v___x_1398_);
lean_dec_ref(v___x_1332_);
v___x_1433_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1434_ = l_Lean_MessageData_ofExpr(v_fst_1428_);
v___x_1435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1433_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
v___x_1436_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1435_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
v___x_1438_ = l_Lean_MessageData_ofConstName(v___x_1282_, v___y_1285_);
v___x_1439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1437_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
v___x_1440_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1439_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
v___x_1442_ = l_Lean_MessageData_ofExpr(v_e_1284_);
v___x_1443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1441_);
lean_ctor_set(v___x_1443_, 1, v___x_1442_);
v___x_1444_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_1445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1443_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
v___x_1446_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1445_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1446_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1446_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
else
{
lean_dec_ref(v_fst_1428_);
lean_dec_ref(v_e_1284_);
v___y_1400_ = v_fst_1427_;
v___y_1401_ = v_snd_1429_;
v___y_1402_ = v___y_1288_;
v___y_1403_ = v___y_1289_;
v___y_1404_ = v___y_1290_;
v___y_1405_ = v___y_1291_;
goto v___jp_1399_;
}
}
else
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_dec_ref(v_snd_1429_);
lean_dec_ref(v_fst_1428_);
lean_dec_ref(v___x_1398_);
lean_dec_ref(v___x_1332_);
lean_dec_ref(v_e_1284_);
lean_dec(v___x_1282_);
v_a_1455_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1430_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1430_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__3___boxed(lean_object* v___x_1490_, lean_object* v___x_1491_, lean_object* v_fst_1492_, lean_object* v___x_1493_, lean_object* v___x_1494_, lean_object* v_e_1495_, lean_object* v___y_1496_, lean_object* v_snd_1497_, lean_object* v_____r_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
uint8_t v___x_109233__boxed_1504_; uint8_t v___x_109237__boxed_1505_; uint8_t v___y_109238__boxed_1506_; lean_object* v_res_1507_; 
v___x_109233__boxed_1504_ = lean_unbox(v___x_1490_);
v___x_109237__boxed_1505_ = lean_unbox(v___x_1494_);
v___y_109238__boxed_1506_ = lean_unbox(v___y_1496_);
v_res_1507_ = l_Lean_Meta_rwMatcher___lam__3(v___x_109233__boxed_1504_, v___x_1491_, v_fst_1492_, v___x_1493_, v___x_109237__boxed_1505_, v_e_1495_, v___y_109238__boxed_1506_, v_snd_1497_, v_____r_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec_ref(v_snd_1497_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4(uint8_t v___x_1508_, lean_object* v___x_1509_, lean_object* v_fst_1510_, lean_object* v___x_1511_, uint8_t v___x_1512_, lean_object* v_e_1513_, lean_object* v_snd_1514_, lean_object* v_____r_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___y_1522_; lean_object* v_proof_1523_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; uint8_t v___y_1548_; lean_object* v___x_1560_; lean_object* v___y_1562_; uint8_t v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; uint8_t v___y_1583_; lean_object* v_a_1584_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; uint8_t v___y_1613_; lean_object* v___y_1614_; size_t v_sz_1624_; size_t v___x_1625_; lean_object* v___x_1626_; lean_object* v___y_1628_; uint8_t v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; uint8_t v___y_1660_; lean_object* v___y_1661_; uint8_t v_fst_1685_; lean_object* v_fst_1686_; lean_object* v_snd_1687_; lean_object* v___x_1699_; lean_object* v___x_1700_; uint8_t v___x_1701_; 
v___x_1560_ = l_Lean_mkAppN(v___x_1509_, v_fst_1510_);
v_sz_1624_ = lean_array_size(v_fst_1510_);
v___x_1625_ = ((size_t)0ULL);
v___x_1626_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_1624_, v___x_1625_, v_fst_1510_);
v___x_1699_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_1700_ = lean_unsigned_to_nat(4u);
v___x_1701_ = l_Lean_Expr_isAppOfArity(v_snd_1514_, v___x_1699_, v___x_1700_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; lean_object* v___x_1703_; uint8_t v___x_1704_; 
v___x_1702_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_1703_ = lean_unsigned_to_nat(3u);
v___x_1704_ = l_Lean_Expr_isAppOfArity(v_snd_1514_, v___x_1702_, v___x_1703_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
lean_dec_ref(v___x_1626_);
lean_dec_ref(v___x_1560_);
lean_dec_ref(v_e_1513_);
v___x_1705_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
v___x_1706_ = l_Lean_MessageData_ofConstName(v___x_1511_, v___x_1512_);
v___x_1707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1705_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
v___x_1708_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
v___x_1709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1707_);
lean_ctor_set(v___x_1709_, 1, v___x_1708_);
v___x_1710_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1709_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1710_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1710_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1711_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
else
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1719_ = l_Lean_Expr_appFn_x21(v_snd_1514_);
v___x_1720_ = l_Lean_Expr_appArg_x21(v___x_1719_);
lean_dec_ref(v___x_1719_);
v___x_1721_ = l_Lean_Expr_appArg_x21(v_snd_1514_);
v_fst_1685_ = v___x_1512_;
v_fst_1686_ = v___x_1720_;
v_snd_1687_ = v___x_1721_;
goto v___jp_1684_;
}
}
else
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1722_ = l_Lean_Expr_appFn_x21(v_snd_1514_);
v___x_1723_ = l_Lean_Expr_appFn_x21(v___x_1722_);
lean_dec_ref(v___x_1722_);
v___x_1724_ = l_Lean_Expr_appArg_x21(v___x_1723_);
lean_dec_ref(v___x_1723_);
v___x_1725_ = l_Lean_Expr_appArg_x21(v_snd_1514_);
v_fst_1685_ = v___x_1508_;
v_fst_1686_ = v___x_1724_;
v_snd_1687_ = v___x_1725_;
goto v___jp_1684_;
}
v___jp_1521_:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1524_, 0, v_proof_1523_);
v___x_1525_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1525_, 0, v___y_1522_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
lean_ctor_set_uint8(v___x_1525_, sizeof(void*)*2, v___x_1508_);
v___x_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
return v___x_1526_;
}
v___jp_1527_:
{
if (lean_obj_tag(v___y_1529_) == 0)
{
lean_object* v_a_1530_; 
v_a_1530_ = lean_ctor_get(v___y_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___y_1529_, 1);
v___y_1522_ = v___y_1528_;
v_proof_1523_ = v_a_1530_;
goto v___jp_1521_;
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_dec_ref(v___y_1528_);
v_a_1531_ = lean_ctor_get(v___y_1529_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___y_1529_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___y_1529_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___y_1529_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
v___jp_1539_:
{
if (v___y_1548_ == 0)
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
lean_dec_ref(v___y_1541_);
v___x_1549_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_1550_ = l_Lean_MessageData_ofExpr(v___y_1544_);
v___x_1551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1549_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_1553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = l_Lean_Exception_toMessageData(v___y_1545_);
v___x_1555_ = l_Lean_indentD(v___x_1554_);
v___x_1556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1553_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
v___x_1557_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_1558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1556_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1558_, v___y_1540_, v___y_1542_, v___y_1547_, v___y_1543_);
v___y_1528_ = v___y_1546_;
v___y_1529_ = v___x_1559_;
goto v___jp_1527_;
}
else
{
lean_dec_ref(v___y_1545_);
lean_dec_ref(v___y_1544_);
v___y_1528_ = v___y_1546_;
v___y_1529_ = v___y_1541_;
goto v___jp_1527_;
}
}
v___jp_1561_:
{
lean_object* v___x_1568_; lean_object* v_a_1569_; lean_object* v___x_1570_; 
v___x_1568_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_1562_, v___y_1565_);
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
lean_dec_ref(v___x_1568_);
v___x_1570_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___x_1560_, v___y_1565_);
if (v___y_1563_ == 0)
{
lean_object* v_a_1571_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1571_);
lean_dec_ref(v___x_1570_);
v___y_1522_ = v_a_1569_;
v_proof_1523_ = v_a_1571_;
goto v___jp_1521_;
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1573_; 
v_a_1572_ = lean_ctor_get(v___x_1570_, 0);
lean_inc_n(v_a_1572_, 2);
lean_dec_ref(v___x_1570_);
v___x_1573_ = l_Lean_Meta_mkEqOfHEq(v_a_1572_, v___x_1508_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_dec(v_a_1572_);
v___y_1528_ = v_a_1569_;
v___y_1529_ = v___x_1573_;
goto v___jp_1527_;
}
else
{
lean_object* v_a_1574_; uint8_t v___x_1575_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1574_);
v___x_1575_ = l_Lean_Exception_isInterrupt(v_a_1574_);
if (v___x_1575_ == 0)
{
uint8_t v___x_1576_; 
lean_inc(v_a_1574_);
v___x_1576_ = l_Lean_Exception_isRuntime(v_a_1574_);
v___y_1540_ = v___y_1564_;
v___y_1541_ = v___x_1573_;
v___y_1542_ = v___y_1565_;
v___y_1543_ = v___y_1567_;
v___y_1544_ = v_a_1572_;
v___y_1545_ = v_a_1574_;
v___y_1546_ = v_a_1569_;
v___y_1547_ = v___y_1566_;
v___y_1548_ = v___x_1576_;
goto v___jp_1539_;
}
else
{
v___y_1540_ = v___y_1564_;
v___y_1541_ = v___x_1573_;
v___y_1542_ = v___y_1565_;
v___y_1543_ = v___y_1567_;
v___y_1544_ = v_a_1572_;
v___y_1545_ = v_a_1574_;
v___y_1546_ = v_a_1569_;
v___y_1547_ = v___y_1566_;
v___y_1548_ = v___x_1575_;
goto v___jp_1539_;
}
}
}
}
v___jp_1577_:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v___x_1585_ = lean_array_get_size(v_a_1584_);
v___x_1586_ = lean_unsigned_to_nat(0u);
v___x_1587_ = lean_nat_dec_eq(v___x_1585_, v___x_1586_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_dec_ref(v___y_1580_);
lean_dec_ref(v___x_1560_);
v___x_1588_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
v___x_1589_ = l_Lean_MessageData_ofConstName(v___x_1511_, v___x_1512_);
v___x_1590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_1592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = lean_array_to_list(v_a_1584_);
v___x_1594_ = lean_box(0);
v___x_1595_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_1593_, v___x_1594_);
v___x_1596_ = l_Lean_MessageData_ofList(v___x_1595_);
v___x_1597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1592_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1597_, v___y_1582_, v___y_1581_, v___y_1579_, v___y_1578_);
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1598_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1598_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
else
{
lean_dec_ref(v_a_1584_);
lean_dec(v___x_1511_);
v___y_1562_ = v___y_1580_;
v___y_1563_ = v___y_1583_;
v___y_1564_ = v___y_1582_;
v___y_1565_ = v___y_1581_;
v___y_1566_ = v___y_1579_;
v___y_1567_ = v___y_1578_;
goto v___jp_1561_;
}
}
v___jp_1607_:
{
if (lean_obj_tag(v___y_1614_) == 0)
{
lean_object* v_a_1615_; 
v_a_1615_ = lean_ctor_get(v___y_1614_, 0);
lean_inc(v_a_1615_);
lean_dec_ref_known(v___y_1614_, 1);
v___y_1578_ = v___y_1608_;
v___y_1579_ = v___y_1609_;
v___y_1580_ = v___y_1610_;
v___y_1581_ = v___y_1611_;
v___y_1582_ = v___y_1612_;
v___y_1583_ = v___y_1613_;
v_a_1584_ = v_a_1615_;
goto v___jp_1577_;
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
lean_dec_ref(v___y_1610_);
lean_dec_ref(v___x_1560_);
lean_dec(v___x_1511_);
v_a_1616_ = lean_ctor_get(v___y_1614_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___y_1614_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___y_1614_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___y_1614_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
v___jp_1627_:
{
lean_object* v___x_1634_; size_t v_sz_1635_; lean_object* v___x_1636_; 
v___x_1634_ = lean_box(0);
v_sz_1635_ = lean_array_size(v___x_1626_);
v___x_1636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___x_1626_, v_sz_1635_, v___x_1625_, v___x_1634_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; uint8_t v___x_1640_; 
lean_dec_ref_known(v___x_1636_, 1);
v___x_1637_ = lean_unsigned_to_nat(0u);
v___x_1638_ = lean_array_get_size(v___x_1626_);
v___x_1639_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_1640_ = lean_nat_dec_lt(v___x_1637_, v___x_1638_);
if (v___x_1640_ == 0)
{
lean_dec_ref(v___x_1626_);
v___y_1578_ = v___y_1633_;
v___y_1579_ = v___y_1632_;
v___y_1580_ = v___y_1628_;
v___y_1581_ = v___y_1631_;
v___y_1582_ = v___y_1630_;
v___y_1583_ = v___y_1629_;
v_a_1584_ = v___x_1639_;
goto v___jp_1577_;
}
else
{
uint8_t v___x_1641_; 
v___x_1641_ = lean_nat_dec_le(v___x_1638_, v___x_1638_);
if (v___x_1641_ == 0)
{
if (v___x_1640_ == 0)
{
lean_dec_ref(v___x_1626_);
v___y_1578_ = v___y_1633_;
v___y_1579_ = v___y_1632_;
v___y_1580_ = v___y_1628_;
v___y_1581_ = v___y_1631_;
v___y_1582_ = v___y_1630_;
v___y_1583_ = v___y_1629_;
v_a_1584_ = v___x_1639_;
goto v___jp_1577_;
}
else
{
size_t v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = lean_usize_of_nat(v___x_1638_);
v___x_1643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12(v___x_1512_, v___x_1626_, v___x_1625_, v___x_1642_, v___x_1639_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
lean_dec_ref(v___x_1626_);
v___y_1608_ = v___y_1633_;
v___y_1609_ = v___y_1632_;
v___y_1610_ = v___y_1628_;
v___y_1611_ = v___y_1631_;
v___y_1612_ = v___y_1630_;
v___y_1613_ = v___y_1629_;
v___y_1614_ = v___x_1643_;
goto v___jp_1607_;
}
}
else
{
size_t v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = lean_usize_of_nat(v___x_1638_);
v___x_1645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__12(v___x_1512_, v___x_1626_, v___x_1625_, v___x_1644_, v___x_1639_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
lean_dec_ref(v___x_1626_);
v___y_1608_ = v___y_1633_;
v___y_1609_ = v___y_1632_;
v___y_1610_ = v___y_1628_;
v___y_1611_ = v___y_1631_;
v___y_1612_ = v___y_1630_;
v___y_1613_ = v___y_1629_;
v___y_1614_ = v___x_1645_;
goto v___jp_1607_;
}
}
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_dec_ref(v___y_1628_);
lean_dec_ref(v___x_1626_);
lean_dec_ref(v___x_1560_);
lean_dec(v___x_1511_);
v_a_1646_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1636_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1636_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
v___jp_1654_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_dec_ref(v___y_1657_);
v___x_1662_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_1663_ = l_Lean_MessageData_ofExpr(v___y_1661_);
v___x_1664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1662_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
v___x_1665_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_1666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1664_);
lean_ctor_set(v___x_1666_, 1, v___x_1665_);
v___x_1667_ = l_Lean_MessageData_ofConstName(v___x_1511_, v___x_1512_);
v___x_1668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1666_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
v___x_1669_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_1670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1668_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v___x_1671_ = l_Lean_MessageData_ofExpr(v_e_1513_);
v___x_1672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1670_);
lean_ctor_set(v___x_1672_, 1, v___x_1671_);
v___x_1673_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_1674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1672_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
v___x_1675_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_1674_, v___y_1655_, v___y_1656_, v___y_1658_, v___y_1659_);
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1675_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1675_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
v___jp_1684_:
{
lean_object* v___x_1688_; 
lean_inc_ref(v_fst_1686_);
lean_inc_ref(v_e_1513_);
v___x_1688_ = l_Lean_Meta_isExprDefEq(v_e_1513_, v_fst_1686_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; uint8_t v___x_1690_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_a_1689_);
lean_dec_ref_known(v___x_1688_, 1);
v___x_1690_ = lean_unbox(v_a_1689_);
lean_dec(v_a_1689_);
if (v___x_1690_ == 0)
{
lean_dec_ref(v___x_1626_);
lean_dec_ref(v___x_1560_);
v___y_1655_ = v___y_1516_;
v___y_1656_ = v___y_1517_;
v___y_1657_ = v_snd_1687_;
v___y_1658_ = v___y_1518_;
v___y_1659_ = v___y_1519_;
v___y_1660_ = v_fst_1685_;
v___y_1661_ = v_fst_1686_;
goto v___jp_1654_;
}
else
{
if (v___x_1512_ == 0)
{
lean_dec_ref(v_fst_1686_);
lean_dec_ref(v_e_1513_);
v___y_1628_ = v_snd_1687_;
v___y_1629_ = v_fst_1685_;
v___y_1630_ = v___y_1516_;
v___y_1631_ = v___y_1517_;
v___y_1632_ = v___y_1518_;
v___y_1633_ = v___y_1519_;
goto v___jp_1627_;
}
else
{
lean_dec_ref(v___x_1626_);
lean_dec_ref(v___x_1560_);
v___y_1655_ = v___y_1516_;
v___y_1656_ = v___y_1517_;
v___y_1657_ = v_snd_1687_;
v___y_1658_ = v___y_1518_;
v___y_1659_ = v___y_1519_;
v___y_1660_ = v_fst_1685_;
v___y_1661_ = v_fst_1686_;
goto v___jp_1654_;
}
}
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
lean_dec_ref(v_snd_1687_);
lean_dec_ref(v_fst_1686_);
lean_dec_ref(v___x_1626_);
lean_dec_ref(v___x_1560_);
lean_dec_ref(v_e_1513_);
lean_dec(v___x_1511_);
v_a_1691_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1688_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1688_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___lam__4___boxed(lean_object* v___x_1726_, lean_object* v___x_1727_, lean_object* v_fst_1728_, lean_object* v___x_1729_, lean_object* v___x_1730_, lean_object* v_e_1731_, lean_object* v_snd_1732_, lean_object* v_____r_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
uint8_t v___x_109721__boxed_1739_; uint8_t v___x_109725__boxed_1740_; lean_object* v_res_1741_; 
v___x_109721__boxed_1739_ = lean_unbox(v___x_1726_);
v___x_109725__boxed_1740_ = lean_unbox(v___x_1730_);
v_res_1741_ = l_Lean_Meta_rwMatcher___lam__4(v___x_109721__boxed_1739_, v___x_1727_, v_fst_1728_, v___x_1729_, v___x_109725__boxed_1740_, v_e_1731_, v_snd_1732_, v_____r_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec_ref(v_snd_1732_);
return v_res_1741_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1742_; double v___x_1743_; 
v___x_1742_ = lean_unsigned_to_nat(0u);
v___x_1743_ = lean_float_of_nat(v___x_1742_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(lean_object* v_cls_1747_, lean_object* v_msg_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v_ref_1754_; lean_object* v___x_1755_; lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1800_; 
v_ref_1754_ = lean_ctor_get(v___y_1751_, 5);
v___x_1755_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1800_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1800_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1760_; lean_object* v_traceState_1761_; lean_object* v_env_1762_; lean_object* v_nextMacroScope_1763_; lean_object* v_ngen_1764_; lean_object* v_auxDeclNGen_1765_; lean_object* v_cache_1766_; lean_object* v_messages_1767_; lean_object* v_infoState_1768_; lean_object* v_snapshotTasks_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1799_; 
v___x_1760_ = lean_st_ref_take(v___y_1752_);
v_traceState_1761_ = lean_ctor_get(v___x_1760_, 4);
v_env_1762_ = lean_ctor_get(v___x_1760_, 0);
v_nextMacroScope_1763_ = lean_ctor_get(v___x_1760_, 1);
v_ngen_1764_ = lean_ctor_get(v___x_1760_, 2);
v_auxDeclNGen_1765_ = lean_ctor_get(v___x_1760_, 3);
v_cache_1766_ = lean_ctor_get(v___x_1760_, 5);
v_messages_1767_ = lean_ctor_get(v___x_1760_, 6);
v_infoState_1768_ = lean_ctor_get(v___x_1760_, 7);
v_snapshotTasks_1769_ = lean_ctor_get(v___x_1760_, 8);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1771_ = v___x_1760_;
v_isShared_1772_ = v_isSharedCheck_1799_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_snapshotTasks_1769_);
lean_inc(v_infoState_1768_);
lean_inc(v_messages_1767_);
lean_inc(v_cache_1766_);
lean_inc(v_traceState_1761_);
lean_inc(v_auxDeclNGen_1765_);
lean_inc(v_ngen_1764_);
lean_inc(v_nextMacroScope_1763_);
lean_inc(v_env_1762_);
lean_dec(v___x_1760_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1799_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
uint64_t v_tid_1773_; lean_object* v_traces_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1798_; 
v_tid_1773_ = lean_ctor_get_uint64(v_traceState_1761_, sizeof(void*)*1);
v_traces_1774_ = lean_ctor_get(v_traceState_1761_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_traceState_1761_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1776_ = v_traceState_1761_;
v_isShared_1777_ = v_isSharedCheck_1798_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_traces_1774_);
lean_dec(v_traceState_1761_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1798_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1778_; double v___x_1779_; uint8_t v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1788_; 
v___x_1778_ = lean_box(0);
v___x_1779_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0);
v___x_1780_ = 0;
v___x_1781_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1));
v___x_1782_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1782_, 0, v_cls_1747_);
lean_ctor_set(v___x_1782_, 1, v___x_1778_);
lean_ctor_set(v___x_1782_, 2, v___x_1781_);
lean_ctor_set_float(v___x_1782_, sizeof(void*)*3, v___x_1779_);
lean_ctor_set_float(v___x_1782_, sizeof(void*)*3 + 8, v___x_1779_);
lean_ctor_set_uint8(v___x_1782_, sizeof(void*)*3 + 16, v___x_1780_);
v___x_1783_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__2));
v___x_1784_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1782_);
lean_ctor_set(v___x_1784_, 1, v_a_1756_);
lean_ctor_set(v___x_1784_, 2, v___x_1783_);
lean_inc(v_ref_1754_);
v___x_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1785_, 0, v_ref_1754_);
lean_ctor_set(v___x_1785_, 1, v___x_1784_);
v___x_1786_ = l_Lean_PersistentArray_push___redArg(v_traces_1774_, v___x_1785_);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v___x_1786_);
v___x_1788_ = v___x_1776_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1786_);
lean_ctor_set_uint64(v_reuseFailAlloc_1797_, sizeof(void*)*1, v_tid_1773_);
v___x_1788_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
lean_object* v___x_1790_; 
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 4, v___x_1788_);
v___x_1790_ = v___x_1771_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_env_1762_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_nextMacroScope_1763_);
lean_ctor_set(v_reuseFailAlloc_1796_, 2, v_ngen_1764_);
lean_ctor_set(v_reuseFailAlloc_1796_, 3, v_auxDeclNGen_1765_);
lean_ctor_set(v_reuseFailAlloc_1796_, 4, v___x_1788_);
lean_ctor_set(v_reuseFailAlloc_1796_, 5, v_cache_1766_);
lean_ctor_set(v_reuseFailAlloc_1796_, 6, v_messages_1767_);
lean_ctor_set(v_reuseFailAlloc_1796_, 7, v_infoState_1768_);
lean_ctor_set(v_reuseFailAlloc_1796_, 8, v_snapshotTasks_1769_);
v___x_1790_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1794_; 
v___x_1791_ = lean_st_ref_set(v___y_1752_, v___x_1790_);
v___x_1792_ = lean_box(0);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1792_);
v___x_1794_ = v___x_1758_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1792_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___boxed(lean_object* v_cls_1801_, lean_object* v_msg_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v_cls_1801_, v_msg_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(lean_object* v_as_1809_, size_t v_i_1810_, size_t v_stop_1811_, lean_object* v_b_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v_a_1819_; uint8_t v___x_1823_; 
v___x_1823_ = lean_usize_dec_eq(v_i_1810_, v_stop_1811_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1827_; 
v___x_1824_ = lean_array_uget_borrowed(v_as_1809_, v_i_1810_);
v___x_1827_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v___x_1824_, v___y_1814_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; uint8_t v___x_1829_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_a_1828_);
lean_dec_ref_known(v___x_1827_, 1);
v___x_1829_ = lean_unbox(v_a_1828_);
lean_dec(v_a_1828_);
if (v___x_1829_ == 0)
{
goto v___jp_1825_;
}
else
{
v_a_1819_ = v_b_1812_;
goto v___jp_1818_;
}
}
else
{
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1830_; uint8_t v___x_1831_; 
v_a_1830_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_a_1830_);
lean_dec_ref_known(v___x_1827_, 1);
v___x_1831_ = lean_unbox(v_a_1830_);
lean_dec(v_a_1830_);
if (v___x_1831_ == 0)
{
v_a_1819_ = v_b_1812_;
goto v___jp_1818_;
}
else
{
goto v___jp_1825_;
}
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_dec_ref(v_b_1812_);
v_a_1832_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1827_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1827_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
v___jp_1825_:
{
lean_object* v___x_1826_; 
lean_inc(v___x_1824_);
v___x_1826_ = lean_array_push(v_b_1812_, v___x_1824_);
v_a_1819_ = v___x_1826_;
goto v___jp_1818_;
}
}
else
{
lean_object* v___x_1840_; 
v___x_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1840_, 0, v_b_1812_);
return v___x_1840_;
}
v___jp_1818_:
{
size_t v___x_1820_; size_t v___x_1821_; 
v___x_1820_ = ((size_t)1ULL);
v___x_1821_ = lean_usize_add(v_i_1810_, v___x_1820_);
v_i_1810_ = v___x_1821_;
v_b_1812_ = v_a_1819_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8___boxed(lean_object* v_as_1841_, lean_object* v_i_1842_, lean_object* v_stop_1843_, lean_object* v_b_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
size_t v_i_boxed_1850_; size_t v_stop_boxed_1851_; lean_object* v_res_1852_; 
v_i_boxed_1850_ = lean_unbox_usize(v_i_1842_);
lean_dec(v_i_1842_);
v_stop_boxed_1851_ = lean_unbox_usize(v_stop_1843_);
lean_dec(v_stop_1843_);
v_res_1852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v_as_1841_, v_i_boxed_1850_, v_stop_boxed_1851_, v_b_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec_ref(v_as_1841_);
return v_res_1852_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(lean_object* v_e_1853_){
_start:
{
if (lean_obj_tag(v_e_1853_) == 0)
{
uint8_t v___x_1854_; 
v___x_1854_ = 2;
return v___x_1854_;
}
else
{
uint8_t v___x_1855_; 
v___x_1855_ = 0;
return v___x_1855_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15___boxed(lean_object* v_e_1856_){
_start:
{
uint8_t v_res_1857_; lean_object* v_r_1858_; 
v_res_1857_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(v_e_1856_);
lean_dec_ref(v_e_1856_);
v_r_1858_ = lean_box(v_res_1857_);
return v_r_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(lean_object* v_opts_1859_, lean_object* v_opt_1860_){
_start:
{
lean_object* v_name_1861_; lean_object* v_defValue_1862_; lean_object* v_map_1863_; lean_object* v___x_1864_; 
v_name_1861_ = lean_ctor_get(v_opt_1860_, 0);
v_defValue_1862_ = lean_ctor_get(v_opt_1860_, 1);
v_map_1863_ = lean_ctor_get(v_opts_1859_, 0);
v___x_1864_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1863_, v_name_1861_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_inc(v_defValue_1862_);
return v_defValue_1862_;
}
else
{
lean_object* v_val_1865_; 
v_val_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_val_1865_);
lean_dec_ref_known(v___x_1864_, 1);
if (lean_obj_tag(v_val_1865_) == 3)
{
lean_object* v_v_1866_; 
v_v_1866_ = lean_ctor_get(v_val_1865_, 0);
lean_inc(v_v_1866_);
lean_dec_ref_known(v_val_1865_, 1);
return v_v_1866_;
}
else
{
lean_dec(v_val_1865_);
lean_inc(v_defValue_1862_);
return v_defValue_1862_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16___boxed(lean_object* v_opts_1867_, lean_object* v_opt_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_1867_, v_opt_1868_);
lean_dec_ref(v_opt_1868_);
lean_dec_ref(v_opts_1867_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(lean_object* v_x_1870_){
_start:
{
if (lean_obj_tag(v_x_1870_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
v_a_1872_ = lean_ctor_get(v_x_1870_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v_x_1870_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v_x_1870_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v_x_1870_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
lean_ctor_set_tag(v___x_1874_, 1);
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
v_a_1880_ = lean_ctor_get(v_x_1870_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v_x_1870_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v_x_1870_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v_x_1870_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
lean_ctor_set_tag(v___x_1882_, 0);
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg___boxed(lean_object* v_x_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(v_x_1888_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15(size_t v_sz_1891_, size_t v_i_1892_, lean_object* v_bs_1893_){
_start:
{
uint8_t v___x_1894_; 
v___x_1894_ = lean_usize_dec_lt(v_i_1892_, v_sz_1891_);
if (v___x_1894_ == 0)
{
return v_bs_1893_;
}
else
{
lean_object* v_v_1895_; lean_object* v_msg_1896_; lean_object* v___x_1897_; lean_object* v_bs_x27_1898_; size_t v___x_1899_; size_t v___x_1900_; lean_object* v___x_1901_; 
v_v_1895_ = lean_array_uget_borrowed(v_bs_1893_, v_i_1892_);
v_msg_1896_ = lean_ctor_get(v_v_1895_, 1);
lean_inc_ref(v_msg_1896_);
v___x_1897_ = lean_unsigned_to_nat(0u);
v_bs_x27_1898_ = lean_array_uset(v_bs_1893_, v_i_1892_, v___x_1897_);
v___x_1899_ = ((size_t)1ULL);
v___x_1900_ = lean_usize_add(v_i_1892_, v___x_1899_);
v___x_1901_ = lean_array_uset(v_bs_x27_1898_, v_i_1892_, v_msg_1896_);
v_i_1892_ = v___x_1900_;
v_bs_1893_ = v___x_1901_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15___boxed(lean_object* v_sz_1903_, lean_object* v_i_1904_, lean_object* v_bs_1905_){
_start:
{
size_t v_sz_boxed_1906_; size_t v_i_boxed_1907_; lean_object* v_res_1908_; 
v_sz_boxed_1906_ = lean_unbox_usize(v_sz_1903_);
lean_dec(v_sz_1903_);
v_i_boxed_1907_ = lean_unbox_usize(v_i_1904_);
lean_dec(v_i_1904_);
v_res_1908_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15(v_sz_boxed_1906_, v_i_boxed_1907_, v_bs_1905_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(lean_object* v_oldTraces_1909_, lean_object* v_data_1910_, lean_object* v_ref_1911_, lean_object* v_msg_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_fileName_1918_; lean_object* v_fileMap_1919_; lean_object* v_options_1920_; lean_object* v_currRecDepth_1921_; lean_object* v_maxRecDepth_1922_; lean_object* v_ref_1923_; lean_object* v_currNamespace_1924_; lean_object* v_openDecls_1925_; lean_object* v_initHeartbeats_1926_; lean_object* v_maxHeartbeats_1927_; lean_object* v_quotContext_1928_; lean_object* v_currMacroScope_1929_; uint8_t v_diag_1930_; lean_object* v_cancelTk_x3f_1931_; uint8_t v_suppressElabErrors_1932_; lean_object* v_inheritedTraceOptions_1933_; lean_object* v___x_1934_; lean_object* v_traceState_1935_; lean_object* v_traces_1936_; lean_object* v_ref_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; size_t v_sz_1940_; size_t v___x_1941_; lean_object* v___x_1942_; lean_object* v_msg_1943_; lean_object* v___x_1944_; lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1982_; 
v_fileName_1918_ = lean_ctor_get(v___y_1915_, 0);
v_fileMap_1919_ = lean_ctor_get(v___y_1915_, 1);
v_options_1920_ = lean_ctor_get(v___y_1915_, 2);
v_currRecDepth_1921_ = lean_ctor_get(v___y_1915_, 3);
v_maxRecDepth_1922_ = lean_ctor_get(v___y_1915_, 4);
v_ref_1923_ = lean_ctor_get(v___y_1915_, 5);
v_currNamespace_1924_ = lean_ctor_get(v___y_1915_, 6);
v_openDecls_1925_ = lean_ctor_get(v___y_1915_, 7);
v_initHeartbeats_1926_ = lean_ctor_get(v___y_1915_, 8);
v_maxHeartbeats_1927_ = lean_ctor_get(v___y_1915_, 9);
v_quotContext_1928_ = lean_ctor_get(v___y_1915_, 10);
v_currMacroScope_1929_ = lean_ctor_get(v___y_1915_, 11);
v_diag_1930_ = lean_ctor_get_uint8(v___y_1915_, sizeof(void*)*14);
v_cancelTk_x3f_1931_ = lean_ctor_get(v___y_1915_, 12);
v_suppressElabErrors_1932_ = lean_ctor_get_uint8(v___y_1915_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1933_ = lean_ctor_get(v___y_1915_, 13);
v___x_1934_ = lean_st_ref_get(v___y_1916_);
v_traceState_1935_ = lean_ctor_get(v___x_1934_, 4);
lean_inc_ref(v_traceState_1935_);
lean_dec(v___x_1934_);
v_traces_1936_ = lean_ctor_get(v_traceState_1935_, 0);
lean_inc_ref(v_traces_1936_);
lean_dec_ref(v_traceState_1935_);
v_ref_1937_ = l_Lean_replaceRef(v_ref_1911_, v_ref_1923_);
lean_inc_ref(v_inheritedTraceOptions_1933_);
lean_inc(v_cancelTk_x3f_1931_);
lean_inc(v_currMacroScope_1929_);
lean_inc(v_quotContext_1928_);
lean_inc(v_maxHeartbeats_1927_);
lean_inc(v_initHeartbeats_1926_);
lean_inc(v_openDecls_1925_);
lean_inc(v_currNamespace_1924_);
lean_inc(v_maxRecDepth_1922_);
lean_inc(v_currRecDepth_1921_);
lean_inc_ref(v_options_1920_);
lean_inc_ref(v_fileMap_1919_);
lean_inc_ref(v_fileName_1918_);
v___x_1938_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1938_, 0, v_fileName_1918_);
lean_ctor_set(v___x_1938_, 1, v_fileMap_1919_);
lean_ctor_set(v___x_1938_, 2, v_options_1920_);
lean_ctor_set(v___x_1938_, 3, v_currRecDepth_1921_);
lean_ctor_set(v___x_1938_, 4, v_maxRecDepth_1922_);
lean_ctor_set(v___x_1938_, 5, v_ref_1937_);
lean_ctor_set(v___x_1938_, 6, v_currNamespace_1924_);
lean_ctor_set(v___x_1938_, 7, v_openDecls_1925_);
lean_ctor_set(v___x_1938_, 8, v_initHeartbeats_1926_);
lean_ctor_set(v___x_1938_, 9, v_maxHeartbeats_1927_);
lean_ctor_set(v___x_1938_, 10, v_quotContext_1928_);
lean_ctor_set(v___x_1938_, 11, v_currMacroScope_1929_);
lean_ctor_set(v___x_1938_, 12, v_cancelTk_x3f_1931_);
lean_ctor_set(v___x_1938_, 13, v_inheritedTraceOptions_1933_);
lean_ctor_set_uint8(v___x_1938_, sizeof(void*)*14, v_diag_1930_);
lean_ctor_set_uint8(v___x_1938_, sizeof(void*)*14 + 1, v_suppressElabErrors_1932_);
v___x_1939_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1936_);
lean_dec_ref(v_traces_1936_);
v_sz_1940_ = lean_array_size(v___x_1939_);
v___x_1941_ = ((size_t)0ULL);
v___x_1942_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13_spec__15(v_sz_1940_, v___x_1941_, v___x_1939_);
v_msg_1943_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1943_, 0, v_data_1910_);
lean_ctor_set(v_msg_1943_, 1, v_msg_1912_);
lean_ctor_set(v_msg_1943_, 2, v___x_1942_);
v___x_1944_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2_spec__3(v_msg_1943_, v___y_1913_, v___y_1914_, v___x_1938_, v___y_1916_);
lean_dec_ref_known(v___x_1938_, 14);
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1947_ = v___x_1944_;
v_isShared_1948_ = v_isSharedCheck_1982_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1944_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1982_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1949_; lean_object* v_traceState_1950_; lean_object* v_env_1951_; lean_object* v_nextMacroScope_1952_; lean_object* v_ngen_1953_; lean_object* v_auxDeclNGen_1954_; lean_object* v_cache_1955_; lean_object* v_messages_1956_; lean_object* v_infoState_1957_; lean_object* v_snapshotTasks_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1981_; 
v___x_1949_ = lean_st_ref_take(v___y_1916_);
v_traceState_1950_ = lean_ctor_get(v___x_1949_, 4);
v_env_1951_ = lean_ctor_get(v___x_1949_, 0);
v_nextMacroScope_1952_ = lean_ctor_get(v___x_1949_, 1);
v_ngen_1953_ = lean_ctor_get(v___x_1949_, 2);
v_auxDeclNGen_1954_ = lean_ctor_get(v___x_1949_, 3);
v_cache_1955_ = lean_ctor_get(v___x_1949_, 5);
v_messages_1956_ = lean_ctor_get(v___x_1949_, 6);
v_infoState_1957_ = lean_ctor_get(v___x_1949_, 7);
v_snapshotTasks_1958_ = lean_ctor_get(v___x_1949_, 8);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1960_ = v___x_1949_;
v_isShared_1961_ = v_isSharedCheck_1981_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_snapshotTasks_1958_);
lean_inc(v_infoState_1957_);
lean_inc(v_messages_1956_);
lean_inc(v_cache_1955_);
lean_inc(v_traceState_1950_);
lean_inc(v_auxDeclNGen_1954_);
lean_inc(v_ngen_1953_);
lean_inc(v_nextMacroScope_1952_);
lean_inc(v_env_1951_);
lean_dec(v___x_1949_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1981_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
uint64_t v_tid_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1979_; 
v_tid_1962_ = lean_ctor_get_uint64(v_traceState_1950_, sizeof(void*)*1);
v_isSharedCheck_1979_ = !lean_is_exclusive(v_traceState_1950_);
if (v_isSharedCheck_1979_ == 0)
{
lean_object* v_unused_1980_; 
v_unused_1980_ = lean_ctor_get(v_traceState_1950_, 0);
lean_dec(v_unused_1980_);
v___x_1964_ = v_traceState_1950_;
v_isShared_1965_ = v_isSharedCheck_1979_;
goto v_resetjp_1963_;
}
else
{
lean_dec(v_traceState_1950_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1979_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1969_; 
v___x_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1966_, 0, v_ref_1911_);
lean_ctor_set(v___x_1966_, 1, v_a_1945_);
v___x_1967_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1909_, v___x_1966_);
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 0, v___x_1967_);
v___x_1969_ = v___x_1964_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1967_);
lean_ctor_set_uint64(v_reuseFailAlloc_1978_, sizeof(void*)*1, v_tid_1962_);
v___x_1969_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1971_; 
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 4, v___x_1969_);
v___x_1971_ = v___x_1960_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_env_1951_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_nextMacroScope_1952_);
lean_ctor_set(v_reuseFailAlloc_1977_, 2, v_ngen_1953_);
lean_ctor_set(v_reuseFailAlloc_1977_, 3, v_auxDeclNGen_1954_);
lean_ctor_set(v_reuseFailAlloc_1977_, 4, v___x_1969_);
lean_ctor_set(v_reuseFailAlloc_1977_, 5, v_cache_1955_);
lean_ctor_set(v_reuseFailAlloc_1977_, 6, v_messages_1956_);
lean_ctor_set(v_reuseFailAlloc_1977_, 7, v_infoState_1957_);
lean_ctor_set(v_reuseFailAlloc_1977_, 8, v_snapshotTasks_1958_);
v___x_1971_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1975_; 
v___x_1972_ = lean_st_ref_set(v___y_1916_, v___x_1971_);
v___x_1973_ = lean_box(0);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 0, v___x_1973_);
v___x_1975_ = v___x_1947_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___x_1973_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13___boxed(lean_object* v_oldTraces_1983_, lean_object* v_data_1984_, lean_object* v_ref_1985_, lean_object* v_msg_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(v_oldTraces_1983_, v_data_1984_, v_ref_1985_, v_msg_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
return v_res_1992_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1(void){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1994_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__0));
v___x_1995_ = l_Lean_stringToMessageData(v___x_1994_);
return v___x_1995_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2(void){
_start:
{
lean_object* v___x_1996_; double v___x_1997_; 
v___x_1996_ = lean_unsigned_to_nat(1000u);
v___x_1997_ = lean_float_of_nat(v___x_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(lean_object* v_cls_1998_, uint8_t v_collapsed_1999_, lean_object* v_tag_2000_, lean_object* v_opts_2001_, uint8_t v_clsEnabled_2002_, lean_object* v_oldTraces_2003_, lean_object* v_msg_2004_, lean_object* v_resStartStop_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v_fst_2011_; lean_object* v_snd_2012_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v_data_2016_; lean_object* v_fst_2027_; lean_object* v_snd_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; lean_object* v___y_2032_; lean_object* v_a_2033_; uint8_t v___y_2048_; double v___y_2079_; 
v_fst_2011_ = lean_ctor_get(v_resStartStop_2005_, 0);
lean_inc(v_fst_2011_);
v_snd_2012_ = lean_ctor_get(v_resStartStop_2005_, 1);
lean_inc(v_snd_2012_);
lean_dec_ref(v_resStartStop_2005_);
v_fst_2027_ = lean_ctor_get(v_snd_2012_, 0);
lean_inc(v_fst_2027_);
v_snd_2028_ = lean_ctor_get(v_snd_2012_, 1);
lean_inc(v_snd_2028_);
lean_dec(v_snd_2012_);
v___x_2029_ = l_Lean_trace_profiler;
v___x_2030_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_opts_2001_, v___x_2029_);
if (v___x_2030_ == 0)
{
v___y_2048_ = v___x_2030_;
goto v___jp_2047_;
}
else
{
lean_object* v___x_2084_; uint8_t v___x_2085_; 
v___x_2084_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2085_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_opts_2001_, v___x_2084_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; lean_object* v___x_2087_; double v___x_2088_; double v___x_2089_; double v___x_2090_; 
v___x_2086_ = l_Lean_trace_profiler_threshold;
v___x_2087_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_2001_, v___x_2086_);
v___x_2088_ = lean_float_of_nat(v___x_2087_);
v___x_2089_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__2);
v___x_2090_ = lean_float_div(v___x_2088_, v___x_2089_);
v___y_2079_ = v___x_2090_;
goto v___jp_2078_;
}
else
{
lean_object* v___x_2091_; lean_object* v___x_2092_; double v___x_2093_; 
v___x_2091_ = l_Lean_trace_profiler_threshold;
v___x_2092_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__16(v_opts_2001_, v___x_2091_);
v___x_2093_ = lean_float_of_nat(v___x_2092_);
v___y_2079_ = v___x_2093_;
goto v___jp_2078_;
}
}
v___jp_2013_:
{
lean_object* v___x_2017_; 
lean_inc(v___y_2015_);
v___x_2017_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__13(v_oldTraces_2003_, v_data_2016_, v___y_2015_, v___y_2014_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v___x_2018_; 
lean_dec_ref_known(v___x_2017_, 1);
v___x_2018_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(v_fst_2011_);
return v___x_2018_;
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
lean_dec(v_fst_2011_);
v_a_2019_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_2017_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_2017_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
v___jp_2031_:
{
uint8_t v_result_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; double v___x_2037_; lean_object* v_data_2038_; 
v_result_2034_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__15(v_fst_2011_);
v___x_2035_ = lean_box(v_result_2034_);
v___x_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
v___x_2037_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__0);
lean_inc_ref(v_tag_2000_);
lean_inc_ref(v___x_2036_);
lean_inc(v_cls_1998_);
v_data_2038_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2038_, 0, v_cls_1998_);
lean_ctor_set(v_data_2038_, 1, v___x_2036_);
lean_ctor_set(v_data_2038_, 2, v_tag_2000_);
lean_ctor_set_float(v_data_2038_, sizeof(void*)*3, v___x_2037_);
lean_ctor_set_float(v_data_2038_, sizeof(void*)*3 + 8, v___x_2037_);
lean_ctor_set_uint8(v_data_2038_, sizeof(void*)*3 + 16, v_collapsed_1999_);
if (v___x_2030_ == 0)
{
lean_dec_ref_known(v___x_2036_, 1);
lean_dec(v_snd_2028_);
lean_dec(v_fst_2027_);
lean_dec_ref(v_tag_2000_);
lean_dec(v_cls_1998_);
v___y_2014_ = v_a_2033_;
v___y_2015_ = v___y_2032_;
v_data_2016_ = v_data_2038_;
goto v___jp_2013_;
}
else
{
lean_object* v_data_2039_; double v___x_2040_; double v___x_2041_; 
lean_dec_ref_known(v_data_2038_, 3);
v_data_2039_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2039_, 0, v_cls_1998_);
lean_ctor_set(v_data_2039_, 1, v___x_2036_);
lean_ctor_set(v_data_2039_, 2, v_tag_2000_);
v___x_2040_ = lean_unbox_float(v_fst_2027_);
lean_dec(v_fst_2027_);
lean_ctor_set_float(v_data_2039_, sizeof(void*)*3, v___x_2040_);
v___x_2041_ = lean_unbox_float(v_snd_2028_);
lean_dec(v_snd_2028_);
lean_ctor_set_float(v_data_2039_, sizeof(void*)*3 + 8, v___x_2041_);
lean_ctor_set_uint8(v_data_2039_, sizeof(void*)*3 + 16, v_collapsed_1999_);
v___y_2014_ = v_a_2033_;
v___y_2015_ = v___y_2032_;
v_data_2016_ = v_data_2039_;
goto v___jp_2013_;
}
}
v___jp_2042_:
{
lean_object* v_ref_2043_; lean_object* v___x_2044_; 
v_ref_2043_ = lean_ctor_get(v___y_2008_, 5);
lean_inc(v___y_2009_);
lean_inc_ref(v___y_2008_);
lean_inc(v___y_2007_);
lean_inc_ref(v___y_2006_);
lean_inc(v_fst_2011_);
v___x_2044_ = lean_apply_6(v_msg_2004_, v_fst_2011_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, lean_box(0));
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2045_);
lean_dec_ref_known(v___x_2044_, 1);
v___y_2032_ = v_ref_2043_;
v_a_2033_ = v_a_2045_;
goto v___jp_2031_;
}
else
{
lean_object* v___x_2046_; 
lean_dec_ref_known(v___x_2044_, 1);
v___x_2046_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___closed__1);
v___y_2032_ = v_ref_2043_;
v_a_2033_ = v___x_2046_;
goto v___jp_2031_;
}
}
v___jp_2047_:
{
if (v_clsEnabled_2002_ == 0)
{
if (v___y_2048_ == 0)
{
lean_object* v___x_2049_; lean_object* v_traceState_2050_; lean_object* v_env_2051_; lean_object* v_nextMacroScope_2052_; lean_object* v_ngen_2053_; lean_object* v_auxDeclNGen_2054_; lean_object* v_cache_2055_; lean_object* v_messages_2056_; lean_object* v_infoState_2057_; lean_object* v_snapshotTasks_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2077_; 
lean_dec(v_snd_2028_);
lean_dec(v_fst_2027_);
lean_dec_ref(v_msg_2004_);
lean_dec_ref(v_tag_2000_);
lean_dec(v_cls_1998_);
v___x_2049_ = lean_st_ref_take(v___y_2009_);
v_traceState_2050_ = lean_ctor_get(v___x_2049_, 4);
v_env_2051_ = lean_ctor_get(v___x_2049_, 0);
v_nextMacroScope_2052_ = lean_ctor_get(v___x_2049_, 1);
v_ngen_2053_ = lean_ctor_get(v___x_2049_, 2);
v_auxDeclNGen_2054_ = lean_ctor_get(v___x_2049_, 3);
v_cache_2055_ = lean_ctor_get(v___x_2049_, 5);
v_messages_2056_ = lean_ctor_get(v___x_2049_, 6);
v_infoState_2057_ = lean_ctor_get(v___x_2049_, 7);
v_snapshotTasks_2058_ = lean_ctor_get(v___x_2049_, 8);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2060_ = v___x_2049_;
v_isShared_2061_ = v_isSharedCheck_2077_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_snapshotTasks_2058_);
lean_inc(v_infoState_2057_);
lean_inc(v_messages_2056_);
lean_inc(v_cache_2055_);
lean_inc(v_traceState_2050_);
lean_inc(v_auxDeclNGen_2054_);
lean_inc(v_ngen_2053_);
lean_inc(v_nextMacroScope_2052_);
lean_inc(v_env_2051_);
lean_dec(v___x_2049_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2077_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
uint64_t v_tid_2062_; lean_object* v_traces_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2076_; 
v_tid_2062_ = lean_ctor_get_uint64(v_traceState_2050_, sizeof(void*)*1);
v_traces_2063_ = lean_ctor_get(v_traceState_2050_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_traceState_2050_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2065_ = v_traceState_2050_;
v_isShared_2066_ = v_isSharedCheck_2076_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_traces_2063_);
lean_dec(v_traceState_2050_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2076_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2067_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2003_, v_traces_2063_);
lean_dec_ref(v_traces_2063_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v___x_2067_);
v___x_2069_ = v___x_2065_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2067_);
lean_ctor_set_uint64(v_reuseFailAlloc_2075_, sizeof(void*)*1, v_tid_2062_);
v___x_2069_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2071_; 
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 4, v___x_2069_);
v___x_2071_ = v___x_2060_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_env_2051_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_nextMacroScope_2052_);
lean_ctor_set(v_reuseFailAlloc_2074_, 2, v_ngen_2053_);
lean_ctor_set(v_reuseFailAlloc_2074_, 3, v_auxDeclNGen_2054_);
lean_ctor_set(v_reuseFailAlloc_2074_, 4, v___x_2069_);
lean_ctor_set(v_reuseFailAlloc_2074_, 5, v_cache_2055_);
lean_ctor_set(v_reuseFailAlloc_2074_, 6, v_messages_2056_);
lean_ctor_set(v_reuseFailAlloc_2074_, 7, v_infoState_2057_);
lean_ctor_set(v_reuseFailAlloc_2074_, 8, v_snapshotTasks_2058_);
v___x_2071_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = lean_st_ref_set(v___y_2009_, v___x_2071_);
v___x_2073_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(v_fst_2011_);
return v___x_2073_;
}
}
}
}
}
else
{
goto v___jp_2042_;
}
}
else
{
goto v___jp_2042_;
}
}
v___jp_2078_:
{
double v___x_2080_; double v___x_2081_; double v___x_2082_; uint8_t v___x_2083_; 
v___x_2080_ = lean_unbox_float(v_snd_2028_);
v___x_2081_ = lean_unbox_float(v_fst_2027_);
v___x_2082_ = lean_float_sub(v___x_2080_, v___x_2081_);
v___x_2083_ = lean_float_decLt(v___y_2079_, v___x_2082_);
v___y_2048_ = v___x_2083_;
goto v___jp_2047_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11___boxed(lean_object* v_cls_2094_, lean_object* v_collapsed_2095_, lean_object* v_tag_2096_, lean_object* v_opts_2097_, lean_object* v_clsEnabled_2098_, lean_object* v_oldTraces_2099_, lean_object* v_msg_2100_, lean_object* v_resStartStop_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
uint8_t v_collapsed_boxed_2107_; uint8_t v_clsEnabled_boxed_2108_; lean_object* v_res_2109_; 
v_collapsed_boxed_2107_ = lean_unbox(v_collapsed_2095_);
v_clsEnabled_boxed_2108_ = lean_unbox(v_clsEnabled_2098_);
v_res_2109_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v_cls_2094_, v_collapsed_boxed_2107_, v_tag_2096_, v_opts_2097_, v_clsEnabled_boxed_2108_, v_oldTraces_2099_, v_msg_2100_, v_resStartStop_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec_ref(v_opts_2097_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__14___redArg(lean_object* v_a_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
lean_object* v___x_2116_; 
v___x_2116_ = l_Lean_Meta_reduceRecMatcher_x3f(v_a_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2130_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2119_ = v___x_2116_;
v_isShared_2120_ = v_isSharedCheck_2130_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2116_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2130_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
if (lean_obj_tag(v_a_2117_) == 1)
{
lean_object* v_val_2121_; lean_object* v___x_2122_; 
lean_del_object(v___x_2119_);
lean_dec_ref(v_a_2110_);
v_val_2121_ = lean_ctor_get(v_a_2117_, 0);
lean_inc(v_val_2121_);
lean_dec_ref_known(v_a_2117_, 1);
v___x_2122_ = l_Lean_Expr_headBeta(v_val_2121_);
v_a_2110_ = v___x_2122_;
goto _start;
}
else
{
lean_object* v___x_2124_; uint8_t v___x_2125_; 
lean_dec(v_a_2117_);
lean_inc_ref(v_a_2110_);
v___x_2124_ = l_Lean_Expr_headBeta(v_a_2110_);
v___x_2125_ = lean_expr_eqv(v_a_2110_, v___x_2124_);
if (v___x_2125_ == 0)
{
lean_del_object(v___x_2119_);
lean_dec_ref(v_a_2110_);
v_a_2110_ = v___x_2124_;
goto _start;
}
else
{
lean_object* v___x_2128_; 
lean_dec_ref(v___x_2124_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 0, v_a_2110_);
v___x_2128_ = v___x_2119_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2110_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
}
else
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
lean_dec_ref(v_a_2110_);
v_a_2131_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___x_2116_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2116_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__14___redArg___boxed(lean_object* v_a_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__14___redArg(v_a_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
return v_res_2145_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__3(void){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2150_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__2));
v___x_2151_ = l_Lean_stringToMessageData(v___x_2150_);
return v___x_2151_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__5(void){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__4));
v___x_2154_ = l_Lean_stringToMessageData(v___x_2153_);
return v___x_2154_;
}
}
static double _init_l_Lean_Meta_rwMatcher___closed__6(void){
_start:
{
lean_object* v___x_2155_; double v___x_2156_; 
v___x_2155_ = lean_unsigned_to_nat(1000000000u);
v___x_2156_ = lean_float_of_nat(v___x_2155_);
return v___x_2156_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__8(void){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__7));
v___x_2159_ = l_Lean_stringToMessageData(v___x_2158_);
return v___x_2159_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__13(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2167_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2168_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
v___x_2169_ = l_Lean_Name_append(v___x_2168_, v___x_2167_);
return v___x_2169_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__15(void){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__14));
v___x_2172_ = l_Lean_stringToMessageData(v___x_2171_);
return v___x_2172_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__17(void){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__16));
v___x_2175_ = l_Lean_stringToMessageData(v___x_2174_);
return v___x_2175_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__19(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2177_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__18));
v___x_2178_ = l_Lean_stringToMessageData(v___x_2177_);
return v___x_2178_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__21(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__20));
v___x_2181_ = l_Lean_stringToMessageData(v___x_2180_);
return v___x_2181_;
}
}
static lean_object* _init_l_Lean_Meta_rwMatcher___closed__22(void){
_start:
{
lean_object* v___x_2182_; lean_object* v_dummy_2183_; 
v___x_2182_ = lean_box(0);
v_dummy_2183_ = l_Lean_Expr_sort___override(v___x_2182_);
return v_dummy_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher(lean_object* v_altIdx_2193_, lean_object* v_e_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_){
_start:
{
lean_object* v___y_2201_; uint8_t v___y_2220_; uint8_t v___y_2225_; lean_object* v___y_2230_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; uint8_t v___y_2238_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v_a_2269_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; uint8_t v___y_2279_; lean_object* v___y_2280_; lean_object* v_proof_2281_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; uint8_t v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2295_; uint8_t v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v___y_2305_; lean_object* v___y_2306_; uint8_t v___y_2307_; lean_object* v___y_2320_; lean_object* v___y_2321_; uint8_t v___y_2322_; lean_object* v___y_2323_; uint8_t v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2329_; lean_object* v___y_2330_; lean_object* v___y_2341_; uint8_t v___y_2342_; lean_object* v___y_2343_; uint8_t v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; uint8_t v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v_a_2353_; lean_object* v___y_2370_; uint8_t v___y_2371_; lean_object* v___y_2372_; uint8_t v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; uint8_t v___y_2377_; lean_object* v___y_2378_; lean_object* v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2386_; size_t v___y_2387_; uint8_t v___y_2388_; lean_object* v___y_2389_; uint8_t v___y_2390_; lean_object* v___y_2391_; uint8_t v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2414_; uint8_t v___y_2415_; size_t v___y_2416_; uint8_t v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; uint8_t v_fst_2422_; lean_object* v_fst_2423_; lean_object* v_snd_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; uint8_t v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; uint8_t v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v_a_2459_; lean_object* v___y_2469_; uint8_t v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; uint8_t v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v_a_2479_; lean_object* v___y_2482_; uint8_t v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2488_; uint8_t v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; uint8_t v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; uint8_t v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v_a_2513_; lean_object* v___y_2526_; uint8_t v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; uint8_t v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v_a_2536_; lean_object* v___y_2539_; uint8_t v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; uint8_t v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; uint8_t v___y_2560_; lean_object* v___y_2561_; uint8_t v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___y_2566_; uint8_t v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; uint8_t v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; uint8_t v___y_2639_; lean_object* v___x_2830_; uint8_t v___x_2831_; 
v___x_2830_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__25));
v___x_2831_ = l_Lean_Expr_isAppOf(v_e_2194_, v___x_2830_);
if (v___x_2831_ == 0)
{
lean_object* v___x_2832_; uint8_t v___x_2833_; 
v___x_2832_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__27));
v___x_2833_ = l_Lean_Expr_isAppOf(v_e_2194_, v___x_2832_);
v___y_2639_ = v___x_2833_;
goto v___jp_2638_;
}
else
{
v___y_2639_ = v___x_2831_;
goto v___jp_2638_;
}
v___jp_2200_:
{
if (lean_obj_tag(v___y_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2210_; 
v_a_2202_ = lean_ctor_get(v___y_2201_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___y_2201_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2204_ = v___y_2201_;
v_isShared_2205_ = v_isSharedCheck_2210_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___y_2201_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2210_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v_a_2206_; lean_object* v___x_2208_; 
v_a_2206_ = lean_ctor_get(v_a_2202_, 0);
lean_inc(v_a_2206_);
lean_dec(v_a_2202_);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v_a_2206_);
v___x_2208_ = v___x_2204_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2206_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
v_a_2211_ = lean_ctor_get(v___y_2201_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___y_2201_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___y_2201_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___y_2201_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
v___jp_2219_:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2221_ = lean_box(0);
v___x_2222_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2222_, 0, v_e_2194_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
lean_ctor_set_uint8(v___x_2222_, sizeof(void*)*2, v___y_2220_);
v___x_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
return v___x_2223_;
}
v___jp_2224_:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2226_ = lean_box(0);
v___x_2227_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2227_, 0, v_e_2194_);
lean_ctor_set(v___x_2227_, 1, v___x_2226_);
lean_ctor_set_uint8(v___x_2227_, sizeof(void*)*2, v___y_2225_);
v___x_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
return v___x_2228_;
}
v___jp_2229_:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2231_ = lean_box(0);
lean_inc(v_a_2198_);
lean_inc_ref(v_a_2197_);
lean_inc(v_a_2196_);
lean_inc_ref(v_a_2195_);
v___x_2232_ = lean_apply_6(v___y_2230_, v___x_2231_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, lean_box(0));
v___y_2201_ = v___x_2232_;
goto v___jp_2200_;
}
v___jp_2233_:
{
if (v___y_2238_ == 0)
{
lean_object* v_options_2239_; uint8_t v_hasTrace_2240_; 
v_options_2239_ = lean_ctor_get(v_a_2197_, 2);
v_hasTrace_2240_ = lean_ctor_get_uint8(v_options_2239_, sizeof(void*)*1);
if (v_hasTrace_2240_ == 0)
{
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
v___y_2230_ = v___y_2237_;
goto v___jp_2229_;
}
else
{
lean_object* v_inheritedTraceOptions_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; uint8_t v___x_2244_; 
v_inheritedTraceOptions_2241_ = lean_ctor_get(v_a_2197_, 13);
v___x_2242_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2234_);
v___x_2243_ = l_Lean_Name_append(v___x_2242_, v___y_2234_);
v___x_2244_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2241_, v_options_2239_, v___x_2243_);
lean_dec(v___x_2243_);
if (v___x_2244_ == 0)
{
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
v___y_2230_ = v___y_2237_;
goto v___jp_2229_;
}
else
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2245_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__3, &l_Lean_Meta_rwMatcher___closed__3_once, _init_l_Lean_Meta_rwMatcher___closed__3);
v___x_2246_ = l_Lean_MessageData_ofConstName(v___y_2236_, v___y_2238_);
v___x_2247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2245_);
lean_ctor_set(v___x_2247_, 1, v___x_2246_);
v___x_2248_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__5, &l_Lean_Meta_rwMatcher___closed__5_once, _init_l_Lean_Meta_rwMatcher___closed__5);
v___x_2249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2247_);
lean_ctor_set(v___x_2249_, 1, v___x_2248_);
v___x_2250_ = l_Lean_Exception_toMessageData(v___y_2235_);
v___x_2251_ = l_Lean_indentD(v___x_2250_);
v___x_2252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2249_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
v___x_2253_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2234_, v___x_2252_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; lean_object* v___x_2255_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_a_2254_);
lean_dec_ref_known(v___x_2253_, 1);
lean_inc(v_a_2198_);
lean_inc_ref(v_a_2197_);
lean_inc(v_a_2196_);
lean_inc_ref(v_a_2195_);
v___x_2255_ = lean_apply_6(v___y_2237_, v_a_2254_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, lean_box(0));
v___y_2201_ = v___x_2255_;
goto v___jp_2200_;
}
else
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
lean_dec_ref(v___y_2237_);
v_a_2256_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v___x_2253_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2253_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2256_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
}
}
else
{
lean_object* v___x_2264_; 
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec(v___y_2234_);
v___x_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2264_, 0, v___y_2235_);
return v___x_2264_;
}
}
v___jp_2265_:
{
uint8_t v___x_2270_; 
v___x_2270_ = l_Lean_Exception_isInterrupt(v_a_2269_);
if (v___x_2270_ == 0)
{
uint8_t v___x_2271_; 
lean_inc_ref(v_a_2269_);
v___x_2271_ = l_Lean_Exception_isRuntime(v_a_2269_);
v___y_2234_ = v___y_2266_;
v___y_2235_ = v_a_2269_;
v___y_2236_ = v___y_2267_;
v___y_2237_ = v___y_2268_;
v___y_2238_ = v___x_2271_;
goto v___jp_2233_;
}
else
{
v___y_2234_ = v___y_2266_;
v___y_2235_ = v_a_2269_;
v___y_2236_ = v___y_2267_;
v___y_2237_ = v___y_2268_;
v___y_2238_ = v___x_2270_;
goto v___jp_2233_;
}
}
v___jp_2272_:
{
if (lean_obj_tag(v___y_2276_) == 0)
{
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec(v___y_2273_);
return v___y_2276_;
}
else
{
lean_object* v_a_2277_; 
v_a_2277_ = lean_ctor_get(v___y_2276_, 0);
lean_inc(v_a_2277_);
lean_dec_ref_known(v___y_2276_, 1);
v___y_2266_ = v___y_2273_;
v___y_2267_ = v___y_2274_;
v___y_2268_ = v___y_2275_;
v_a_2269_ = v_a_2277_;
goto v___jp_2265_;
}
}
v___jp_2278_:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2282_, 0, v_proof_2281_);
v___x_2283_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2283_, 0, v___y_2280_);
lean_ctor_set(v___x_2283_, 1, v___x_2282_);
lean_ctor_set_uint8(v___x_2283_, sizeof(void*)*2, v___y_2279_);
v___x_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
return v___x_2284_;
}
v___jp_2285_:
{
if (lean_obj_tag(v___y_2291_) == 0)
{
lean_object* v_a_2292_; 
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2287_);
lean_dec(v___y_2286_);
v_a_2292_ = lean_ctor_get(v___y_2291_, 0);
lean_inc(v_a_2292_);
lean_dec_ref_known(v___y_2291_, 1);
v___y_2279_ = v___y_2289_;
v___y_2280_ = v___y_2288_;
v_proof_2281_ = v_a_2292_;
goto v___jp_2278_;
}
else
{
lean_object* v_a_2293_; 
lean_dec_ref(v___y_2288_);
v_a_2293_ = lean_ctor_get(v___y_2291_, 0);
lean_inc(v_a_2293_);
lean_dec_ref_known(v___y_2291_, 1);
v___y_2266_ = v___y_2286_;
v___y_2267_ = v___y_2287_;
v___y_2268_ = v___y_2290_;
v_a_2269_ = v_a_2293_;
goto v___jp_2265_;
}
}
v___jp_2294_:
{
if (v___y_2307_ == 0)
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
lean_dec_ref(v___y_2298_);
v___x_2308_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__1, &l_Lean_Meta_rwMatcher___lam__2___closed__1_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__1);
v___x_2309_ = l_Lean_MessageData_ofExpr(v___y_2302_);
v___x_2310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2308_);
lean_ctor_set(v___x_2310_, 1, v___x_2309_);
v___x_2311_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__3, &l_Lean_Meta_rwMatcher___lam__2___closed__3_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__3);
v___x_2312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2310_);
lean_ctor_set(v___x_2312_, 1, v___x_2311_);
v___x_2313_ = l_Lean_Exception_toMessageData(v___y_2304_);
v___x_2314_ = l_Lean_indentD(v___x_2313_);
v___x_2315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2312_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___x_2316_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__5, &l_Lean_Meta_rwMatcher___lam__2___closed__5_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__5);
v___x_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2315_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2317_, v___y_2305_, v___y_2303_, v___y_2297_, v___y_2299_);
v___y_2286_ = v___y_2300_;
v___y_2287_ = v___y_2295_;
v___y_2288_ = v___y_2301_;
v___y_2289_ = v___y_2296_;
v___y_2290_ = v___y_2306_;
v___y_2291_ = v___x_2318_;
goto v___jp_2285_;
}
else
{
lean_dec_ref(v___y_2304_);
lean_dec_ref(v___y_2302_);
v___y_2286_ = v___y_2300_;
v___y_2287_ = v___y_2295_;
v___y_2288_ = v___y_2301_;
v___y_2289_ = v___y_2296_;
v___y_2290_ = v___y_2306_;
v___y_2291_ = v___y_2298_;
goto v___jp_2285_;
}
}
v___jp_2319_:
{
lean_object* v___x_2331_; lean_object* v_a_2332_; lean_object* v___x_2333_; 
v___x_2331_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_2323_, v___y_2328_);
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2332_);
lean_dec_ref(v___x_2331_);
v___x_2333_ = l_Lean_instantiateMVars___at___00Lean_Meta_rwMatcher_spec__4___redArg(v___y_2325_, v___y_2328_);
if (v___y_2324_ == 0)
{
lean_object* v_a_2334_; 
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2321_);
lean_dec(v___y_2320_);
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_a_2334_);
lean_dec_ref(v___x_2333_);
v___y_2279_ = v___y_2322_;
v___y_2280_ = v_a_2332_;
v_proof_2281_ = v_a_2334_;
goto v___jp_2278_;
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2336_; 
v_a_2335_ = lean_ctor_get(v___x_2333_, 0);
lean_inc_n(v_a_2335_, 2);
lean_dec_ref(v___x_2333_);
v___x_2336_ = l_Lean_Meta_mkEqOfHEq(v_a_2335_, v___y_2322_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_dec(v_a_2335_);
v___y_2286_ = v___y_2320_;
v___y_2287_ = v___y_2321_;
v___y_2288_ = v_a_2332_;
v___y_2289_ = v___y_2322_;
v___y_2290_ = v___y_2326_;
v___y_2291_ = v___x_2336_;
goto v___jp_2285_;
}
else
{
lean_object* v_a_2337_; uint8_t v___x_2338_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
v___x_2338_ = l_Lean_Exception_isInterrupt(v_a_2337_);
if (v___x_2338_ == 0)
{
uint8_t v___x_2339_; 
lean_inc(v_a_2337_);
v___x_2339_ = l_Lean_Exception_isRuntime(v_a_2337_);
v___y_2295_ = v___y_2321_;
v___y_2296_ = v___y_2322_;
v___y_2297_ = v___y_2329_;
v___y_2298_ = v___x_2336_;
v___y_2299_ = v___y_2330_;
v___y_2300_ = v___y_2320_;
v___y_2301_ = v_a_2332_;
v___y_2302_ = v_a_2335_;
v___y_2303_ = v___y_2328_;
v___y_2304_ = v_a_2337_;
v___y_2305_ = v___y_2327_;
v___y_2306_ = v___y_2326_;
v___y_2307_ = v___x_2339_;
goto v___jp_2294_;
}
else
{
v___y_2295_ = v___y_2321_;
v___y_2296_ = v___y_2322_;
v___y_2297_ = v___y_2329_;
v___y_2298_ = v___x_2336_;
v___y_2299_ = v___y_2330_;
v___y_2300_ = v___y_2320_;
v___y_2301_ = v_a_2332_;
v___y_2302_ = v_a_2335_;
v___y_2303_ = v___y_2328_;
v___y_2304_ = v_a_2337_;
v___y_2305_ = v___y_2327_;
v___y_2306_ = v___y_2326_;
v___y_2307_ = v___x_2338_;
goto v___jp_2294_;
}
}
}
}
v___jp_2340_:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; uint8_t v___x_2356_; 
v___x_2354_ = lean_array_get_size(v_a_2353_);
v___x_2355_ = lean_unsigned_to_nat(0u);
v___x_2356_ = lean_nat_dec_eq(v___x_2354_, v___x_2355_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v_a_2368_; 
lean_dec_ref(v___y_2350_);
lean_dec_ref(v___y_2343_);
v___x_2357_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__7, &l_Lean_Meta_rwMatcher___lam__2___closed__7_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__7);
lean_inc(v___y_2345_);
v___x_2358_ = l_Lean_MessageData_ofConstName(v___y_2345_, v___y_2342_);
v___x_2359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2357_);
lean_ctor_set(v___x_2359_, 1, v___x_2358_);
v___x_2360_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__9, &l_Lean_Meta_rwMatcher___lam__2___closed__9_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__9);
v___x_2361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2359_);
lean_ctor_set(v___x_2361_, 1, v___x_2360_);
v___x_2362_ = lean_array_to_list(v_a_2353_);
v___x_2363_ = lean_box(0);
v___x_2364_ = l_List_mapTR_loop___at___00Lean_Meta_rwMatcher_spec__6(v___x_2362_, v___x_2363_);
v___x_2365_ = l_Lean_MessageData_ofList(v___x_2364_);
v___x_2366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2361_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
v___x_2367_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2366_, v___y_2347_, v___y_2349_, v___y_2346_, v___y_2352_);
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
lean_inc(v_a_2368_);
lean_dec_ref(v___x_2367_);
v___y_2266_ = v___y_2341_;
v___y_2267_ = v___y_2345_;
v___y_2268_ = v___y_2351_;
v_a_2269_ = v_a_2368_;
goto v___jp_2265_;
}
else
{
lean_dec_ref(v_a_2353_);
v___y_2320_ = v___y_2341_;
v___y_2321_ = v___y_2345_;
v___y_2322_ = v___y_2344_;
v___y_2323_ = v___y_2343_;
v___y_2324_ = v___y_2348_;
v___y_2325_ = v___y_2350_;
v___y_2326_ = v___y_2351_;
v___y_2327_ = v___y_2347_;
v___y_2328_ = v___y_2349_;
v___y_2329_ = v___y_2346_;
v___y_2330_ = v___y_2352_;
goto v___jp_2319_;
}
}
v___jp_2369_:
{
if (lean_obj_tag(v___y_2382_) == 0)
{
lean_object* v_a_2383_; 
v_a_2383_ = lean_ctor_get(v___y_2382_, 0);
lean_inc(v_a_2383_);
lean_dec_ref_known(v___y_2382_, 1);
v___y_2341_ = v___y_2370_;
v___y_2342_ = v___y_2371_;
v___y_2343_ = v___y_2374_;
v___y_2344_ = v___y_2373_;
v___y_2345_ = v___y_2372_;
v___y_2346_ = v___y_2376_;
v___y_2347_ = v___y_2375_;
v___y_2348_ = v___y_2377_;
v___y_2349_ = v___y_2378_;
v___y_2350_ = v___y_2379_;
v___y_2351_ = v___y_2381_;
v___y_2352_ = v___y_2380_;
v_a_2353_ = v_a_2383_;
goto v___jp_2340_;
}
else
{
lean_object* v_a_2384_; 
lean_dec_ref(v___y_2379_);
lean_dec_ref(v___y_2374_);
v_a_2384_ = lean_ctor_get(v___y_2382_, 0);
lean_inc(v_a_2384_);
lean_dec_ref_known(v___y_2382_, 1);
v___y_2266_ = v___y_2370_;
v___y_2267_ = v___y_2372_;
v___y_2268_ = v___y_2381_;
v_a_2269_ = v_a_2384_;
goto v___jp_2265_;
}
}
v___jp_2385_:
{
lean_object* v___x_2400_; size_t v_sz_2401_; lean_object* v___x_2402_; 
v___x_2400_ = lean_box(0);
v_sz_2401_ = lean_array_size(v___y_2393_);
v___x_2402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7(v___y_2393_, v_sz_2401_, v___y_2387_, v___x_2400_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; uint8_t v___x_2406_; 
lean_dec_ref_known(v___x_2402_, 1);
v___x_2403_ = lean_unsigned_to_nat(0u);
v___x_2404_ = lean_array_get_size(v___y_2393_);
v___x_2405_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__10));
v___x_2406_ = lean_nat_dec_lt(v___x_2403_, v___x_2404_);
if (v___x_2406_ == 0)
{
lean_dec_ref(v___y_2393_);
v___y_2341_ = v___y_2386_;
v___y_2342_ = v___y_2388_;
v___y_2343_ = v___y_2391_;
v___y_2344_ = v___y_2390_;
v___y_2345_ = v___y_2389_;
v___y_2346_ = v___y_2398_;
v___y_2347_ = v___y_2396_;
v___y_2348_ = v___y_2392_;
v___y_2349_ = v___y_2397_;
v___y_2350_ = v___y_2394_;
v___y_2351_ = v___y_2395_;
v___y_2352_ = v___y_2399_;
v_a_2353_ = v___x_2405_;
goto v___jp_2340_;
}
else
{
uint8_t v___x_2407_; 
v___x_2407_ = lean_nat_dec_le(v___x_2404_, v___x_2404_);
if (v___x_2407_ == 0)
{
if (v___x_2406_ == 0)
{
lean_dec_ref(v___y_2393_);
v___y_2341_ = v___y_2386_;
v___y_2342_ = v___y_2388_;
v___y_2343_ = v___y_2391_;
v___y_2344_ = v___y_2390_;
v___y_2345_ = v___y_2389_;
v___y_2346_ = v___y_2398_;
v___y_2347_ = v___y_2396_;
v___y_2348_ = v___y_2392_;
v___y_2349_ = v___y_2397_;
v___y_2350_ = v___y_2394_;
v___y_2351_ = v___y_2395_;
v___y_2352_ = v___y_2399_;
v_a_2353_ = v___x_2405_;
goto v___jp_2340_;
}
else
{
size_t v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = lean_usize_of_nat(v___x_2404_);
v___x_2409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___y_2393_, v___y_2387_, v___x_2408_, v___x_2405_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
lean_dec_ref(v___y_2393_);
v___y_2370_ = v___y_2386_;
v___y_2371_ = v___y_2388_;
v___y_2372_ = v___y_2389_;
v___y_2373_ = v___y_2390_;
v___y_2374_ = v___y_2391_;
v___y_2375_ = v___y_2396_;
v___y_2376_ = v___y_2398_;
v___y_2377_ = v___y_2392_;
v___y_2378_ = v___y_2397_;
v___y_2379_ = v___y_2394_;
v___y_2380_ = v___y_2399_;
v___y_2381_ = v___y_2395_;
v___y_2382_ = v___x_2409_;
goto v___jp_2369_;
}
}
else
{
size_t v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = lean_usize_of_nat(v___x_2404_);
v___x_2411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_rwMatcher_spec__8(v___y_2393_, v___y_2387_, v___x_2410_, v___x_2405_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
lean_dec_ref(v___y_2393_);
v___y_2370_ = v___y_2386_;
v___y_2371_ = v___y_2388_;
v___y_2372_ = v___y_2389_;
v___y_2373_ = v___y_2390_;
v___y_2374_ = v___y_2391_;
v___y_2375_ = v___y_2396_;
v___y_2376_ = v___y_2398_;
v___y_2377_ = v___y_2392_;
v___y_2378_ = v___y_2397_;
v___y_2379_ = v___y_2394_;
v___y_2380_ = v___y_2399_;
v___y_2381_ = v___y_2395_;
v___y_2382_ = v___x_2411_;
goto v___jp_2369_;
}
}
}
else
{
lean_object* v_a_2412_; 
lean_dec_ref(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec_ref(v___y_2391_);
v_a_2412_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_a_2412_);
lean_dec_ref_known(v___x_2402_, 1);
v___y_2266_ = v___y_2386_;
v___y_2267_ = v___y_2389_;
v___y_2268_ = v___y_2395_;
v_a_2269_ = v_a_2412_;
goto v___jp_2265_;
}
}
v___jp_2413_:
{
lean_object* v___x_2429_; 
lean_inc_ref(v_fst_2423_);
lean_inc_ref(v_e_2194_);
v___x_2429_ = l_Lean_Meta_isExprDefEq(v_e_2194_, v_fst_2423_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; uint8_t v___x_2431_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_a_2430_);
lean_dec_ref_known(v___x_2429_, 1);
v___x_2431_ = lean_unbox(v_a_2430_);
lean_dec(v_a_2430_);
if (v___x_2431_ == 0)
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v_a_2446_; 
lean_dec_ref(v_snd_2424_);
lean_dec_ref(v___y_2420_);
lean_dec_ref(v___y_2419_);
v___x_2432_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__12, &l_Lean_Meta_rwMatcher___lam__2___closed__12_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__12);
v___x_2433_ = l_Lean_MessageData_ofExpr(v_fst_2423_);
v___x_2434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2432_);
lean_ctor_set(v___x_2434_, 1, v___x_2433_);
v___x_2435_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__14, &l_Lean_Meta_rwMatcher___lam__2___closed__14_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__14);
v___x_2436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2434_);
lean_ctor_set(v___x_2436_, 1, v___x_2435_);
lean_inc(v___y_2418_);
v___x_2437_ = l_Lean_MessageData_ofConstName(v___y_2418_, v___y_2415_);
v___x_2438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2436_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
v___x_2439_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__16, &l_Lean_Meta_rwMatcher___lam__2___closed__16_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__16);
v___x_2440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2438_);
lean_ctor_set(v___x_2440_, 1, v___x_2439_);
v___x_2441_ = l_Lean_MessageData_ofExpr(v_e_2194_);
v___x_2442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2440_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
v___x_2443_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_rwMatcher_spec__7___closed__3);
v___x_2444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2442_);
lean_ctor_set(v___x_2444_, 1, v___x_2443_);
v___x_2445_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2444_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_a_2446_);
lean_dec_ref(v___x_2445_);
v___y_2266_ = v___y_2414_;
v___y_2267_ = v___y_2418_;
v___y_2268_ = v___y_2421_;
v_a_2269_ = v_a_2446_;
goto v___jp_2265_;
}
else
{
lean_dec_ref(v_fst_2423_);
lean_dec_ref(v_e_2194_);
v___y_2386_ = v___y_2414_;
v___y_2387_ = v___y_2416_;
v___y_2388_ = v___y_2415_;
v___y_2389_ = v___y_2418_;
v___y_2390_ = v___y_2417_;
v___y_2391_ = v_snd_2424_;
v___y_2392_ = v_fst_2422_;
v___y_2393_ = v___y_2419_;
v___y_2394_ = v___y_2420_;
v___y_2395_ = v___y_2421_;
v___y_2396_ = v___y_2425_;
v___y_2397_ = v___y_2426_;
v___y_2398_ = v___y_2427_;
v___y_2399_ = v___y_2428_;
goto v___jp_2385_;
}
}
else
{
lean_object* v_a_2447_; 
lean_dec_ref(v_snd_2424_);
lean_dec_ref(v_fst_2423_);
lean_dec_ref(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec_ref(v_e_2194_);
v_a_2447_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_a_2447_);
lean_dec_ref_known(v___x_2429_, 1);
v___y_2266_ = v___y_2414_;
v___y_2267_ = v___y_2418_;
v___y_2268_ = v___y_2421_;
v_a_2269_ = v_a_2447_;
goto v___jp_2265_;
}
}
v___jp_2448_:
{
lean_object* v___x_2460_; double v___x_2461_; double v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2460_ = lean_io_get_num_heartbeats();
v___x_2461_ = lean_float_of_nat(v___y_2454_);
v___x_2462_ = lean_float_of_nat(v___x_2460_);
v___x_2463_ = lean_box_float(v___x_2461_);
v___x_2464_ = lean_box_float(v___x_2462_);
v___x_2465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2463_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
v___x_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2466_, 0, v_a_2459_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
lean_inc_ref(v___y_2451_);
lean_inc(v___y_2449_);
v___x_2467_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v___y_2449_, v___y_2452_, v___y_2451_, v___y_2457_, v___y_2456_, v___y_2455_, v___y_2453_, v___x_2466_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
v___y_2273_ = v___y_2449_;
v___y_2274_ = v___y_2450_;
v___y_2275_ = v___y_2458_;
v___y_2276_ = v___x_2467_;
goto v___jp_2272_;
}
v___jp_2468_:
{
lean_object* v___x_2480_; 
v___x_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2480_, 0, v_a_2479_);
v___y_2449_ = v___y_2469_;
v___y_2450_ = v___y_2472_;
v___y_2451_ = v___y_2471_;
v___y_2452_ = v___y_2470_;
v___y_2453_ = v___y_2473_;
v___y_2454_ = v___y_2474_;
v___y_2455_ = v___y_2475_;
v___y_2456_ = v___y_2476_;
v___y_2457_ = v___y_2477_;
v___y_2458_ = v___y_2478_;
v_a_2459_ = v___x_2480_;
goto v___jp_2448_;
}
v___jp_2481_:
{
if (lean_obj_tag(v___y_2492_) == 0)
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2500_; 
v_a_2493_ = lean_ctor_get(v___y_2492_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___y_2492_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2495_ = v___y_2492_;
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___y_2492_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2500_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2498_; 
if (v_isShared_2496_ == 0)
{
lean_ctor_set_tag(v___x_2495_, 1);
v___x_2498_ = v___x_2495_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2493_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
v___y_2449_ = v___y_2482_;
v___y_2450_ = v___y_2485_;
v___y_2451_ = v___y_2484_;
v___y_2452_ = v___y_2483_;
v___y_2453_ = v___y_2486_;
v___y_2454_ = v___y_2487_;
v___y_2455_ = v___y_2488_;
v___y_2456_ = v___y_2489_;
v___y_2457_ = v___y_2490_;
v___y_2458_ = v___y_2491_;
v_a_2459_ = v___x_2498_;
goto v___jp_2448_;
}
}
}
else
{
lean_object* v_a_2501_; 
v_a_2501_ = lean_ctor_get(v___y_2492_, 0);
lean_inc(v_a_2501_);
lean_dec_ref_known(v___y_2492_, 1);
v___y_2469_ = v___y_2482_;
v___y_2470_ = v___y_2483_;
v___y_2471_ = v___y_2484_;
v___y_2472_ = v___y_2485_;
v___y_2473_ = v___y_2486_;
v___y_2474_ = v___y_2487_;
v___y_2475_ = v___y_2488_;
v___y_2476_ = v___y_2489_;
v___y_2477_ = v___y_2490_;
v___y_2478_ = v___y_2491_;
v_a_2479_ = v_a_2501_;
goto v___jp_2468_;
}
}
v___jp_2502_:
{
lean_object* v___x_2514_; double v___x_2515_; double v___x_2516_; double v___x_2517_; double v___x_2518_; double v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2514_ = lean_io_mono_nanos_now();
v___x_2515_ = lean_float_of_nat(v___y_2508_);
v___x_2516_ = lean_float_once(&l_Lean_Meta_rwMatcher___closed__6, &l_Lean_Meta_rwMatcher___closed__6_once, _init_l_Lean_Meta_rwMatcher___closed__6);
v___x_2517_ = lean_float_div(v___x_2515_, v___x_2516_);
v___x_2518_ = lean_float_of_nat(v___x_2514_);
v___x_2519_ = lean_float_div(v___x_2518_, v___x_2516_);
v___x_2520_ = lean_box_float(v___x_2517_);
v___x_2521_ = lean_box_float(v___x_2519_);
v___x_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2520_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
v___x_2523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2523_, 0, v_a_2513_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
lean_inc_ref(v___y_2505_);
lean_inc(v___y_2503_);
v___x_2524_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11(v___y_2503_, v___y_2506_, v___y_2505_, v___y_2511_, v___y_2510_, v___y_2509_, v___y_2507_, v___x_2523_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
v___y_2273_ = v___y_2503_;
v___y_2274_ = v___y_2504_;
v___y_2275_ = v___y_2512_;
v___y_2276_ = v___x_2524_;
goto v___jp_2272_;
}
v___jp_2525_:
{
lean_object* v___x_2537_; 
v___x_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2537_, 0, v_a_2536_);
v___y_2503_ = v___y_2526_;
v___y_2504_ = v___y_2529_;
v___y_2505_ = v___y_2528_;
v___y_2506_ = v___y_2527_;
v___y_2507_ = v___y_2531_;
v___y_2508_ = v___y_2530_;
v___y_2509_ = v___y_2532_;
v___y_2510_ = v___y_2533_;
v___y_2511_ = v___y_2534_;
v___y_2512_ = v___y_2535_;
v_a_2513_ = v___x_2537_;
goto v___jp_2502_;
}
v___jp_2538_:
{
if (lean_obj_tag(v___y_2549_) == 0)
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2557_; 
v_a_2550_ = lean_ctor_get(v___y_2549_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___y_2549_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2552_ = v___y_2549_;
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___y_2549_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
if (v_isShared_2553_ == 0)
{
lean_ctor_set_tag(v___x_2552_, 1);
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2550_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
v___y_2503_ = v___y_2539_;
v___y_2504_ = v___y_2542_;
v___y_2505_ = v___y_2541_;
v___y_2506_ = v___y_2540_;
v___y_2507_ = v___y_2544_;
v___y_2508_ = v___y_2543_;
v___y_2509_ = v___y_2545_;
v___y_2510_ = v___y_2546_;
v___y_2511_ = v___y_2547_;
v___y_2512_ = v___y_2548_;
v_a_2513_ = v___x_2555_;
goto v___jp_2502_;
}
}
}
else
{
lean_object* v_a_2558_; 
v_a_2558_ = lean_ctor_get(v___y_2549_, 0);
lean_inc(v_a_2558_);
lean_dec_ref_known(v___y_2549_, 1);
v___y_2526_ = v___y_2539_;
v___y_2527_ = v___y_2540_;
v___y_2528_ = v___y_2541_;
v___y_2529_ = v___y_2542_;
v___y_2530_ = v___y_2543_;
v___y_2531_ = v___y_2544_;
v___y_2532_ = v___y_2545_;
v___y_2533_ = v___y_2546_;
v___y_2534_ = v___y_2547_;
v___y_2535_ = v___y_2548_;
v_a_2536_ = v_a_2558_;
goto v___jp_2525_;
}
}
v___jp_2559_:
{
lean_object* v___x_2574_; lean_object* v_a_2575_; lean_object* v___x_2576_; uint8_t v___x_2577_; 
v___x_2574_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_rwMatcher_spec__9___redArg(v_a_2198_);
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_a_2575_);
lean_dec_ref(v___x_2574_);
v___x_2576_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2577_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v___y_2572_, v___x_2576_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2578_ = lean_io_mono_nanos_now();
lean_inc(v_a_2198_);
lean_inc_ref(v_a_2197_);
lean_inc(v_a_2196_);
lean_inc_ref(v_a_2195_);
v___x_2579_ = lean_infer_type(v___y_2570_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; uint8_t v___x_2581_; lean_object* v___x_2582_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2580_);
lean_dec_ref_known(v___x_2579_, 1);
v___x_2581_ = 0;
v___x_2582_ = l_Lean_Meta_forallMetaTelescope(v_a_2580_, v___x_2581_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; lean_object* v_snd_2584_; lean_object* v_fst_2585_; lean_object* v_snd_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2604_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_a_2583_);
lean_dec_ref_known(v___x_2582_, 1);
v_snd_2584_ = lean_ctor_get(v_a_2583_, 1);
lean_inc(v_snd_2584_);
v_fst_2585_ = lean_ctor_get(v_a_2583_, 0);
lean_inc(v_fst_2585_);
lean_dec(v_a_2583_);
v_snd_2586_ = lean_ctor_get(v_snd_2584_, 1);
v_isSharedCheck_2604_ = !lean_is_exclusive(v_snd_2584_);
if (v_isSharedCheck_2604_ == 0)
{
lean_object* v_unused_2605_; 
v_unused_2605_ = lean_ctor_get(v_snd_2584_, 0);
lean_dec(v_unused_2605_);
v___x_2588_ = v_snd_2584_;
v_isShared_2589_ = v_isSharedCheck_2604_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_snd_2586_);
lean_dec(v_snd_2584_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2604_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; uint8_t v___x_2592_; 
v___x_2590_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2565_);
v___x_2591_ = l_Lean_Name_append(v___x_2590_, v___y_2565_);
v___x_2592_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2566_, v___y_2572_, v___x_2591_);
lean_dec(v___x_2591_);
if (v___x_2592_ == 0)
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
lean_del_object(v___x_2588_);
v___x_2593_ = lean_box(0);
v___x_2594_ = l_Lean_Meta_rwMatcher___lam__2(v___y_2562_, v___y_2564_, v_fst_2585_, v___y_2561_, v___x_2577_, v_e_2194_, v_snd_2586_, v___x_2593_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
lean_dec(v_snd_2586_);
v___y_2539_ = v___y_2565_;
v___y_2540_ = v___y_2567_;
v___y_2541_ = v___y_2568_;
v___y_2542_ = v___y_2569_;
v___y_2543_ = v___x_2578_;
v___y_2544_ = v___y_2563_;
v___y_2545_ = v_a_2575_;
v___y_2546_ = v___y_2571_;
v___y_2547_ = v___y_2572_;
v___y_2548_ = v___y_2573_;
v___y_2549_ = v___x_2594_;
goto v___jp_2538_;
}
else
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2598_; 
v___x_2595_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2586_);
v___x_2596_ = l_Lean_indentExpr(v_snd_2586_);
if (v_isShared_2589_ == 0)
{
lean_ctor_set_tag(v___x_2588_, 7);
lean_ctor_set(v___x_2588_, 1, v___x_2596_);
lean_ctor_set(v___x_2588_, 0, v___x_2595_);
v___x_2598_ = v___x_2588_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v___x_2596_);
v___x_2598_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
lean_object* v___x_2599_; 
lean_inc(v___y_2565_);
v___x_2599_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2565_, v___x_2598_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; lean_object* v___x_2601_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_a_2600_);
lean_dec_ref_known(v___x_2599_, 1);
v___x_2601_ = l_Lean_Meta_rwMatcher___lam__2(v___y_2562_, v___y_2564_, v_fst_2585_, v___y_2561_, v___x_2577_, v_e_2194_, v_snd_2586_, v_a_2600_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
lean_dec(v_snd_2586_);
v___y_2539_ = v___y_2565_;
v___y_2540_ = v___y_2567_;
v___y_2541_ = v___y_2568_;
v___y_2542_ = v___y_2569_;
v___y_2543_ = v___x_2578_;
v___y_2544_ = v___y_2563_;
v___y_2545_ = v_a_2575_;
v___y_2546_ = v___y_2571_;
v___y_2547_ = v___y_2572_;
v___y_2548_ = v___y_2573_;
v___y_2549_ = v___x_2601_;
goto v___jp_2538_;
}
else
{
lean_object* v_a_2602_; 
lean_dec(v_snd_2586_);
lean_dec(v_fst_2585_);
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2561_);
lean_dec_ref(v_e_2194_);
v_a_2602_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_a_2602_);
lean_dec_ref_known(v___x_2599_, 1);
v___y_2526_ = v___y_2565_;
v___y_2527_ = v___y_2567_;
v___y_2528_ = v___y_2568_;
v___y_2529_ = v___y_2569_;
v___y_2530_ = v___x_2578_;
v___y_2531_ = v___y_2563_;
v___y_2532_ = v_a_2575_;
v___y_2533_ = v___y_2571_;
v___y_2534_ = v___y_2572_;
v___y_2535_ = v___y_2573_;
v_a_2536_ = v_a_2602_;
goto v___jp_2525_;
}
}
}
}
}
else
{
lean_object* v_a_2606_; 
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2561_);
lean_dec_ref(v_e_2194_);
v_a_2606_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_a_2606_);
lean_dec_ref_known(v___x_2582_, 1);
v___y_2526_ = v___y_2565_;
v___y_2527_ = v___y_2567_;
v___y_2528_ = v___y_2568_;
v___y_2529_ = v___y_2569_;
v___y_2530_ = v___x_2578_;
v___y_2531_ = v___y_2563_;
v___y_2532_ = v_a_2575_;
v___y_2533_ = v___y_2571_;
v___y_2534_ = v___y_2572_;
v___y_2535_ = v___y_2573_;
v_a_2536_ = v_a_2606_;
goto v___jp_2525_;
}
}
else
{
lean_object* v_a_2607_; 
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2561_);
lean_dec_ref(v_e_2194_);
v_a_2607_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2607_);
lean_dec_ref_known(v___x_2579_, 1);
v___y_2526_ = v___y_2565_;
v___y_2527_ = v___y_2567_;
v___y_2528_ = v___y_2568_;
v___y_2529_ = v___y_2569_;
v___y_2530_ = v___x_2578_;
v___y_2531_ = v___y_2563_;
v___y_2532_ = v_a_2575_;
v___y_2533_ = v___y_2571_;
v___y_2534_ = v___y_2572_;
v___y_2535_ = v___y_2573_;
v_a_2536_ = v_a_2607_;
goto v___jp_2525_;
}
}
else
{
lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2608_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2198_);
lean_inc_ref(v_a_2197_);
lean_inc(v_a_2196_);
lean_inc_ref(v_a_2195_);
v___x_2609_ = lean_infer_type(v___y_2570_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; uint8_t v___x_2611_; lean_object* v___x_2612_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_a_2610_);
lean_dec_ref_known(v___x_2609_, 1);
v___x_2611_ = 0;
v___x_2612_ = l_Lean_Meta_forallMetaTelescope(v_a_2610_, v___x_2611_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v_snd_2614_; lean_object* v_fst_2615_; lean_object* v_snd_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2634_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2613_);
lean_dec_ref_known(v___x_2612_, 1);
v_snd_2614_ = lean_ctor_get(v_a_2613_, 1);
lean_inc(v_snd_2614_);
v_fst_2615_ = lean_ctor_get(v_a_2613_, 0);
lean_inc(v_fst_2615_);
lean_dec(v_a_2613_);
v_snd_2616_ = lean_ctor_get(v_snd_2614_, 1);
v_isSharedCheck_2634_ = !lean_is_exclusive(v_snd_2614_);
if (v_isSharedCheck_2634_ == 0)
{
lean_object* v_unused_2635_; 
v_unused_2635_ = lean_ctor_get(v_snd_2614_, 0);
lean_dec(v_unused_2635_);
v___x_2618_ = v_snd_2614_;
v_isShared_2619_ = v_isSharedCheck_2634_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_snd_2616_);
lean_dec(v_snd_2614_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2634_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; 
v___x_2620_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__1));
lean_inc(v___y_2565_);
v___x_2621_ = l_Lean_Name_append(v___x_2620_, v___y_2565_);
v___x_2622_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v___y_2566_, v___y_2572_, v___x_2621_);
lean_dec(v___x_2621_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
lean_del_object(v___x_2618_);
v___x_2623_ = lean_box(0);
v___x_2624_ = l_Lean_Meta_rwMatcher___lam__3(v___y_2562_, v___y_2564_, v_fst_2615_, v___y_2561_, v___x_2577_, v_e_2194_, v___y_2560_, v_snd_2616_, v___x_2623_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
lean_dec(v_snd_2616_);
v___y_2482_ = v___y_2565_;
v___y_2483_ = v___y_2567_;
v___y_2484_ = v___y_2568_;
v___y_2485_ = v___y_2569_;
v___y_2486_ = v___y_2563_;
v___y_2487_ = v___x_2608_;
v___y_2488_ = v_a_2575_;
v___y_2489_ = v___y_2571_;
v___y_2490_ = v___y_2572_;
v___y_2491_ = v___y_2573_;
v___y_2492_ = v___x_2624_;
goto v___jp_2481_;
}
else
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2628_; 
v___x_2625_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2616_);
v___x_2626_ = l_Lean_indentExpr(v_snd_2616_);
if (v_isShared_2619_ == 0)
{
lean_ctor_set_tag(v___x_2618_, 7);
lean_ctor_set(v___x_2618_, 1, v___x_2626_);
lean_ctor_set(v___x_2618_, 0, v___x_2625_);
v___x_2628_ = v___x_2618_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v___x_2625_);
lean_ctor_set(v_reuseFailAlloc_2633_, 1, v___x_2626_);
v___x_2628_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
lean_object* v___x_2629_; 
lean_inc(v___y_2565_);
v___x_2629_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___y_2565_, v___x_2628_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_a_2630_; lean_object* v___x_2631_; 
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_a_2630_);
lean_dec_ref_known(v___x_2629_, 1);
v___x_2631_ = l_Lean_Meta_rwMatcher___lam__3(v___y_2562_, v___y_2564_, v_fst_2615_, v___y_2561_, v___x_2577_, v_e_2194_, v___y_2560_, v_snd_2616_, v_a_2630_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
lean_dec(v_snd_2616_);
v___y_2482_ = v___y_2565_;
v___y_2483_ = v___y_2567_;
v___y_2484_ = v___y_2568_;
v___y_2485_ = v___y_2569_;
v___y_2486_ = v___y_2563_;
v___y_2487_ = v___x_2608_;
v___y_2488_ = v_a_2575_;
v___y_2489_ = v___y_2571_;
v___y_2490_ = v___y_2572_;
v___y_2491_ = v___y_2573_;
v___y_2492_ = v___x_2631_;
goto v___jp_2481_;
}
else
{
lean_object* v_a_2632_; 
lean_dec(v_snd_2616_);
lean_dec(v_fst_2615_);
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2561_);
lean_dec_ref(v_e_2194_);
v_a_2632_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_a_2632_);
lean_dec_ref_known(v___x_2629_, 1);
v___y_2469_ = v___y_2565_;
v___y_2470_ = v___y_2567_;
v___y_2471_ = v___y_2568_;
v___y_2472_ = v___y_2569_;
v___y_2473_ = v___y_2563_;
v___y_2474_ = v___x_2608_;
v___y_2475_ = v_a_2575_;
v___y_2476_ = v___y_2571_;
v___y_2477_ = v___y_2572_;
v___y_2478_ = v___y_2573_;
v_a_2479_ = v_a_2632_;
goto v___jp_2468_;
}
}
}
}
}
else
{
lean_object* v_a_2636_; 
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2561_);
lean_dec_ref(v_e_2194_);
v_a_2636_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2636_);
lean_dec_ref_known(v___x_2612_, 1);
v___y_2469_ = v___y_2565_;
v___y_2470_ = v___y_2567_;
v___y_2471_ = v___y_2568_;
v___y_2472_ = v___y_2569_;
v___y_2473_ = v___y_2563_;
v___y_2474_ = v___x_2608_;
v___y_2475_ = v_a_2575_;
v___y_2476_ = v___y_2571_;
v___y_2477_ = v___y_2572_;
v___y_2478_ = v___y_2573_;
v_a_2479_ = v_a_2636_;
goto v___jp_2468_;
}
}
else
{
lean_object* v_a_2637_; 
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2561_);
lean_dec_ref(v_e_2194_);
v_a_2637_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_a_2637_);
lean_dec_ref_known(v___x_2609_, 1);
v___y_2469_ = v___y_2565_;
v___y_2470_ = v___y_2567_;
v___y_2471_ = v___y_2568_;
v___y_2472_ = v___y_2569_;
v___y_2473_ = v___y_2563_;
v___y_2474_ = v___x_2608_;
v___y_2475_ = v_a_2575_;
v___y_2476_ = v___y_2571_;
v___y_2477_ = v___y_2572_;
v___y_2478_ = v___y_2573_;
v_a_2479_ = v_a_2637_;
goto v___jp_2468_;
}
}
}
v___jp_2638_:
{
uint8_t v___x_2640_; 
v___x_2640_ = 1;
if (v___y_2639_ == 0)
{
lean_object* v___x_2641_; lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2810_; 
v___x_2641_ = l_Lean_Meta_isMatcherApp___at___00Lean_Meta_rwMatcher_spec__1___redArg(v_e_2194_, v_a_2198_);
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2644_ = v___x_2641_;
v_isShared_2645_ = v_isSharedCheck_2810_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_a_2642_);
lean_dec(v___x_2641_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2810_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
uint8_t v___x_2646_; 
v___x_2646_ = lean_unbox(v_a_2642_);
lean_dec(v_a_2642_);
if (v___x_2646_ == 0)
{
lean_object* v_options_2647_; uint8_t v_hasTrace_2648_; 
lean_del_object(v___x_2644_);
lean_dec(v_altIdx_2193_);
v_options_2647_ = lean_ctor_get(v_a_2197_, 2);
v_hasTrace_2648_ = lean_ctor_get_uint8(v_options_2647_, sizeof(void*)*1);
if (v_hasTrace_2648_ == 0)
{
v___y_2220_ = v___x_2640_;
goto v___jp_2219_;
}
else
{
lean_object* v_inheritedTraceOptions_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; uint8_t v___x_2652_; 
v_inheritedTraceOptions_2649_ = lean_ctor_get(v_a_2197_, 13);
v___x_2650_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2651_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2652_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2649_, v_options_2647_, v___x_2651_);
if (v___x_2652_ == 0)
{
v___y_2220_ = v___x_2640_;
goto v___jp_2219_;
}
else
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2653_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__15, &l_Lean_Meta_rwMatcher___closed__15_once, _init_l_Lean_Meta_rwMatcher___closed__15);
lean_inc_ref(v_e_2194_);
v___x_2654_ = l_Lean_indentExpr(v_e_2194_);
v___x_2655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2653_);
lean_ctor_set(v___x_2655_, 1, v___x_2654_);
v___x_2656_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2650_, v___x_2655_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_dec_ref_known(v___x_2656_, 1);
v___y_2220_ = v___x_2640_;
goto v___jp_2219_;
}
else
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2664_; 
lean_dec_ref(v_e_2194_);
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2659_ = v___x_2656_;
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2656_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_a_2657_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
}
}
}
else
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2665_ = l_Lean_Expr_getAppFn(v_e_2194_);
v___x_2666_ = l_Lean_Expr_constName_x21(v___x_2665_);
lean_inc(v_a_2198_);
lean_inc_ref(v_a_2197_);
lean_inc(v_a_2196_);
lean_inc_ref(v_a_2195_);
lean_inc(v___x_2666_);
v___x_2667_ = lean_get_congr_match_equations_for(v___x_2666_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; lean_object* v___x_2669_; uint8_t v___x_2670_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
lean_inc(v_a_2668_);
lean_dec_ref_known(v___x_2667_, 1);
v___x_2669_ = lean_array_get_size(v_a_2668_);
v___x_2670_ = lean_nat_dec_lt(v_altIdx_2193_, v___x_2669_);
if (v___x_2670_ == 0)
{
lean_object* v_options_2671_; uint8_t v_hasTrace_2672_; 
lean_dec(v_a_2668_);
lean_dec_ref(v___x_2665_);
v_options_2671_ = lean_ctor_get(v_a_2197_, 2);
v_hasTrace_2672_ = lean_ctor_get_uint8(v_options_2671_, sizeof(void*)*1);
if (v_hasTrace_2672_ == 0)
{
lean_dec(v___x_2666_);
lean_del_object(v___x_2644_);
lean_dec(v_altIdx_2193_);
v___y_2225_ = v___x_2640_;
goto v___jp_2224_;
}
else
{
lean_object* v_inheritedTraceOptions_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; uint8_t v___x_2676_; 
v_inheritedTraceOptions_2673_ = lean_ctor_get(v_a_2197_, 13);
v___x_2674_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2675_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2676_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2673_, v_options_2671_, v___x_2675_);
if (v___x_2676_ == 0)
{
lean_dec(v___x_2666_);
lean_del_object(v___x_2644_);
lean_dec(v_altIdx_2193_);
v___y_2225_ = v___x_2640_;
goto v___jp_2224_;
}
else
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2680_; 
v___x_2677_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__17, &l_Lean_Meta_rwMatcher___closed__17_once, _init_l_Lean_Meta_rwMatcher___closed__17);
v___x_2678_ = l_Nat_reprFast(v_altIdx_2193_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set_tag(v___x_2644_, 3);
lean_ctor_set(v___x_2644_, 0, v___x_2678_);
v___x_2680_ = v___x_2644_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2678_);
v___x_2680_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2681_ = l_Lean_MessageData_ofFormat(v___x_2680_);
v___x_2682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2677_);
lean_ctor_set(v___x_2682_, 1, v___x_2681_);
v___x_2683_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__19, &l_Lean_Meta_rwMatcher___closed__19_once, _init_l_Lean_Meta_rwMatcher___closed__19);
v___x_2684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2682_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
v___x_2685_ = l_Nat_reprFast(v___x_2669_);
v___x_2686_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2685_);
v___x_2687_ = l_Lean_MessageData_ofFormat(v___x_2686_);
v___x_2688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2684_);
lean_ctor_set(v___x_2688_, 1, v___x_2687_);
v___x_2689_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__21, &l_Lean_Meta_rwMatcher___closed__21_once, _init_l_Lean_Meta_rwMatcher___closed__21);
v___x_2690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2688_);
lean_ctor_set(v___x_2690_, 1, v___x_2689_);
v___x_2691_ = l_Lean_MessageData_ofConstName(v___x_2666_, v___y_2639_);
v___x_2692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2690_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
v___x_2693_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2674_, v___x_2692_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_dec_ref_known(v___x_2693_, 1);
v___y_2225_ = v___x_2640_;
goto v___jp_2224_;
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
lean_dec_ref(v_e_2194_);
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2693_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2693_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
}
}
}
else
{
lean_object* v_options_2703_; lean_object* v_inheritedTraceOptions_2704_; uint8_t v_hasTrace_2705_; lean_object* v_nargs_2706_; lean_object* v___x_2707_; lean_object* v___f_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v_dummy_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
lean_dec(v___x_2666_);
lean_del_object(v___x_2644_);
v_options_2703_ = lean_ctor_get(v_a_2197_, 2);
v_inheritedTraceOptions_2704_ = lean_ctor_get(v_a_2197_, 13);
v_hasTrace_2705_ = lean_ctor_get_uint8(v_options_2703_, sizeof(void*)*1);
v_nargs_2706_ = l_Lean_Expr_getAppNumArgs(v_e_2194_);
v___x_2707_ = lean_box(v___x_2640_);
lean_inc_ref_n(v_e_2194_, 2);
v___f_2708_ = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2708_, 0, v_e_2194_);
lean_closure_set(v___f_2708_, 1, v___x_2707_);
v___x_2709_ = lean_box(0);
v___x_2710_ = lean_array_get(v___x_2709_, v_a_2668_, v_altIdx_2193_);
lean_dec(v_altIdx_2193_);
lean_dec(v_a_2668_);
v___x_2711_ = ((lean_object*)(l_Lean_Meta_rwMatcher___closed__12));
v___x_2712_ = l_Lean_Expr_constLevels_x21(v___x_2665_);
lean_dec_ref(v___x_2665_);
lean_inc(v___x_2710_);
v___x_2713_ = l_Lean_mkConst(v___x_2710_, v___x_2712_);
v_dummy_2714_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__22, &l_Lean_Meta_rwMatcher___closed__22_once, _init_l_Lean_Meta_rwMatcher___closed__22);
lean_inc(v_nargs_2706_);
v___x_2715_ = lean_mk_array(v_nargs_2706_, v_dummy_2714_);
v___x_2716_ = lean_unsigned_to_nat(1u);
v___x_2717_ = lean_nat_sub(v_nargs_2706_, v___x_2716_);
lean_dec(v_nargs_2706_);
v___x_2718_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2194_, v___x_2715_, v___x_2717_);
v___x_2719_ = l_Lean_mkAppN(v___x_2713_, v___x_2718_);
lean_dec_ref(v___x_2718_);
if (v_hasTrace_2705_ == 0)
{
lean_object* v___x_2720_; 
lean_inc(v_a_2198_);
lean_inc_ref(v_a_2197_);
lean_inc(v_a_2196_);
lean_inc_ref(v_a_2195_);
lean_inc_ref(v___x_2719_);
v___x_2720_ = lean_infer_type(v___x_2719_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v_a_2721_; uint8_t v___x_2722_; lean_object* v___x_2723_; 
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2721_);
lean_dec_ref_known(v___x_2720_, 1);
v___x_2722_ = 0;
v___x_2723_ = l_Lean_Meta_forallMetaTelescope(v_a_2721_, v___x_2722_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v_a_2724_; lean_object* v_snd_2725_; lean_object* v_fst_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2764_; 
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
lean_inc(v_a_2724_);
lean_dec_ref_known(v___x_2723_, 1);
v_snd_2725_ = lean_ctor_get(v_a_2724_, 1);
v_fst_2726_ = lean_ctor_get(v_a_2724_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v_a_2724_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2728_ = v_a_2724_;
v_isShared_2729_ = v_isSharedCheck_2764_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_snd_2725_);
lean_inc(v_fst_2726_);
lean_dec(v_a_2724_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2764_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v_snd_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2762_; 
v_snd_2730_ = lean_ctor_get(v_snd_2725_, 1);
v_isSharedCheck_2762_ = !lean_is_exclusive(v_snd_2725_);
if (v_isSharedCheck_2762_ == 0)
{
lean_object* v_unused_2763_; 
v_unused_2763_ = lean_ctor_get(v_snd_2725_, 0);
lean_dec(v_unused_2763_);
v___x_2732_ = v_snd_2725_;
v_isShared_2733_ = v_isSharedCheck_2762_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_snd_2730_);
lean_dec(v_snd_2725_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2762_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2734_; size_t v_sz_2735_; size_t v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; uint8_t v___x_2740_; 
v___x_2734_ = l_Lean_mkAppN(v___x_2719_, v_fst_2726_);
v_sz_2735_ = lean_array_size(v_fst_2726_);
v___x_2736_ = ((size_t)0ULL);
v___x_2737_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_rwMatcher_spec__3(v_sz_2735_, v___x_2736_, v_fst_2726_);
v___x_2738_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__18));
v___x_2739_ = lean_unsigned_to_nat(4u);
v___x_2740_ = l_Lean_Expr_isAppOfArity(v_snd_2730_, v___x_2738_, v___x_2739_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; lean_object* v___x_2742_; uint8_t v___x_2743_; 
v___x_2741_ = ((lean_object*)(l_Lean_Meta_rwMatcher___lam__2___closed__20));
v___x_2742_ = lean_unsigned_to_nat(3u);
v___x_2743_ = l_Lean_Expr_isAppOfArity(v_snd_2730_, v___x_2741_, v___x_2742_);
if (v___x_2743_ == 0)
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2747_; 
lean_dec_ref(v___x_2737_);
lean_dec_ref(v___x_2734_);
lean_dec(v_snd_2730_);
lean_dec_ref(v_e_2194_);
v___x_2744_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__22, &l_Lean_Meta_rwMatcher___lam__2___closed__22_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__22);
lean_inc(v___x_2710_);
v___x_2745_ = l_Lean_MessageData_ofConstName(v___x_2710_, v_hasTrace_2705_);
if (v_isShared_2733_ == 0)
{
lean_ctor_set_tag(v___x_2732_, 7);
lean_ctor_set(v___x_2732_, 1, v___x_2745_);
lean_ctor_set(v___x_2732_, 0, v___x_2744_);
v___x_2747_ = v___x_2732_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2744_);
lean_ctor_set(v_reuseFailAlloc_2754_, 1, v___x_2745_);
v___x_2747_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
lean_object* v___x_2748_; lean_object* v___x_2750_; 
v___x_2748_ = lean_obj_once(&l_Lean_Meta_rwMatcher___lam__2___closed__24, &l_Lean_Meta_rwMatcher___lam__2___closed__24_once, _init_l_Lean_Meta_rwMatcher___lam__2___closed__24);
if (v_isShared_2729_ == 0)
{
lean_ctor_set_tag(v___x_2728_, 7);
lean_ctor_set(v___x_2728_, 1, v___x_2748_);
lean_ctor_set(v___x_2728_, 0, v___x_2747_);
v___x_2750_ = v___x_2728_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2747_);
lean_ctor_set(v_reuseFailAlloc_2753_, 1, v___x_2748_);
v___x_2750_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
lean_object* v___x_2751_; lean_object* v_a_2752_; 
v___x_2751_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v___x_2750_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
lean_inc(v_a_2752_);
lean_dec_ref(v___x_2751_);
v___y_2266_ = v___x_2711_;
v___y_2267_ = v___x_2710_;
v___y_2268_ = v___f_2708_;
v_a_2269_ = v_a_2752_;
goto v___jp_2265_;
}
}
}
else
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
lean_del_object(v___x_2732_);
lean_del_object(v___x_2728_);
v___x_2755_ = l_Lean_Expr_appFn_x21(v_snd_2730_);
v___x_2756_ = l_Lean_Expr_appArg_x21(v___x_2755_);
lean_dec_ref(v___x_2755_);
v___x_2757_ = l_Lean_Expr_appArg_x21(v_snd_2730_);
lean_dec(v_snd_2730_);
v___y_2414_ = v___x_2711_;
v___y_2415_ = v_hasTrace_2705_;
v___y_2416_ = v___x_2736_;
v___y_2417_ = v___x_2640_;
v___y_2418_ = v___x_2710_;
v___y_2419_ = v___x_2737_;
v___y_2420_ = v___x_2734_;
v___y_2421_ = v___f_2708_;
v_fst_2422_ = v_hasTrace_2705_;
v_fst_2423_ = v___x_2756_;
v_snd_2424_ = v___x_2757_;
v___y_2425_ = v_a_2195_;
v___y_2426_ = v_a_2196_;
v___y_2427_ = v_a_2197_;
v___y_2428_ = v_a_2198_;
goto v___jp_2413_;
}
}
else
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
lean_del_object(v___x_2732_);
lean_del_object(v___x_2728_);
v___x_2758_ = l_Lean_Expr_appFn_x21(v_snd_2730_);
v___x_2759_ = l_Lean_Expr_appFn_x21(v___x_2758_);
lean_dec_ref(v___x_2758_);
v___x_2760_ = l_Lean_Expr_appArg_x21(v___x_2759_);
lean_dec_ref(v___x_2759_);
v___x_2761_ = l_Lean_Expr_appArg_x21(v_snd_2730_);
lean_dec(v_snd_2730_);
v___y_2414_ = v___x_2711_;
v___y_2415_ = v_hasTrace_2705_;
v___y_2416_ = v___x_2736_;
v___y_2417_ = v___x_2640_;
v___y_2418_ = v___x_2710_;
v___y_2419_ = v___x_2737_;
v___y_2420_ = v___x_2734_;
v___y_2421_ = v___f_2708_;
v_fst_2422_ = v___x_2640_;
v_fst_2423_ = v___x_2760_;
v_snd_2424_ = v___x_2761_;
v___y_2425_ = v_a_2195_;
v___y_2426_ = v_a_2196_;
v___y_2427_ = v_a_2197_;
v___y_2428_ = v_a_2198_;
goto v___jp_2413_;
}
}
}
}
else
{
lean_object* v_a_2765_; 
lean_dec_ref(v___x_2719_);
lean_dec_ref(v_e_2194_);
v_a_2765_ = lean_ctor_get(v___x_2723_, 0);
lean_inc(v_a_2765_);
lean_dec_ref_known(v___x_2723_, 1);
v___y_2266_ = v___x_2711_;
v___y_2267_ = v___x_2710_;
v___y_2268_ = v___f_2708_;
v_a_2269_ = v_a_2765_;
goto v___jp_2265_;
}
}
else
{
lean_object* v_a_2766_; 
lean_dec_ref(v___x_2719_);
lean_dec_ref(v_e_2194_);
v_a_2766_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2766_);
lean_dec_ref_known(v___x_2720_, 1);
v___y_2266_ = v___x_2711_;
v___y_2267_ = v___x_2710_;
v___y_2268_ = v___f_2708_;
v_a_2269_ = v_a_2766_;
goto v___jp_2265_;
}
}
else
{
lean_object* v___x_2767_; lean_object* v___f_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; uint8_t v___x_2771_; 
v___x_2767_ = lean_box(v___y_2639_);
lean_inc_ref(v_e_2194_);
lean_inc(v___x_2710_);
v___f_2768_ = lean_alloc_closure((void*)(l_Lean_Meta_rwMatcher___lam__1___boxed), 9, 3);
lean_closure_set(v___f_2768_, 0, v___x_2710_);
lean_closure_set(v___f_2768_, 1, v___x_2767_);
lean_closure_set(v___f_2768_, 2, v_e_2194_);
v___x_2769_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2___closed__1));
v___x_2770_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__13, &l_Lean_Meta_rwMatcher___closed__13_once, _init_l_Lean_Meta_rwMatcher___closed__13);
v___x_2771_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2704_, v_options_2703_, v___x_2770_);
if (v___x_2771_ == 0)
{
lean_object* v___x_2772_; uint8_t v___x_2773_; 
v___x_2772_ = l_Lean_trace_profiler;
v___x_2773_ = l_Lean_Option_get___at___00Lean_Meta_rwMatcher_spec__10(v_options_2703_, v___x_2772_);
if (v___x_2773_ == 0)
{
lean_object* v___x_2774_; 
lean_dec_ref(v___f_2768_);
lean_inc(v_a_2198_);
lean_inc_ref(v_a_2197_);
lean_inc(v_a_2196_);
lean_inc_ref(v_a_2195_);
lean_inc_ref(v___x_2719_);
v___x_2774_ = lean_infer_type(v___x_2719_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v_a_2775_; uint8_t v___x_2776_; lean_object* v___x_2777_; 
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_a_2775_);
lean_dec_ref_known(v___x_2774_, 1);
v___x_2776_ = 0;
v___x_2777_ = l_Lean_Meta_forallMetaTelescope(v_a_2775_, v___x_2776_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; lean_object* v_snd_2779_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc(v_a_2778_);
lean_dec_ref_known(v___x_2777_, 1);
v_snd_2779_ = lean_ctor_get(v_a_2778_, 1);
lean_inc(v_snd_2779_);
if (v___x_2771_ == 0)
{
lean_object* v_fst_2780_; lean_object* v_snd_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v_fst_2780_ = lean_ctor_get(v_a_2778_, 0);
lean_inc(v_fst_2780_);
lean_dec(v_a_2778_);
v_snd_2781_ = lean_ctor_get(v_snd_2779_, 1);
lean_inc(v_snd_2781_);
lean_dec(v_snd_2779_);
v___x_2782_ = lean_box(0);
lean_inc(v___x_2710_);
v___x_2783_ = l_Lean_Meta_rwMatcher___lam__4(v___x_2640_, v___x_2719_, v_fst_2780_, v___x_2710_, v___x_2773_, v_e_2194_, v_snd_2781_, v___x_2782_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
lean_dec(v_snd_2781_);
v___y_2273_ = v___x_2711_;
v___y_2274_ = v___x_2710_;
v___y_2275_ = v___f_2708_;
v___y_2276_ = v___x_2783_;
goto v___jp_2272_;
}
else
{
lean_object* v_fst_2784_; lean_object* v_snd_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2798_; 
v_fst_2784_ = lean_ctor_get(v_a_2778_, 0);
lean_inc(v_fst_2784_);
lean_dec(v_a_2778_);
v_snd_2785_ = lean_ctor_get(v_snd_2779_, 1);
v_isSharedCheck_2798_ = !lean_is_exclusive(v_snd_2779_);
if (v_isSharedCheck_2798_ == 0)
{
lean_object* v_unused_2799_; 
v_unused_2799_ = lean_ctor_get(v_snd_2779_, 0);
lean_dec(v_unused_2799_);
v___x_2787_ = v_snd_2779_;
v_isShared_2788_ = v_isSharedCheck_2798_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_snd_2785_);
lean_dec(v_snd_2779_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2798_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2792_; 
v___x_2789_ = lean_obj_once(&l_Lean_Meta_rwMatcher___closed__8, &l_Lean_Meta_rwMatcher___closed__8_once, _init_l_Lean_Meta_rwMatcher___closed__8);
lean_inc(v_snd_2785_);
v___x_2790_ = l_Lean_indentExpr(v_snd_2785_);
if (v_isShared_2788_ == 0)
{
lean_ctor_set_tag(v___x_2787_, 7);
lean_ctor_set(v___x_2787_, 1, v___x_2790_);
lean_ctor_set(v___x_2787_, 0, v___x_2789_);
v___x_2792_ = v___x_2787_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2789_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v___x_2790_);
v___x_2792_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
lean_object* v___x_2793_; 
v___x_2793_ = l_Lean_addTrace___at___00Lean_Meta_rwMatcher_spec__2(v___x_2711_, v___x_2792_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v___x_2795_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_a_2794_);
lean_dec_ref_known(v___x_2793_, 1);
lean_inc(v___x_2710_);
v___x_2795_ = l_Lean_Meta_rwMatcher___lam__4(v___x_2640_, v___x_2719_, v_fst_2784_, v___x_2710_, v___x_2773_, v_e_2194_, v_snd_2785_, v_a_2794_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
lean_dec(v_snd_2785_);
v___y_2273_ = v___x_2711_;
v___y_2274_ = v___x_2710_;
v___y_2275_ = v___f_2708_;
v___y_2276_ = v___x_2795_;
goto v___jp_2272_;
}
else
{
lean_object* v_a_2796_; 
lean_dec(v_snd_2785_);
lean_dec(v_fst_2784_);
lean_dec_ref(v___x_2719_);
lean_dec_ref(v_e_2194_);
v_a_2796_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_a_2796_);
lean_dec_ref_known(v___x_2793_, 1);
v___y_2266_ = v___x_2711_;
v___y_2267_ = v___x_2710_;
v___y_2268_ = v___f_2708_;
v_a_2269_ = v_a_2796_;
goto v___jp_2265_;
}
}
}
}
}
else
{
lean_object* v_a_2800_; 
lean_dec_ref(v___x_2719_);
lean_dec_ref(v_e_2194_);
v_a_2800_ = lean_ctor_get(v___x_2777_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2777_, 1);
v___y_2266_ = v___x_2711_;
v___y_2267_ = v___x_2710_;
v___y_2268_ = v___f_2708_;
v_a_2269_ = v_a_2800_;
goto v___jp_2265_;
}
}
else
{
lean_object* v_a_2801_; 
lean_dec_ref(v___x_2719_);
lean_dec_ref(v_e_2194_);
v_a_2801_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_a_2801_);
lean_dec_ref_known(v___x_2774_, 1);
v___y_2266_ = v___x_2711_;
v___y_2267_ = v___x_2710_;
v___y_2268_ = v___f_2708_;
v_a_2269_ = v_a_2801_;
goto v___jp_2265_;
}
}
else
{
lean_inc_ref(v___x_2719_);
lean_inc(v___x_2710_);
v___y_2560_ = v___y_2639_;
v___y_2561_ = v___x_2710_;
v___y_2562_ = v___x_2640_;
v___y_2563_ = v___f_2768_;
v___y_2564_ = v___x_2719_;
v___y_2565_ = v___x_2711_;
v___y_2566_ = v_inheritedTraceOptions_2704_;
v___y_2567_ = v___x_2640_;
v___y_2568_ = v___x_2769_;
v___y_2569_ = v___x_2710_;
v___y_2570_ = v___x_2719_;
v___y_2571_ = v___x_2771_;
v___y_2572_ = v_options_2703_;
v___y_2573_ = v___f_2708_;
goto v___jp_2559_;
}
}
else
{
lean_inc_ref(v___x_2719_);
lean_inc(v___x_2710_);
v___y_2560_ = v___y_2639_;
v___y_2561_ = v___x_2710_;
v___y_2562_ = v___x_2640_;
v___y_2563_ = v___f_2768_;
v___y_2564_ = v___x_2719_;
v___y_2565_ = v___x_2711_;
v___y_2566_ = v_inheritedTraceOptions_2704_;
v___y_2567_ = v___x_2640_;
v___y_2568_ = v___x_2769_;
v___y_2569_ = v___x_2710_;
v___y_2570_ = v___x_2719_;
v___y_2571_ = v___x_2771_;
v___y_2572_ = v_options_2703_;
v___y_2573_ = v___f_2708_;
goto v___jp_2559_;
}
}
}
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
lean_dec(v___x_2666_);
lean_dec_ref(v___x_2665_);
lean_del_object(v___x_2644_);
lean_dec_ref(v_e_2194_);
lean_dec(v_altIdx_2193_);
v_a_2802_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2667_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2667_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
}
}
else
{
lean_object* v___x_2811_; 
lean_dec(v_altIdx_2193_);
v___x_2811_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__14___redArg(v_e_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2821_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2814_ = v___x_2811_;
v_isShared_2815_ = v_isSharedCheck_2821_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2811_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2821_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2819_; 
v___x_2816_ = lean_box(0);
v___x_2817_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2817_, 0, v_a_2812_);
lean_ctor_set(v___x_2817_, 1, v___x_2816_);
lean_ctor_set_uint8(v___x_2817_, sizeof(void*)*2, v___x_2640_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 0, v___x_2817_);
v___x_2819_ = v___x_2814_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v___x_2817_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
else
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
v_a_2822_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2824_ = v___x_2811_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2811_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2822_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_rwMatcher___boxed(lean_object* v_altIdx_2834_, lean_object* v_e_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Lean_Meta_rwMatcher(v_altIdx_2834_, v_e_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_);
lean_dec(v_a_2839_);
lean_dec_ref(v_a_2838_);
lean_dec(v_a_2837_);
lean_dec_ref(v_a_2836_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(lean_object* v_mvarId_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v___x_2848_; 
v___x_2848_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___redArg(v_mvarId_2842_, v___y_2844_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0___boxed(lean_object* v_mvarId_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_){
_start:
{
lean_object* v_res_2855_; 
v_res_2855_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0(v_mvarId_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v_mvarId_2849_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5(lean_object* v_00_u03b1_2856_, lean_object* v_msg_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v___x_2863_; 
v___x_2863_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___redArg(v_msg_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5___boxed(lean_object* v_00_u03b1_2864_, lean_object* v_msg_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l_Lean_throwError___at___00Lean_Meta_rwMatcher_spec__5(v_00_u03b1_2864_, v_msg_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14(lean_object* v_00_u03b1_2872_, lean_object* v_x_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
lean_object* v___x_2879_; 
v___x_2879_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___redArg(v_x_2873_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14___boxed(lean_object* v_00_u03b1_2880_, lean_object* v_x_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_rwMatcher_spec__11_spec__14(v_00_u03b1_2880_, v_x_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__14(lean_object* v_inst_2888_, lean_object* v_a_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_){
_start:
{
lean_object* v___x_2895_; 
v___x_2895_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__14___redArg(v_a_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__14___boxed(lean_object* v_inst_2896_, lean_object* v_a_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Meta_rwMatcher_spec__14(v_inst_2896_, v_a_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
return v_res_2903_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(lean_object* v_00_u03b2_2904_, lean_object* v_x_2905_, lean_object* v_x_2906_){
_start:
{
uint8_t v___x_2907_; 
v___x_2907_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___redArg(v_x_2905_, v_x_2906_);
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2908_, lean_object* v_x_2909_, lean_object* v_x_2910_){
_start:
{
uint8_t v_res_2911_; lean_object* v_r_2912_; 
v_res_2911_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0(v_00_u03b2_2908_, v_x_2909_, v_x_2910_);
lean_dec(v_x_2910_);
lean_dec_ref(v_x_2909_);
v_r_2912_ = lean_box(v_res_2911_);
return v_r_2912_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5(lean_object* v_00_u03b2_2913_, lean_object* v_x_2914_, size_t v_x_2915_, lean_object* v_x_2916_){
_start:
{
uint8_t v___x_2917_; 
v___x_2917_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___redArg(v_x_2914_, v_x_2915_, v_x_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b2_2918_, lean_object* v_x_2919_, lean_object* v_x_2920_, lean_object* v_x_2921_){
_start:
{
size_t v_x_112281__boxed_2922_; uint8_t v_res_2923_; lean_object* v_r_2924_; 
v_x_112281__boxed_2922_ = lean_unbox_usize(v_x_2920_);
lean_dec(v_x_2920_);
v_res_2923_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5(v_00_u03b2_2918_, v_x_2919_, v_x_112281__boxed_2922_, v_x_2921_);
lean_dec(v_x_2921_);
lean_dec_ref(v_x_2919_);
v_r_2924_ = lean_box(v_res_2923_);
return v_r_2924_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20(lean_object* v_00_u03b2_2925_, lean_object* v_keys_2926_, lean_object* v_vals_2927_, lean_object* v_heq_2928_, lean_object* v_i_2929_, lean_object* v_k_2930_){
_start:
{
uint8_t v___x_2931_; 
v___x_2931_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20___redArg(v_keys_2926_, v_i_2929_, v_k_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20___boxed(lean_object* v_00_u03b2_2932_, lean_object* v_keys_2933_, lean_object* v_vals_2934_, lean_object* v_heq_2935_, lean_object* v_i_2936_, lean_object* v_k_2937_){
_start:
{
uint8_t v_res_2938_; lean_object* v_r_2939_; 
v_res_2938_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_rwMatcher_spec__0_spec__0_spec__5_spec__20(v_00_u03b2_2932_, v_keys_2933_, v_vals_2934_, v_heq_2935_, v_i_2936_, v_k_2937_);
lean_dec(v_k_2937_);
lean_dec_ref(v_vals_2934_);
lean_dec_ref(v_keys_2933_);
v_r_2939_ = lean_box(v_res_2938_);
return v_r_2939_;
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
