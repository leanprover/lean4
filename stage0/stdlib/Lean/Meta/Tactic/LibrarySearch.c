// Lean compiler output
// Module: Lean.Meta.Tactic.LibrarySearch
// Imports: public import Lean.Meta.LazyDiscrTree public import Lean.Meta.Tactic.SolveByElim public import Lean.Meta.Tactic.Grind.Main public import Lean.Util.Heartbeats import Init.Grind.Util import Init.Try import Lean.Elab.Tactic.Basic import Init.Omega
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_getMaxHeartbeats___redArg(lean_object*);
lean_object* l_Lean_getRemainingHeartbeats___redArg(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapForallTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerInternalExceptionId(lean_object*);
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Linter_isDeprecated(lean_object*, lean_object*);
uint8_t l_Lean_Name_isMetaprogramming(lean_object*);
lean_object* l_Lean_AsyncConstantInfo_toConstantVal(lean_object*);
lean_object* l_Lean_Meta_LazyDiscrTree_findMatches___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_applySymm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkDefaultParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Result_hasFailed(lean_object*);
lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withSuppressedMessages___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "librarySearch"};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 205, 46, 93, 234, 75, 44, 75)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(147, 126, 84, 67, 30, 19, 97, 104)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__3_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__3_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__3_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__4_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__3_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__4_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__4_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__6_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__4_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__6_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__6_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__7_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__7_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__7_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__8_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__6_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__7_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__8_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__8_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__9_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__8_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__9_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__9_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__10_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "LibrarySearch"};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__10_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__10_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__11_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__9_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__10_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(163, 78, 22, 138, 134, 243, 124, 51)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__11_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__11_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__12_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__11_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(110, 120, 122, 133, 19, 71, 36, 249)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__12_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__12_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__13_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__12_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(151, 146, 148, 188, 159, 0, 15, 205)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__13_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__13_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__14_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__13_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__7_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(199, 3, 3, 192, 219, 237, 74, 42)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__14_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__14_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__15_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__14_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__10_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 81, 21, 29, 149, 2, 225, 39)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__15_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__15_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__16_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__16_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__16_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__17_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__15_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__16_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(206, 129, 140, 75, 45, 159, 152, 19)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__17_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__17_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__18_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__18_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__18_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__19_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__17_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__18_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(207, 237, 167, 131, 38, 2, 223, 9)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__19_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__19_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__20_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__19_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(226, 89, 165, 117, 164, 120, 225, 40)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__20_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__20_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__21_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__20_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__7_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(246, 152, 58, 84, 237, 223, 251, 209)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__21_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__21_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__22_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__21_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(11, 67, 15, 244, 60, 52, 77, 103)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__22_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__22_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__23_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__22_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__10_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(139, 233, 199, 48, 25, 63, 191, 255)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__23_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__23_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__24_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__24_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__25_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__25_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__25_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__26_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__26_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__27_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__27_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__27_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__28_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__28_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__29_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__29_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "lemmas"};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 205, 46, 93, 234, 75, 44, 75)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(147, 126, 84, 67, 30, 19, 97, 104)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(197, 54, 69, 18, 129, 165, 16, 234)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__23_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),((lean_object*)(((size_t)(472600257) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(154, 223, 28, 58, 97, 218, 116, 222)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__3_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__25_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(53, 33, 63, 88, 40, 222, 1, 43)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__3_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__3_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__4_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__3_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__27_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(117, 161, 124, 21, 15, 207, 112, 94)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__4_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__4_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__4_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(56, 96, 151, 243, 172, 210, 118, 145)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2____boxed(lean_object*);
static const lean_ctor_object l_Lean_Meta_LibrarySearch_grindDischarger___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_LibrarySearch_grindDischarger___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_LibrarySearch_grindDischarger___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_grindDischarger___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_LibrarySearch_grindDischarger___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_LibrarySearch_grindDischarger___closed__0 = (const lean_object*)&l_Lean_Meta_LibrarySearch_grindDischarger___closed__0_value;
static const lean_string_object l_Lean_Meta_LibrarySearch_grindDischarger___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Marker"};
static const lean_object* l_Lean_Meta_LibrarySearch_grindDischarger___closed__1 = (const lean_object*)&l_Lean_Meta_LibrarySearch_grindDischarger___closed__1_value;
static const lean_ctor_object l_Lean_Meta_LibrarySearch_grindDischarger___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_LibrarySearch_grindDischarger___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_LibrarySearch_grindDischarger___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_LibrarySearch_grindDischarger___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_LibrarySearch_grindDischarger___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_LibrarySearch_grindDischarger___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_LibrarySearch_grindDischarger___closed__1_value),LEAN_SCALAR_PTR_LITERAL(46, 250, 206, 136, 19, 229, 9, 31)}};
static const lean_object* l_Lean_Meta_LibrarySearch_grindDischarger___closed__2 = (const lean_object*)&l_Lean_Meta_LibrarySearch_grindDischarger___closed__2_value;
static const lean_ctor_object l_Lean_Meta_LibrarySearch_grindDischarger___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_LibrarySearch_grindDischarger___closed__3 = (const lean_object*)&l_Lean_Meta_LibrarySearch_grindDischarger___closed__3_value;
static const lean_ctor_object l_Lean_Meta_LibrarySearch_grindDischarger___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*14 + 40, .m_other = 14, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(10000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1048576) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 1, 1, 0, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_LibrarySearch_grindDischarger___closed__4 = (const lean_object*)&l_Lean_Meta_LibrarySearch_grindDischarger___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_grindDischarger(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_grindDischarger___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_tryDischarger___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryDischarger___lam__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_LibrarySearch_tryDischarger___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Try"};
static const lean_object* l_Lean_Meta_LibrarySearch_tryDischarger___closed__0 = (const lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__0_value;
static const lean_ctor_object l_Lean_Meta_LibrarySearch_tryDischarger___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_LibrarySearch_tryDischarger___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__0_value),LEAN_SCALAR_PTR_LITERAL(110, 237, 160, 227, 109, 164, 83, 112)}};
static const lean_ctor_object l_Lean_Meta_LibrarySearch_tryDischarger___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_LibrarySearch_grindDischarger___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 13, 122, 73, 14, 49, 113, 49)}};
static const lean_object* l_Lean_Meta_LibrarySearch_tryDischarger___closed__1 = (const lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__1_value;
static const lean_closure_object l_Lean_Meta_LibrarySearch_tryDischarger___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LibrarySearch_tryDischarger___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_LibrarySearch_tryDischarger___closed__2 = (const lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__2_value;
static const lean_string_object l_Lean_Meta_LibrarySearch_tryDischarger___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Meta_LibrarySearch_tryDischarger___closed__3 = (const lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__3_value;
static const lean_string_object l_Lean_Meta_LibrarySearch_tryDischarger___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "tryTrace"};
static const lean_object* l_Lean_Meta_LibrarySearch_tryDischarger___closed__4 = (const lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__4_value;
static const lean_ctor_object l_Lean_Meta_LibrarySearch_tryDischarger___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_LibrarySearch_tryDischarger___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_LibrarySearch_tryDischarger___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_LibrarySearch_tryDischarger___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__4_value),LEAN_SCALAR_PTR_LITERAL(222, 128, 230, 128, 87, 180, 97, 21)}};
static const lean_object* l_Lean_Meta_LibrarySearch_tryDischarger___closed__5 = (const lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__5_value;
static const lean_string_object l_Lean_Meta_LibrarySearch_tryDischarger___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "try\?"};
static const lean_object* l_Lean_Meta_LibrarySearch_tryDischarger___closed__6 = (const lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__6_value;
static const lean_string_object l_Lean_Meta_LibrarySearch_tryDischarger___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Meta_LibrarySearch_tryDischarger___closed__7 = (const lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__7_value;
static const lean_ctor_object l_Lean_Meta_LibrarySearch_tryDischarger___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_LibrarySearch_tryDischarger___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_LibrarySearch_tryDischarger___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_LibrarySearch_tryDischarger___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__8_value_aux_2),((lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__7_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Meta_LibrarySearch_tryDischarger___closed__8 = (const lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__8_value;
static const lean_string_object l_Lean_Meta_LibrarySearch_tryDischarger___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Meta_LibrarySearch_tryDischarger___closed__9 = (const lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__9_value;
static const lean_ctor_object l_Lean_Meta_LibrarySearch_tryDischarger___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__9_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Meta_LibrarySearch_tryDischarger___closed__10 = (const lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__10_value;
static lean_once_cell_t l_Lean_Meta_LibrarySearch_tryDischarger___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LibrarySearch_tryDischarger___closed__11;
static const lean_array_object l_Lean_Meta_LibrarySearch_tryDischarger___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_LibrarySearch_tryDischarger___closed__12 = (const lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__12_value;
static const lean_ctor_object l_Lean_Meta_LibrarySearch_tryDischarger___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*8 + 16, .m_other = 8, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__12_value),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_LibrarySearch_tryDischarger___closed__13 = (const lean_object*)&l_Lean_Meta_LibrarySearch_tryDischarger___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryDischarger(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryDischarger___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_LibrarySearch_solveByElim___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LibrarySearch_solveByElim___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LibrarySearch_solveByElim___closed__0 = (const lean_object*)&l_Lean_Meta_LibrarySearch_solveByElim___closed__0_value;
static const lean_closure_object l_Lean_Meta_LibrarySearch_solveByElim___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LibrarySearch_solveByElim___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LibrarySearch_solveByElim___closed__1 = (const lean_object*)&l_Lean_Meta_LibrarySearch_solveByElim___closed__1_value;
static const lean_closure_object l_Lean_Meta_LibrarySearch_solveByElim___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LibrarySearch_solveByElim___lam__2___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LibrarySearch_solveByElim___closed__2 = (const lean_object*)&l_Lean_Meta_LibrarySearch_solveByElim___closed__2_value;
static const lean_array_object l_Lean_Meta_LibrarySearch_solveByElim___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_LibrarySearch_solveByElim___closed__3 = (const lean_object*)&l_Lean_Meta_LibrarySearch_solveByElim___closed__3_value;
static const lean_closure_object l_Lean_Meta_LibrarySearch_solveByElim___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LibrarySearch_grindDischarger___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LibrarySearch_solveByElim___closed__4 = (const lean_object*)&l_Lean_Meta_LibrarySearch_solveByElim___closed__4_value;
static const lean_closure_object l_Lean_Meta_LibrarySearch_solveByElim___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LibrarySearch_tryDischarger___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LibrarySearch_solveByElim___closed__5 = (const lean_object*)&l_Lean_Meta_LibrarySearch_solveByElim___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_DeclMod_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_instInhabitedDeclMod_default;
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_instInhabitedDeclMod;
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_LibrarySearch_instOrdDeclMod___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LibrarySearch_instOrdDeclMod___closed__0 = (const lean_object*)&l_Lean_Meta_LibrarySearch_instOrdDeclMod___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_LibrarySearch_instOrdDeclMod = (const lean_object*)&l_Lean_Meta_LibrarySearch_instOrdDeclMod___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_LibrarySearch_instHashableDeclMod___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LibrarySearch_instHashableDeclMod___closed__0 = (const lean_object*)&l_Lean_Meta_LibrarySearch_instHashableDeclMod___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_LibrarySearch_instHashableDeclMod = (const lean_object*)&l_Lean_Meta_LibrarySearch_instHashableDeclMod___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_858108106____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_858108106____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_ext;
static const lean_ctor_object l_Lean_Meta_LibrarySearch_droppedKeys___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_LibrarySearch_droppedKeys___closed__0 = (const lean_object*)&l_Lean_Meta_LibrarySearch_droppedKeys___closed__0_value;
static const lean_string_object l_Lean_Meta_LibrarySearch_droppedKeys___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_LibrarySearch_droppedKeys___closed__1 = (const lean_object*)&l_Lean_Meta_LibrarySearch_droppedKeys___closed__1_value;
static const lean_ctor_object l_Lean_Meta_LibrarySearch_droppedKeys___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_LibrarySearch_droppedKeys___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_LibrarySearch_droppedKeys___closed__2 = (const lean_object*)&l_Lean_Meta_LibrarySearch_droppedKeys___closed__2_value;
static const lean_ctor_object l_Lean_Meta_LibrarySearch_droppedKeys___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_LibrarySearch_droppedKeys___closed__2_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_Meta_LibrarySearch_droppedKeys___closed__3 = (const lean_object*)&l_Lean_Meta_LibrarySearch_droppedKeys___closed__3_value;
static const lean_ctor_object l_Lean_Meta_LibrarySearch_droppedKeys___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)&l_Lean_Meta_LibrarySearch_droppedKeys___closed__0_value)}};
static const lean_object* l_Lean_Meta_LibrarySearch_droppedKeys___closed__4 = (const lean_object*)&l_Lean_Meta_LibrarySearch_droppedKeys___closed__4_value;
static const lean_ctor_object l_Lean_Meta_LibrarySearch_droppedKeys___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)&l_Lean_Meta_LibrarySearch_droppedKeys___closed__4_value)}};
static const lean_object* l_Lean_Meta_LibrarySearch_droppedKeys___closed__5 = (const lean_object*)&l_Lean_Meta_LibrarySearch_droppedKeys___closed__5_value;
static const lean_ctor_object l_Lean_Meta_LibrarySearch_droppedKeys___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_LibrarySearch_droppedKeys___closed__3_value),((lean_object*)&l_Lean_Meta_LibrarySearch_droppedKeys___closed__5_value)}};
static const lean_object* l_Lean_Meta_LibrarySearch_droppedKeys___closed__6 = (const lean_object*)&l_Lean_Meta_LibrarySearch_droppedKeys___closed__6_value;
static const lean_ctor_object l_Lean_Meta_LibrarySearch_droppedKeys___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_LibrarySearch_droppedKeys___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_LibrarySearch_droppedKeys___closed__7 = (const lean_object*)&l_Lean_Meta_LibrarySearch_droppedKeys___closed__7_value;
static const lean_ctor_object l_Lean_Meta_LibrarySearch_droppedKeys___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_LibrarySearch_droppedKeys___closed__0_value),((lean_object*)&l_Lean_Meta_LibrarySearch_droppedKeys___closed__7_value)}};
static const lean_object* l_Lean_Meta_LibrarySearch_droppedKeys___closed__8 = (const lean_object*)&l_Lean_Meta_LibrarySearch_droppedKeys___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_LibrarySearch_droppedKeys = (const lean_object*)&l_Lean_Meta_LibrarySearch_droppedKeys___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_constantsPerImportTask;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2955776588____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2955776588____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt;
static const lean_closure_object l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__0 = (const lean_object*)&l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__0_value;
static lean_once_cell_t l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_libSearchFindDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_libSearchFindDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_LibrarySearch_getStarLemmas___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_LibrarySearch_getStarLemmas___closed__0 = (const lean_object*)&l_Lean_Meta_LibrarySearch_getStarLemmas___closed__0_value;
static const lean_ctor_object l_Lean_Meta_LibrarySearch_getStarLemmas___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_LibrarySearch_getStarLemmas___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Meta_LibrarySearch_getStarLemmas___closed__1 = (const lean_object*)&l_Lean_Meta_LibrarySearch_getStarLemmas___closed__1_value;
static lean_once_cell_t l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2;
static const lean_array_object l_Lean_Meta_LibrarySearch_getStarLemmas___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_LibrarySearch_getStarLemmas___closed__3 = (const lean_object*)&l_Lean_Meta_LibrarySearch_getStarLemmas___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_getStarLemmas(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_getStarLemmas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "abortSpeculation"};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__7_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__10_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(14, 179, 197, 182, 147, 201, 96, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__0_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(221, 180, 178, 73, 239, 82, 182, 211)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_abortSpeculationId;
static lean_once_cell_t l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_isAbortSpeculation(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_isAbortSpeculation___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mp"};
static const lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_ctor_object l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 220, 216, 40, 239, 165, 44, 174)}};
static const lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mpr"};
static const lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_ctor_object l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(14, 81, 9, 215, 230, 198, 87, 3)}};
static const lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__0 = (const lean_object*)&l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__0_value;
static const lean_closure_object l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__1 = (const lean_object*)&l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trying "};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " with mp"};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__7_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " with mpr"};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__10_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_LibrarySearch_tryOnEach___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_LibrarySearch_tryOnEach___closed__0 = (const lean_object*)&l_Lean_Meta_LibrarySearch_tryOnEach___closed__0_value;
static const lean_ctor_object l_Lean_Meta_LibrarySearch_tryOnEach___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_LibrarySearch_tryOnEach___closed__0_value)}};
static const lean_object* l_Lean_Meta_LibrarySearch_tryOnEach___closed__1 = (const lean_object*)&l_Lean_Meta_LibrarySearch_tryOnEach___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryOnEach(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryOnEach___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_LibrarySearch_libSearchFindDecls___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 1, 1, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearch(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__24_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = lean_unsigned_to_nat(4259869437u);
v___x_58_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__23_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_59_ = l_Lean_Name_num___override(v___x_58_, v___x_57_);
return v___x_59_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__26_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__25_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_62_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__24_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__24_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__24_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_);
v___x_63_ = l_Lean_Name_str___override(v___x_62_, v___x_61_);
return v___x_63_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__28_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__27_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_66_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__26_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__26_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__26_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_);
v___x_67_ = l_Lean_Name_str___override(v___x_66_, v___x_65_);
return v___x_67_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__29_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_unsigned_to_nat(2u);
v___x_69_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__28_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__28_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__28_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_);
v___x_70_ = l_Lean_Name_num___override(v___x_69_, v___x_68_);
return v___x_70_;
}
}
lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_72_; uint8_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_72_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_73_ = 0;
v___x_74_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__29_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__29_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__29_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_);
v___x_75_ = l_Lean_registerTraceClass(v___x_72_, v___x_73_, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_76_;
v_res_76_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_();
stack->m_obj
 = v_res_76_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2____boxed(lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_();
return v_res_78_;
}
}
lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_97_; uint8_t v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_97_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_));
v___x_98_ = 0;
v___x_99_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_));
v___x_100_ = l_Lean_registerTraceClass(v___x_97_, v___x_98_, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_101_;
v_res_101_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_();
stack->m_obj
 = v_res_101_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2____boxed(lean_object* v_a_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_();
return v_res_103_;
}
}
lean_object* l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(lean_object* v_x_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___lam__0___closed__0));
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_grindDischarger___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_106_ = stack[0].m_obj;
lean_object* v___y_107_ = stack[1].m_obj;
lean_object* v___y_108_ = stack[2].m_obj;
lean_object* v___y_109_ = stack[3].m_obj;
lean_object* v___y_110_ = stack[4].m_obj;
lean_object* v_res_114_;
v_res_114_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(v_x_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
stack->m_obj
 = v_res_114_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_grindDischarger___lam__0___boxed(lean_object* v_x_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(v_x_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v_x_115_);
return v_res_121_;
}
}
lean_object* l_Lean_Meta_LibrarySearch_grindDischarger(lean_object* v_mvarId_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___y_153_; uint8_t v___y_154_; lean_object* v_a_159_; lean_object* v___y_163_; lean_object* v___x_173_; 
lean_inc(v_mvarId_146_);
v___x_173_ = l_Lean_MVarId_getType(v_mvarId_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; lean_object* v___x_175_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc_n(v_a_174_, 2);
lean_dec_ref_known(v___x_173_, 1);
v___x_175_ = l_Lean_Meta_getLevel(v_a_174_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_a_176_);
lean_dec_ref_known(v___x_175_, 1);
v___x_177_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__2));
v___x_178_ = lean_box(0);
v___x_179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_179_, 0, v_a_176_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = l_Lean_Expr_const___override(v___x_177_, v___x_179_);
v___x_181_ = l_Lean_Expr_app___override(v___x_180_, v_a_174_);
v___x_182_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__3));
v___x_183_ = lean_box(0);
v___x_184_ = l_Lean_MVarId_apply(v_mvarId_146_, v___x_181_, v___x_182_, v___x_183_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_a_185_);
lean_dec_ref_known(v___x_184_, 1);
if (lean_obj_tag(v_a_185_) == 1)
{
lean_object* v_tail_186_; 
v_tail_186_ = lean_ctor_get(v_a_185_, 1);
if (lean_obj_tag(v_tail_186_) == 0)
{
lean_object* v_head_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
lean_inc(v_tail_186_);
v_head_187_ = lean_ctor_get(v_a_185_, 0);
lean_inc(v_head_187_);
lean_dec_ref_known(v_a_185_, 2);
v___x_188_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__4));
v___x_189_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_188_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_211_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_211_ == 0)
{
v___x_192_ = v___x_189_;
v_isShared_193_ = v_isSharedCheck_211_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_189_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_211_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_Meta_Grind_main(v_head_187_, v_a_190_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_209_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_209_ == 0)
{
v___x_197_ = v___x_194_;
v_isShared_198_ = v_isSharedCheck_209_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_194_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_209_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
uint8_t v___x_199_; 
v___x_199_ = l_Lean_Meta_Grind_Result_hasFailed(v_a_195_);
lean_dec(v_a_195_);
if (v___x_199_ == 0)
{
lean_object* v___x_201_; 
if (v_isShared_193_ == 0)
{
lean_ctor_set_tag(v___x_192_, 1);
lean_ctor_set(v___x_192_, 0, v_tail_186_);
v___x_201_ = v___x_192_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_tail_186_);
v___x_201_ = v_reuseFailAlloc_205_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
lean_object* v___x_203_; 
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v___x_201_);
v___x_203_ = v___x_197_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_201_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
else
{
lean_object* v___x_207_; 
lean_del_object(v___x_192_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v___x_183_);
v___x_207_ = v___x_197_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_183_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
else
{
lean_object* v_a_210_; 
lean_del_object(v___x_192_);
v_a_210_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_a_210_);
lean_dec_ref_known(v___x_194_, 1);
v_a_159_ = v_a_210_;
goto v___jp_158_;
}
}
}
else
{
lean_object* v_a_212_; 
lean_dec(v_head_187_);
v_a_212_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_a_212_);
lean_dec_ref_known(v___x_189_, 1);
v_a_159_ = v_a_212_;
goto v___jp_158_;
}
}
else
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(v_a_185_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
lean_dec_ref_known(v_a_185_, 2);
v___y_163_ = v___x_213_;
goto v___jp_162_;
}
}
else
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(v_a_185_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
lean_dec(v_a_185_);
v___y_163_ = v___x_214_;
goto v___jp_162_;
}
}
else
{
lean_object* v_a_215_; 
v_a_215_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_a_215_);
lean_dec_ref_known(v___x_184_, 1);
v_a_159_ = v_a_215_;
goto v___jp_158_;
}
}
else
{
lean_object* v_a_216_; 
lean_dec(v_a_174_);
lean_dec(v_mvarId_146_);
v_a_216_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_a_216_);
lean_dec_ref_known(v___x_175_, 1);
v_a_159_ = v_a_216_;
goto v___jp_158_;
}
}
else
{
lean_object* v_a_217_; 
lean_dec(v_mvarId_146_);
v_a_217_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_a_217_);
lean_dec_ref_known(v___x_173_, 1);
v_a_159_ = v_a_217_;
goto v___jp_158_;
}
v___jp_152_:
{
if (v___y_154_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; 
lean_dec_ref(v___y_153_);
v___x_155_ = lean_box(0);
v___x_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
return v___x_156_;
}
else
{
lean_object* v___x_157_; 
v___x_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_157_, 0, v___y_153_);
return v___x_157_;
}
}
v___jp_158_:
{
uint8_t v___x_160_; 
v___x_160_ = l_Lean_Exception_isInterrupt(v_a_159_);
if (v___x_160_ == 0)
{
uint8_t v___x_161_; 
lean_inc_ref(v_a_159_);
v___x_161_ = l_Lean_Exception_isRuntime(v_a_159_);
v___y_153_ = v_a_159_;
v___y_154_ = v___x_161_;
goto v___jp_152_;
}
else
{
v___y_153_ = v_a_159_;
v___y_154_ = v___x_160_;
goto v___jp_152_;
}
}
v___jp_162_:
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_172_; 
v_a_164_ = lean_ctor_get(v___y_163_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___y_163_);
if (v_isSharedCheck_172_ == 0)
{
v___x_166_ = v___y_163_;
v_isShared_167_ = v_isSharedCheck_172_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___y_163_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_172_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v_a_168_; lean_object* v___x_170_; 
v_a_168_ = lean_ctor_get(v_a_164_, 0);
lean_inc(v_a_168_);
lean_dec(v_a_164_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 0, v_a_168_);
v___x_170_ = v___x_166_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_grindDischarger_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_146_ = stack[0].m_obj;
lean_object* v_a_147_ = stack[1].m_obj;
lean_object* v_a_148_ = stack[2].m_obj;
lean_object* v_a_149_ = stack[3].m_obj;
lean_object* v_a_150_ = stack[4].m_obj;
lean_object* v_res_218_;
v_res_218_ = l_Lean_Meta_LibrarySearch_grindDischarger(v_mvarId_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
stack->m_obj
 = v_res_218_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_grindDischarger___boxed(lean_object* v_mvarId_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Meta_LibrarySearch_grindDischarger(v_mvarId_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
return v_res_225_;
}
}
uint8_t l_Lean_Meta_LibrarySearch_tryDischarger___lam__1(uint8_t v___x_226_, lean_object* v_x_227_){
_start:
{
return v___x_226_;
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_tryDischarger___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_226_ = stack[0].m_num;
lean_object* v_x_227_ = stack[1].m_obj;
uint8_t v_res_228_;
v_res_228_ = l_Lean_Meta_LibrarySearch_tryDischarger___lam__1(v___x_226_, v_x_227_);
stack->m_num = v_res_228_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryDischarger___lam__1___boxed(lean_object* v___x_229_, lean_object* v_x_230_){
_start:
{
uint8_t v___x_3817__boxed_231_; uint8_t v_res_232_; lean_object* v_r_233_; 
v___x_3817__boxed_231_ = lean_unbox(v___x_229_);
v_res_232_ = l_Lean_Meta_LibrarySearch_tryDischarger___lam__1(v___x_3817__boxed_231_, v_x_230_);
lean_dec(v_x_230_);
v_r_233_ = lean_box(v_res_232_);
return v_r_233_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_tryDischarger___closed__11(void){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Array_mkArray0___redArg();
return v___x_259_;
}
}
lean_object* l_Lean_Meta_LibrarySearch_tryDischarger(lean_object* v_mvarId_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v___y_277_; uint8_t v___y_278_; lean_object* v_a_283_; lean_object* v___y_287_; lean_object* v___x_297_; 
lean_inc(v_mvarId_270_);
v___x_297_ = l_Lean_MVarId_getType(v_mvarId_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v_a_298_; lean_object* v___x_299_; 
v_a_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc_n(v_a_298_, 2);
lean_dec_ref_known(v___x_297_, 1);
v___x_299_ = l_Lean_Meta_getLevel(v_a_298_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_a_300_);
lean_dec_ref_known(v___x_299_, 1);
v___x_301_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__1));
v___x_302_ = lean_box(0);
v___x_303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_303_, 0, v_a_300_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___x_304_ = l_Lean_Expr_const___override(v___x_301_, v___x_303_);
v___x_305_ = l_Lean_Expr_app___override(v___x_304_, v_a_298_);
v___x_306_ = 0;
v___x_307_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__3));
v___x_308_ = lean_box(0);
v___x_309_ = l_Lean_MVarId_apply(v_mvarId_270_, v___x_305_, v___x_307_, v___x_308_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_360_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_360_ == 0)
{
v___x_312_ = v___x_309_;
v_isShared_313_ = v_isSharedCheck_360_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_309_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_360_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
if (lean_obj_tag(v_a_310_) == 1)
{
lean_object* v_tail_314_; 
v_tail_314_ = lean_ctor_get(v_a_310_, 1);
if (lean_obj_tag(v_tail_314_) == 0)
{
lean_object* v_head_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_356_; 
lean_inc(v_tail_314_);
v_head_315_ = lean_ctor_get(v_a_310_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v_a_310_);
if (v_isSharedCheck_356_ == 0)
{
lean_object* v_unused_357_; 
v_unused_357_ = lean_ctor_get(v_a_310_, 1);
lean_dec(v_unused_357_);
v___x_317_ = v_a_310_;
v_isShared_318_ = v_isSharedCheck_356_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_head_315_);
lean_dec(v_a_310_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_356_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v_ref_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
v_ref_319_ = lean_ctor_get(v_a_273_, 2);
v___x_320_ = l_Lean_SourceInfo_fromRef(v_ref_319_, v___x_306_);
v___x_321_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__5));
v___x_322_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__6));
lean_inc(v___x_320_);
if (v_isShared_318_ == 0)
{
lean_ctor_set_tag(v___x_317_, 2);
lean_ctor_set(v___x_317_, 1, v___x_322_);
lean_ctor_set(v___x_317_, 0, v___x_320_);
v___x_324_ = v___x_317_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v___x_322_);
v___x_324_ = v_reuseFailAlloc_355_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_325_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__8));
v___x_326_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__10));
v___x_327_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_tryDischarger___closed__11, &l_Lean_Meta_LibrarySearch_tryDischarger___closed__11_once, _init_l_Lean_Meta_LibrarySearch_tryDischarger___closed__11);
lean_inc_n(v___x_320_, 2);
v___x_328_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_328_, 0, v___x_320_);
lean_ctor_set(v___x_328_, 1, v___x_326_);
lean_ctor_set(v___x_328_, 2, v___x_327_);
v___x_329_ = l_Lean_Syntax_node1(v___x_320_, v___x_325_, v___x_328_);
v___x_330_ = l_Lean_Syntax_node2(v___x_320_, v___x_321_, v___x_324_, v___x_329_);
v___x_331_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_331_, 0, v___x_330_);
v___x_332_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSuppressedMessages___boxed), 11, 2);
lean_closure_set(v___x_332_, 0, lean_box(0));
lean_closure_set(v___x_332_, 1, v___x_331_);
v___x_333_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___boxed), 9, 2);
lean_closure_set(v___x_333_, 0, v_head_315_);
lean_closure_set(v___x_333_, 1, v___x_332_);
v___x_334_ = lean_box(1);
v___x_335_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__13));
v___x_336_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_336_, 0, v___x_302_);
lean_ctor_set(v___x_336_, 1, v___x_334_);
lean_ctor_set(v___x_336_, 2, v_tail_314_);
lean_ctor_set(v___x_336_, 3, v___x_302_);
lean_ctor_set(v___x_336_, 4, v___x_302_);
lean_ctor_set(v___x_336_, 5, v___x_334_);
lean_ctor_set(v___x_336_, 6, v___x_302_);
v___x_337_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_333_, v___x_335_, v___x_336_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_353_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_353_ == 0)
{
v___x_340_ = v___x_337_;
v_isShared_341_ = v_isSharedCheck_353_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_353_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v_fst_342_; uint8_t v___x_343_; 
v_fst_342_ = lean_ctor_get(v_a_338_, 0);
lean_inc(v_fst_342_);
lean_dec(v_a_338_);
v___x_343_ = l_List_isEmpty___redArg(v_fst_342_);
lean_dec(v_fst_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_345_; 
lean_del_object(v___x_312_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_308_);
v___x_345_ = v___x_340_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_308_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
else
{
lean_object* v___x_348_; 
if (v_isShared_313_ == 0)
{
lean_ctor_set_tag(v___x_312_, 1);
lean_ctor_set(v___x_312_, 0, v_tail_314_);
v___x_348_ = v___x_312_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_tail_314_);
v___x_348_ = v_reuseFailAlloc_352_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
lean_object* v___x_350_; 
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_348_);
v___x_350_ = v___x_340_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
else
{
lean_object* v_a_354_; 
lean_del_object(v___x_312_);
v_a_354_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_354_);
lean_dec_ref_known(v___x_337_, 1);
v_a_283_ = v_a_354_;
goto v___jp_282_;
}
}
}
}
else
{
lean_object* v___x_358_; 
lean_del_object(v___x_312_);
v___x_358_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(v_a_310_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
lean_dec_ref_known(v_a_310_, 2);
v___y_287_ = v___x_358_;
goto v___jp_286_;
}
}
else
{
lean_object* v___x_359_; 
lean_del_object(v___x_312_);
v___x_359_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(v_a_310_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
lean_dec(v_a_310_);
v___y_287_ = v___x_359_;
goto v___jp_286_;
}
}
}
else
{
lean_object* v_a_361_; 
v_a_361_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_a_361_);
lean_dec_ref_known(v___x_309_, 1);
v_a_283_ = v_a_361_;
goto v___jp_282_;
}
}
else
{
lean_object* v_a_362_; 
lean_dec(v_a_298_);
lean_dec(v_mvarId_270_);
v_a_362_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_a_362_);
lean_dec_ref_known(v___x_299_, 1);
v_a_283_ = v_a_362_;
goto v___jp_282_;
}
}
else
{
lean_object* v_a_363_; 
lean_dec(v_mvarId_270_);
v_a_363_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_a_363_);
lean_dec_ref_known(v___x_297_, 1);
v_a_283_ = v_a_363_;
goto v___jp_282_;
}
v___jp_276_:
{
if (v___y_278_ == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; 
lean_dec_ref(v___y_277_);
v___x_279_ = lean_box(0);
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
else
{
lean_object* v___x_281_; 
v___x_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_281_, 0, v___y_277_);
return v___x_281_;
}
}
v___jp_282_:
{
uint8_t v___x_284_; 
v___x_284_ = l_Lean_Exception_isInterrupt(v_a_283_);
if (v___x_284_ == 0)
{
uint8_t v___x_285_; 
lean_inc_ref(v_a_283_);
v___x_285_ = l_Lean_Exception_isRuntime(v_a_283_);
v___y_277_ = v_a_283_;
v___y_278_ = v___x_285_;
goto v___jp_276_;
}
else
{
v___y_277_ = v_a_283_;
v___y_278_ = v___x_284_;
goto v___jp_276_;
}
}
v___jp_286_:
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_296_; 
v_a_288_ = lean_ctor_get(v___y_287_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___y_287_);
if (v_isSharedCheck_296_ == 0)
{
v___x_290_ = v___y_287_;
v_isShared_291_ = v_isSharedCheck_296_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___y_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_296_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v_a_292_; lean_object* v___x_294_; 
v_a_292_ = lean_ctor_get(v_a_288_, 0);
lean_inc(v_a_292_);
lean_dec(v_a_288_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v_a_292_);
v___x_294_ = v___x_290_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_tryDischarger_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_270_ = stack[0].m_obj;
lean_object* v_a_271_ = stack[1].m_obj;
lean_object* v_a_272_ = stack[2].m_obj;
lean_object* v_a_273_ = stack[3].m_obj;
lean_object* v_a_274_ = stack[4].m_obj;
lean_object* v_res_364_;
v_res_364_ = l_Lean_Meta_LibrarySearch_tryDischarger(v_mvarId_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
stack->m_obj
 = v_res_364_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryDischarger___boxed(lean_object* v_mvarId_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Meta_LibrarySearch_tryDischarger(v_mvarId_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
return v_res_371_;
}
}
lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__0(lean_object* v_x_372_, lean_object* v_x_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_box(0);
v___x_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_solveByElim___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_372_ = stack[0].m_obj;
lean_object* v_x_373_ = stack[1].m_obj;
lean_object* v___y_374_ = stack[2].m_obj;
lean_object* v___y_375_ = stack[3].m_obj;
lean_object* v___y_376_ = stack[4].m_obj;
lean_object* v___y_377_ = stack[5].m_obj;
lean_object* v_res_381_;
v_res_381_ = l_Lean_Meta_LibrarySearch_solveByElim___lam__0(v_x_372_, v_x_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
stack->m_obj
 = v_res_381_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__0___boxed(lean_object* v_x_382_, lean_object* v_x_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Meta_LibrarySearch_solveByElim___lam__0(v_x_382_, v_x_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v_x_383_);
lean_dec(v_x_382_);
return v_res_389_;
}
}
lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__1(lean_object* v_x_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
uint8_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_396_ = 0;
v___x_397_ = lean_box(v___x_396_);
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_solveByElim___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_390_ = stack[0].m_obj;
lean_object* v___y_391_ = stack[1].m_obj;
lean_object* v___y_392_ = stack[2].m_obj;
lean_object* v___y_393_ = stack[3].m_obj;
lean_object* v___y_394_ = stack[4].m_obj;
lean_object* v_res_399_;
v_res_399_ = l_Lean_Meta_LibrarySearch_solveByElim___lam__1(v_x_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
stack->m_obj
 = v_res_399_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__1___boxed(lean_object* v_x_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_Meta_LibrarySearch_solveByElim___lam__1(v_x_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v_x_400_);
return v_res_406_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(lean_object* v_msgData_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v___x_413_; lean_object* v_env_414_; uint8_t v___x_415_; lean_object* v_env_416_; lean_object* v___x_417_; lean_object* v_toCold_418_; lean_object* v_mctx_419_; lean_object* v_lctx_420_; lean_object* v_options_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_413_ = lean_st_ref_get(v___y_411_);
v_env_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc_ref(v_env_414_);
lean_dec(v___x_413_);
v___x_415_ = 0;
v_env_416_ = l_Lean_Environment_setRecordingDeps(v_env_414_, v___x_415_);
v___x_417_ = lean_st_ref_get(v___y_409_);
v_toCold_418_ = lean_ctor_get(v___y_410_, 0);
v_mctx_419_ = lean_ctor_get(v___x_417_, 0);
lean_inc_ref(v_mctx_419_);
lean_dec(v___x_417_);
v_lctx_420_ = lean_ctor_get(v___y_408_, 2);
v_options_421_ = lean_ctor_get(v_toCold_418_, 2);
lean_inc_ref(v_options_421_);
lean_inc_ref(v_lctx_420_);
v___x_422_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_422_, 0, v_env_416_);
lean_ctor_set(v___x_422_, 1, v_mctx_419_);
lean_ctor_set(v___x_422_, 2, v_lctx_420_);
lean_ctor_set(v___x_422_, 3, v_options_421_);
v___x_423_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v_msgData_407_);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_407_ = stack[0].m_obj;
lean_object* v___y_408_ = stack[1].m_obj;
lean_object* v___y_409_ = stack[2].m_obj;
lean_object* v___y_410_ = stack[3].m_obj;
lean_object* v___y_411_ = stack[4].m_obj;
lean_object* v_res_425_;
v_res_425_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msgData_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
stack->m_obj
 = v_res_425_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0___boxed(lean_object* v_msgData_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msgData_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
return v_res_432_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(lean_object* v_msg_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_ref_439_; lean_object* v___x_440_; lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_449_; 
v_ref_439_ = lean_ctor_get(v___y_436_, 2);
v___x_440_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msg_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
v_a_441_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_449_ == 0)
{
v___x_443_ = v___x_440_;
v_isShared_444_ = v_isSharedCheck_449_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_440_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_449_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; lean_object* v___x_447_; 
lean_inc(v_ref_439_);
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v_ref_439_);
lean_ctor_set(v___x_445_, 1, v_a_441_);
if (v_isShared_444_ == 0)
{
lean_ctor_set_tag(v___x_443_, 1);
lean_ctor_set(v___x_443_, 0, v___x_445_);
v___x_447_ = v___x_443_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_433_ = stack[0].m_obj;
lean_object* v___y_434_ = stack[1].m_obj;
lean_object* v___y_435_ = stack[2].m_obj;
lean_object* v___y_436_ = stack[3].m_obj;
lean_object* v___y_437_ = stack[4].m_obj;
lean_object* v_res_450_;
v_res_450_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v_msg_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
stack->m_obj
 = v_res_450_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg___boxed(lean_object* v_msg_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v_msg_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
return v_res_457_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__0));
v___x_460_ = l_Lean_stringToMessageData(v___x_459_);
return v___x_460_;
}
}
lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__2(lean_object* v_x_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1);
v___x_468_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_467_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
return v___x_468_;
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_solveByElim___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_461_ = stack[0].m_obj;
lean_object* v___y_462_ = stack[1].m_obj;
lean_object* v___y_463_ = stack[2].m_obj;
lean_object* v___y_464_ = stack[3].m_obj;
lean_object* v___y_465_ = stack[4].m_obj;
lean_object* v_res_469_;
v_res_469_ = l_Lean_Meta_LibrarySearch_solveByElim___lam__2(v_x_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
stack->m_obj
 = v_res_469_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__2___boxed(lean_object* v_x_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_Meta_LibrarySearch_solveByElim___lam__2(v_x_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v_x_470_);
return v_res_476_;
}
}
lean_object* l_Lean_Meta_LibrarySearch_solveByElim(lean_object* v_required_484_, uint8_t v_exfalso_485_, lean_object* v_goals_486_, lean_object* v_maxDepth_487_, uint8_t v_grind_488_, uint8_t v_try_x3f_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v___x_495_; uint8_t v_transparency_496_; lean_object* v___f_497_; lean_object* v___f_498_; lean_object* v___f_499_; uint8_t v___x_500_; lean_object* v___x_501_; uint8_t v___x_502_; lean_object* v___y_504_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_495_ = l_Lean_Meta_Context_config(v_a_490_);
v_transparency_496_ = lean_ctor_get_uint8(v___x_495_, 9);
lean_dec_ref(v___x_495_);
v___f_497_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__0));
v___f_498_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__1));
v___f_499_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__2));
v___x_500_ = 1;
v___x_501_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_501_, 0, v_maxDepth_487_);
lean_ctor_set(v___x_501_, 1, v___f_497_);
lean_ctor_set(v___x_501_, 2, v___f_498_);
lean_ctor_set(v___x_501_, 3, v___f_499_);
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*4, v___x_500_);
v___x_502_ = 0;
v___x_523_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__3));
v___x_524_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_524_, 0, v___x_501_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
lean_ctor_set_uint8(v___x_524_, sizeof(void*)*2, v_transparency_496_);
lean_ctor_set_uint8(v___x_524_, sizeof(void*)*2 + 1, v___x_500_);
lean_ctor_set_uint8(v___x_524_, sizeof(void*)*2 + 2, v_exfalso_485_);
v___x_525_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_525_, 0, v___x_524_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*1, v___x_500_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*1 + 1, v___x_500_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*1 + 2, v___x_502_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*1 + 3, v___x_502_);
if (v_try_x3f_489_ == 0)
{
if (v_grind_488_ == 0)
{
v___y_504_ = v___x_525_;
goto v___jp_503_;
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__4));
v___x_527_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v___x_525_, v___x_526_);
v___y_504_ = v___x_527_;
goto v___jp_503_;
}
}
else
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__5));
v___x_529_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v___x_525_, v___x_528_);
v___y_504_ = v___x_529_;
goto v___jp_503_;
}
v___jp_503_:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_505_ = lean_box(0);
v___x_506_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__3));
v___x_507_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v___x_502_, v___x_502_, v___x_505_, v___x_505_, v___x_506_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v_fst_509_; lean_object* v_snd_510_; uint8_t v___x_511_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
lean_dec_ref_known(v___x_507_, 1);
v_fst_509_ = lean_ctor_get(v_a_508_, 0);
lean_inc(v_fst_509_);
v_snd_510_ = lean_ctor_get(v_a_508_, 1);
lean_inc(v_snd_510_);
lean_dec(v_a_508_);
v___x_511_ = l_List_isEmpty___redArg(v_required_484_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(v___y_504_, v_required_484_);
v___x_513_ = l_Lean_Meta_SolveByElim_solveByElim(v___x_512_, v_fst_509_, v_snd_510_, v_goals_486_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
return v___x_513_;
}
else
{
lean_object* v___x_514_; 
lean_dec(v_required_484_);
v___x_514_ = l_Lean_Meta_SolveByElim_solveByElim(v___y_504_, v_fst_509_, v_snd_510_, v_goals_486_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
return v___x_514_;
}
}
else
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
lean_dec_ref(v___y_504_);
lean_dec(v_goals_486_);
lean_dec(v_required_484_);
v_a_515_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_507_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_507_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_solveByElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_required_484_ = stack[0].m_obj;
uint8_t v_exfalso_485_ = stack[1].m_num;
lean_object* v_goals_486_ = stack[2].m_obj;
lean_object* v_maxDepth_487_ = stack[3].m_obj;
uint8_t v_grind_488_ = stack[4].m_num;
uint8_t v_try_x3f_489_ = stack[5].m_num;
lean_object* v_a_490_ = stack[6].m_obj;
lean_object* v_a_491_ = stack[7].m_obj;
lean_object* v_a_492_ = stack[8].m_obj;
lean_object* v_a_493_ = stack[9].m_obj;
lean_object* v_res_530_;
v_res_530_ = l_Lean_Meta_LibrarySearch_solveByElim(v_required_484_, v_exfalso_485_, v_goals_486_, v_maxDepth_487_, v_grind_488_, v_try_x3f_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
stack->m_obj
 = v_res_530_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___boxed(lean_object* v_required_531_, lean_object* v_exfalso_532_, lean_object* v_goals_533_, lean_object* v_maxDepth_534_, lean_object* v_grind_535_, lean_object* v_try_x3f_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_){
_start:
{
uint8_t v_exfalso_boxed_542_; uint8_t v_grind_boxed_543_; uint8_t v_try_x3f_boxed_544_; lean_object* v_res_545_; 
v_exfalso_boxed_542_ = lean_unbox(v_exfalso_532_);
v_grind_boxed_543_ = lean_unbox(v_grind_535_);
v_try_x3f_boxed_544_ = lean_unbox(v_try_x3f_536_);
v_res_545_ = l_Lean_Meta_LibrarySearch_solveByElim(v_required_531_, v_exfalso_boxed_542_, v_goals_533_, v_maxDepth_534_, v_grind_boxed_543_, v_try_x3f_boxed_544_, v_a_537_, v_a_538_, v_a_539_, v_a_540_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
return v_res_545_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0(lean_object* v_00_u03b1_546_, lean_object* v_msg_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v_msg_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
return v___x_553_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_547_ = stack[1].m_obj;
lean_object* v___y_548_ = stack[2].m_obj;
lean_object* v___y_549_ = stack[3].m_obj;
lean_object* v___y_550_ = stack[4].m_obj;
lean_object* v___y_551_ = stack[5].m_obj;
lean_object* v_res_554_;
v_res_554_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0(lean_box(0), v_msg_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
stack->m_obj
 = v_res_554_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___boxed(lean_object* v_00_u03b1_555_, lean_object* v_msg_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0(v_00_u03b1_555_, v_msg_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_562_;
}
}
lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx___impl(uint8_t v_x_563_){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_box(v_x_563_);
v___x_565_ = lean_obj_tag_nat(v___x_564_);
lean_dec(v___x_564_);
return v___x_565_;
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_563_ = stack[0].m_num;
lean_object* v_res_566_;
v_res_566_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx___impl(v_x_563_);
stack->m_obj
 = v_res_566_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx___impl___boxed(lean_object* v_x_567_){
_start:
{
uint8_t v_x_4__boxed_568_; lean_object* v_res_569_; 
v_x_4__boxed_568_ = lean_unbox(v_x_567_);
v_res_569_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx___impl(v_x_4__boxed_568_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg(lean_object* v_k_570_){
_start:
{
lean_inc(v_k_570_);
return v_k_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg___boxed(lean_object* v_k_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg(v_k_571_);
lean_dec(v_k_571_);
return v_res_572_;
}
}
lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim(lean_object* v_motive_573_, lean_object* v_ctorIdx_574_, uint8_t v_t_575_, lean_object* v_h_576_, lean_object* v_k_577_){
_start:
{
lean_inc(v_k_577_);
return v_k_577_;
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_DeclMod_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_574_ = stack[1].m_obj;
uint8_t v_t_575_ = stack[2].m_num;
lean_object* v_k_577_ = stack[4].m_obj;
lean_object* v_res_578_;
v_res_578_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorElim(lean_box(0), v_ctorIdx_574_, v_t_575_, lean_box(0), v_k_577_);
stack->m_obj
 = v_res_578_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___boxed(lean_object* v_motive_579_, lean_object* v_ctorIdx_580_, lean_object* v_t_581_, lean_object* v_h_582_, lean_object* v_k_583_){
_start:
{
uint8_t v_t_boxed_584_; lean_object* v_res_585_; 
v_t_boxed_584_ = lean_unbox(v_t_581_);
v_res_585_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorElim(v_motive_579_, v_ctorIdx_580_, v_t_boxed_584_, v_h_582_, v_k_583_);
lean_dec(v_k_583_);
lean_dec(v_ctorIdx_580_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg(lean_object* v_none_586_){
_start:
{
lean_inc(v_none_586_);
return v_none_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg___boxed(lean_object* v_none_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg(v_none_587_);
lean_dec(v_none_587_);
return v_res_588_;
}
}
lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim(lean_object* v_motive_589_, uint8_t v_t_590_, lean_object* v_h_591_, lean_object* v_none_592_){
_start:
{
lean_inc(v_none_592_);
return v_none_592_;
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_DeclMod_none_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_590_ = stack[1].m_num;
lean_object* v_none_592_ = stack[3].m_obj;
lean_object* v_res_593_;
v_res_593_ = l_Lean_Meta_LibrarySearch_DeclMod_none_elim(lean_box(0), v_t_590_, lean_box(0), v_none_592_);
stack->m_obj
 = v_res_593_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___boxed(lean_object* v_motive_594_, lean_object* v_t_595_, lean_object* v_h_596_, lean_object* v_none_597_){
_start:
{
uint8_t v_t_boxed_598_; lean_object* v_res_599_; 
v_t_boxed_598_ = lean_unbox(v_t_595_);
v_res_599_ = l_Lean_Meta_LibrarySearch_DeclMod_none_elim(v_motive_594_, v_t_boxed_598_, v_h_596_, v_none_597_);
lean_dec(v_none_597_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg(lean_object* v_mp_600_){
_start:
{
lean_inc(v_mp_600_);
return v_mp_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg___boxed(lean_object* v_mp_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg(v_mp_601_);
lean_dec(v_mp_601_);
return v_res_602_;
}
}
lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim(lean_object* v_motive_603_, uint8_t v_t_604_, lean_object* v_h_605_, lean_object* v_mp_606_){
_start:
{
lean_inc(v_mp_606_);
return v_mp_606_;
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_DeclMod_mp_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_604_ = stack[1].m_num;
lean_object* v_mp_606_ = stack[3].m_obj;
lean_object* v_res_607_;
v_res_607_ = l_Lean_Meta_LibrarySearch_DeclMod_mp_elim(lean_box(0), v_t_604_, lean_box(0), v_mp_606_);
stack->m_obj
 = v_res_607_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___boxed(lean_object* v_motive_608_, lean_object* v_t_609_, lean_object* v_h_610_, lean_object* v_mp_611_){
_start:
{
uint8_t v_t_boxed_612_; lean_object* v_res_613_; 
v_t_boxed_612_ = lean_unbox(v_t_609_);
v_res_613_ = l_Lean_Meta_LibrarySearch_DeclMod_mp_elim(v_motive_608_, v_t_boxed_612_, v_h_610_, v_mp_611_);
lean_dec(v_mp_611_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg(lean_object* v_mpr_614_){
_start:
{
lean_inc(v_mpr_614_);
return v_mpr_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg___boxed(lean_object* v_mpr_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg(v_mpr_615_);
lean_dec(v_mpr_615_);
return v_res_616_;
}
}
lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim(lean_object* v_motive_617_, uint8_t v_t_618_, lean_object* v_h_619_, lean_object* v_mpr_620_){
_start:
{
lean_inc(v_mpr_620_);
return v_mpr_620_;
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_618_ = stack[1].m_num;
lean_object* v_mpr_620_ = stack[3].m_obj;
lean_object* v_res_621_;
v_res_621_ = l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim(lean_box(0), v_t_618_, lean_box(0), v_mpr_620_);
stack->m_obj
 = v_res_621_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___boxed(lean_object* v_motive_622_, lean_object* v_t_623_, lean_object* v_h_624_, lean_object* v_mpr_625_){
_start:
{
uint8_t v_t_boxed_626_; lean_object* v_res_627_; 
v_t_boxed_626_ = lean_unbox(v_t_623_);
v_res_627_ = l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim(v_motive_622_, v_t_boxed_626_, v_h_624_, v_mpr_625_);
lean_dec(v_mpr_625_);
return v_res_627_;
}
}
uint8_t l_Lean_Meta_LibrarySearch_DeclMod_ofNat(lean_object* v_n_628_){
_start:
{
lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = lean_nat_dec_le(v_n_628_, v___x_629_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_631_ = lean_unsigned_to_nat(1u);
v___x_632_ = lean_nat_dec_le(v_n_628_, v___x_631_);
if (v___x_632_ == 0)
{
uint8_t v___x_633_; 
v___x_633_ = 2;
return v___x_633_;
}
else
{
uint8_t v___x_634_; 
v___x_634_ = 1;
return v___x_634_;
}
}
else
{
uint8_t v___x_635_; 
v___x_635_ = 0;
return v___x_635_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_DeclMod_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_628_ = stack[0].m_obj;
uint8_t v_res_636_;
v_res_636_ = l_Lean_Meta_LibrarySearch_DeclMod_ofNat(v_n_628_);
stack->m_num = v_res_636_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ofNat___boxed(lean_object* v_n_637_){
_start:
{
uint8_t v_res_638_; lean_object* v_r_639_; 
v_res_638_ = l_Lean_Meta_LibrarySearch_DeclMod_ofNat(v_n_637_);
lean_dec(v_n_637_);
v_r_639_ = lean_box(v_res_638_);
return v_r_639_;
}
}
uint8_t l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod(uint8_t v_x_640_, uint8_t v_y_641_){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_642_ = lean_box(v_x_640_);
v___x_643_ = lean_obj_tag_nat(v___x_642_);
lean_dec(v___x_642_);
v___x_644_ = lean_box(v_y_641_);
v___x_645_ = lean_obj_tag_nat(v___x_644_);
lean_dec(v___x_644_);
v___x_646_ = lean_nat_dec_eq(v___x_643_, v___x_645_);
return v___x_646_;
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_640_ = stack[0].m_num;
uint8_t v_y_641_ = stack[1].m_num;
uint8_t v_res_647_;
v_res_647_ = l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod(v_x_640_, v_y_641_);
stack->m_num = v_res_647_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod___boxed(lean_object* v_x_648_, lean_object* v_y_649_){
_start:
{
uint8_t v_x_23__boxed_650_; uint8_t v_y_24__boxed_651_; uint8_t v_res_652_; lean_object* v_r_653_; 
v_x_23__boxed_650_ = lean_unbox(v_x_648_);
v_y_24__boxed_651_ = lean_unbox(v_y_649_);
v_res_652_ = l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod(v_x_23__boxed_650_, v_y_24__boxed_651_);
v_r_653_ = lean_box(v_res_652_);
return v_r_653_;
}
}
static uint8_t _init_l_Lean_Meta_LibrarySearch_instInhabitedDeclMod_default(void){
_start:
{
uint8_t v___x_654_; 
v___x_654_ = 0;
return v___x_654_;
}
}
static uint8_t _init_l_Lean_Meta_LibrarySearch_instInhabitedDeclMod(void){
_start:
{
uint8_t v___x_655_; 
v___x_655_ = 0;
return v___x_655_;
}
}
uint8_t l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord(uint8_t v_x_656_, uint8_t v_y_657_){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_658_ = lean_box(v_x_656_);
v___x_659_ = lean_obj_tag_nat(v___x_658_);
lean_dec(v___x_658_);
v___x_660_ = lean_box(v_y_657_);
v___x_661_ = lean_obj_tag_nat(v___x_660_);
lean_dec(v___x_660_);
v___x_662_ = lean_nat_dec_lt(v___x_659_, v___x_661_);
if (v___x_662_ == 0)
{
uint8_t v___x_663_; 
v___x_663_ = lean_nat_dec_eq(v___x_659_, v___x_661_);
if (v___x_663_ == 0)
{
uint8_t v___x_664_; 
v___x_664_ = 2;
return v___x_664_;
}
else
{
uint8_t v___x_665_; 
v___x_665_ = 1;
return v___x_665_;
}
}
else
{
uint8_t v___x_666_; 
v___x_666_ = 0;
return v___x_666_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_656_ = stack[0].m_num;
uint8_t v_y_657_ = stack[1].m_num;
uint8_t v_res_667_;
v_res_667_ = l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord(v_x_656_, v_y_657_);
stack->m_num = v_res_667_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord___boxed(lean_object* v_x_668_, lean_object* v_y_669_){
_start:
{
uint8_t v_x_33__boxed_670_; uint8_t v_y_34__boxed_671_; uint8_t v_res_672_; lean_object* v_r_673_; 
v_x_33__boxed_670_ = lean_unbox(v_x_668_);
v_y_34__boxed_671_ = lean_unbox(v_y_669_);
v_res_672_ = l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord(v_x_33__boxed_670_, v_y_34__boxed_671_);
v_r_673_ = lean_box(v_res_672_);
return v_r_673_;
}
}
uint64_t l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash(uint8_t v_x_676_){
_start:
{
switch(v_x_676_)
{
case 0:
{
uint64_t v___x_677_; 
v___x_677_ = 0ULL;
return v___x_677_;
}
case 1:
{
uint64_t v___x_678_; 
v___x_678_ = 1ULL;
return v___x_678_;
}
default: 
{
uint64_t v___x_679_; 
v___x_679_ = 2ULL;
return v___x_679_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_676_ = stack[0].m_num;
uint64_t v_res_680_;
v_res_680_ = l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash(v_x_676_);
stack->m_num = v_res_680_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash___boxed(lean_object* v_x_681_){
_start:
{
uint8_t v_x_40__boxed_682_; uint64_t v_res_683_; lean_object* v_r_684_; 
v_x_40__boxed_682_ = lean_unbox(v_x_681_);
v_res_683_ = l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash(v_x_40__boxed_682_);
v_r_684_ = lean_box_uint64(v_res_683_);
return v_r_684_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0(lean_object* v_k_687_, lean_object* v_b_688_, lean_object* v_c_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v___x_695_; 
lean_inc(v___y_693_);
lean_inc_ref(v___y_692_);
lean_inc(v___y_691_);
lean_inc_ref(v___y_690_);
v___x_695_ = lean_apply_7(v_k_687_, v_b_688_, v_c_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, lean_box(0));
return v___x_695_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_687_ = stack[0].m_obj;
lean_object* v_b_688_ = stack[1].m_obj;
lean_object* v_c_689_ = stack[2].m_obj;
lean_object* v___y_690_ = stack[3].m_obj;
lean_object* v___y_691_ = stack[4].m_obj;
lean_object* v___y_692_ = stack[5].m_obj;
lean_object* v___y_693_ = stack[6].m_obj;
lean_object* v_res_696_;
v_res_696_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0(v_k_687_, v_b_688_, v_c_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
stack->m_obj
 = v_res_696_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0___boxed(lean_object* v_k_697_, lean_object* v_b_698_, lean_object* v_c_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0(v_k_697_, v_b_698_, v_c_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
return v_res_705_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(lean_object* v_type_706_, lean_object* v_k_707_, uint8_t v_cleanupAnnotations_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v___f_714_; uint8_t v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___f_714_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_714_, 0, v_k_707_);
v___x_715_ = 0;
v___x_716_ = lean_box(0);
v___x_717_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_715_, v___x_716_, v_type_706_, v___f_714_, v_cleanupAnnotations_708_, v___x_715_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_717_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_717_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
v_a_726_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_717_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_717_);
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
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_706_ = stack[0].m_obj;
lean_object* v_k_707_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_708_ = stack[2].m_num;
lean_object* v___y_709_ = stack[3].m_obj;
lean_object* v___y_710_ = stack[4].m_obj;
lean_object* v___y_711_ = stack[5].m_obj;
lean_object* v___y_712_ = stack[6].m_obj;
lean_object* v_res_734_;
v_res_734_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_706_, v_k_707_, v_cleanupAnnotations_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
stack->m_obj
 = v_res_734_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___boxed(lean_object* v_type_735_, lean_object* v_k_736_, lean_object* v_cleanupAnnotations_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_743_; lean_object* v_res_744_; 
v_cleanupAnnotations_boxed_743_ = lean_unbox(v_cleanupAnnotations_737_);
v_res_744_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_735_, v_k_736_, v_cleanupAnnotations_boxed_743_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
return v_res_744_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0(lean_object* v_00_u03b1_745_, lean_object* v_type_746_, lean_object* v_k_747_, uint8_t v_cleanupAnnotations_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_746_, v_k_747_, v_cleanupAnnotations_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
return v___x_754_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_746_ = stack[1].m_obj;
lean_object* v_k_747_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_748_ = stack[3].m_num;
lean_object* v___y_749_ = stack[4].m_obj;
lean_object* v___y_750_ = stack[5].m_obj;
lean_object* v___y_751_ = stack[6].m_obj;
lean_object* v___y_752_ = stack[7].m_obj;
lean_object* v_res_755_;
v_res_755_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0(lean_box(0), v_type_746_, v_k_747_, v_cleanupAnnotations_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
stack->m_obj
 = v_res_755_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___boxed(lean_object* v_00_u03b1_756_, lean_object* v_type_757_, lean_object* v_k_758_, lean_object* v_cleanupAnnotations_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_765_; lean_object* v_res_766_; 
v_cleanupAnnotations_boxed_765_ = lean_unbox(v_cleanupAnnotations_759_);
v_res_766_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0(v_00_u03b1_756_, v_type_757_, v_k_758_, v_cleanupAnnotations_boxed_765_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
return v_res_766_;
}
}
lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0(lean_object* v_name_773_, lean_object* v_x_774_, lean_object* v_type_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
uint8_t v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_781_ = 0;
v___x_782_ = lean_box(v___x_781_);
lean_inc(v_name_773_);
v___x_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_783_, 0, v_name_773_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_type_775_, v___x_783_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_834_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_834_ == 0)
{
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_834_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_834_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v_key_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v_key_789_ = lean_ctor_get(v_a_785_, 0);
v___x_790_ = lean_unsigned_to_nat(1u);
v___x_791_ = lean_mk_empty_array_with_capacity(v___x_790_);
lean_inc(v_a_785_);
v___x_792_ = lean_array_push(v___x_791_, v_a_785_);
v___x_793_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__2));
v___x_794_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_789_, v___x_793_);
if (v___x_794_ == 0)
{
lean_object* v___x_796_; 
lean_dec(v_a_785_);
lean_dec(v_name_773_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_792_);
v___x_796_ = v___x_787_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_792_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
else
{
lean_object* v___x_798_; uint8_t v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
lean_del_object(v___x_787_);
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = 1;
v___x_800_ = lean_box(v___x_799_);
lean_inc(v_name_773_);
v___x_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_801_, 0, v_name_773_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
lean_inc(v_a_785_);
v___x_802_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_a_785_, v___x_798_, v___x_801_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_804_; uint8_t v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_803_);
lean_dec_ref_known(v___x_802_, 1);
v___x_804_ = lean_array_push(v___x_792_, v_a_803_);
v___x_805_ = 2;
v___x_806_ = lean_box(v___x_805_);
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v_name_773_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_a_785_, v___x_790_, v___x_807_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_817_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_817_ == 0)
{
v___x_811_ = v___x_808_;
v_isShared_812_ = v_isSharedCheck_817_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_808_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_817_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_813_ = lean_array_push(v___x_804_, v_a_809_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_813_);
v___x_815_ = v___x_811_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_dec_ref(v___x_804_);
v_a_818_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_808_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_808_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_dec_ref(v___x_792_);
lean_dec(v_a_785_);
lean_dec(v_name_773_);
v_a_826_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_802_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_802_);
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
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_dec(v_name_773_);
v_a_835_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_784_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_784_);
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
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_773_ = stack[0].m_obj;
lean_object* v_x_774_ = stack[1].m_obj;
lean_object* v_type_775_ = stack[2].m_obj;
lean_object* v___y_776_ = stack[3].m_obj;
lean_object* v___y_777_ = stack[4].m_obj;
lean_object* v___y_778_ = stack[5].m_obj;
lean_object* v___y_779_ = stack[6].m_obj;
lean_object* v_res_843_;
v_res_843_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0(v_name_773_, v_x_774_, v_type_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
stack->m_obj
 = v_res_843_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___boxed(lean_object* v_name_844_, lean_object* v_x_845_, lean_object* v_type_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0(v_name_844_, v_x_845_, v_type_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec_ref(v_x_845_);
return v_res_852_;
}
}
lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport(lean_object* v_name_855_, lean_object* v_c_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v___f_862_; lean_object* v___x_863_; lean_object* v_env_864_; uint8_t v___x_865_; 
lean_inc_n(v_name_855_, 2);
v___f_862_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___boxed), 8, 1);
lean_closure_set(v___f_862_, 0, v_name_855_);
v___x_863_ = lean_st_ref_get(v_a_860_);
v_env_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc_ref(v_env_864_);
lean_dec(v___x_863_);
v___x_865_ = l_Lean_Linter_isDeprecated(v_env_864_, v_name_855_);
if (v___x_865_ == 0)
{
uint8_t v___x_866_; 
v___x_866_ = l_Lean_Name_isMetaprogramming(v_name_855_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; lean_object* v_type_868_; lean_object* v___x_869_; 
v___x_867_ = l_Lean_AsyncConstantInfo_toConstantVal(v_c_856_);
v_type_868_ = lean_ctor_get(v___x_867_, 2);
lean_inc_ref(v_type_868_);
lean_dec_ref(v___x_867_);
v___x_869_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_868_, v___f_862_, v___x_866_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
return v___x_869_;
}
else
{
lean_object* v___x_870_; lean_object* v___x_871_; 
lean_dec_ref(v___f_862_);
lean_dec_ref(v_c_856_);
v___x_870_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0));
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
return v___x_871_;
}
}
else
{
lean_object* v___x_872_; lean_object* v___x_873_; 
lean_dec_ref(v___f_862_);
lean_dec_ref(v_c_856_);
lean_dec(v_name_855_);
v___x_872_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0));
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
return v___x_873_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_855_ = stack[0].m_obj;
lean_object* v_c_856_ = stack[1].m_obj;
lean_object* v_a_857_ = stack[2].m_obj;
lean_object* v_a_858_ = stack[3].m_obj;
lean_object* v_a_859_ = stack[4].m_obj;
lean_object* v_a_860_ = stack[5].m_obj;
lean_object* v_res_874_;
v_res_874_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport(v_name_855_, v_c_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
stack->m_obj
 = v_res_874_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___boxed(lean_object* v_name_875_, lean_object* v_c_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport(v_name_875_, v_c_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
return v_res_882_;
}
}
lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_858108106____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_884_ = lean_box(0);
v___x_885_ = lean_st_mk_ref(v___x_884_);
v___x_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
return v___x_886_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_858108106____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_887_;
v_res_887_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_858108106____hygCtx___hyg_2_();
stack->m_obj
 = v_res_887_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_858108106____hygCtx___hyg_2____boxed(lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_858108106____hygCtx___hyg_2_();
return v_res_889_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_constantsPerImportTask(void){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = lean_unsigned_to_nat(6500u);
return v___x_915_;
}
}
lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2955776588____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_917_ = lean_box(0);
v___x_918_ = lean_st_mk_ref(v___x_917_);
v___x_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
return v___x_919_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2955776588____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_920_;
v_res_920_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2955776588____hygCtx___hyg_2_();
stack->m_obj
 = v_res_920_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2955776588____hygCtx___hyg_2____boxed(lean_object* v_a_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2955776588____hygCtx___hyg_2_();
return v_res_922_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1(void){
_start:
{
lean_object* v_droppedRef_924_; lean_object* v___x_925_; 
v_droppedRef_924_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt;
v___x_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_925_, 0, v_droppedRef_924_);
return v___x_925_;
}
}
lean_object* l_Lean_Meta_LibrarySearch_libSearchFindDecls(lean_object* v_ty_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_932_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_ext;
v___x_933_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__0));
v___x_934_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_droppedKeys));
v___x_935_ = lean_unsigned_to_nat(6500u);
v___x_936_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1, &l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1_once, _init_l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1);
v___x_937_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v___x_932_, v___x_933_, v___x_934_, v___x_935_, v___x_936_, v_ty_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
return v___x_937_;
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_libSearchFindDecls_0interp(lean_interpreter_value* stack)
{
lean_object* v_ty_926_ = stack[0].m_obj;
lean_object* v_a_927_ = stack[1].m_obj;
lean_object* v_a_928_ = stack[2].m_obj;
lean_object* v_a_929_ = stack[3].m_obj;
lean_object* v_a_930_ = stack[4].m_obj;
lean_object* v_res_938_;
v_res_938_ = l_Lean_Meta_LibrarySearch_libSearchFindDecls(v_ty_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
stack->m_obj
 = v_res_938_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_libSearchFindDecls___boxed(lean_object* v_ty_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_Meta_LibrarySearch_libSearchFindDecls(v_ty_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
return v_res_945_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_949_ = lean_box(0);
v___x_950_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_getStarLemmas___closed__1));
v___x_951_ = l_Lean_mkConst(v___x_950_, v___x_949_);
return v___x_951_;
}
}
lean_object* l_Lean_Meta_LibrarySearch_getStarLemmas(lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v_ref_959_; lean_object* v___x_960_; 
v_ref_959_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt;
v___x_960_ = lean_st_ref_get(v_ref_959_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2, &l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2_once, _init_l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2);
v___x_962_ = l_Lean_Meta_LibrarySearch_libSearchFindDecls(v___x_961_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_975_; 
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_975_ == 0)
{
lean_object* v_unused_976_; 
v_unused_976_ = lean_ctor_get(v___x_962_, 0);
lean_dec(v_unused_976_);
v___x_964_ = v___x_962_;
v_isShared_965_ = v_isSharedCheck_975_;
goto v_resetjp_963_;
}
else
{
lean_dec(v___x_962_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_975_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; 
v___x_966_ = lean_st_ref_get(v_ref_959_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_967_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_getStarLemmas___closed__3));
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_967_);
v___x_969_ = v___x_964_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
else
{
lean_object* v_val_971_; lean_object* v___x_973_; 
v_val_971_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_val_971_);
lean_dec_ref_known(v___x_966_, 1);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v_val_971_);
v___x_973_ = v___x_964_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_val_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
else
{
return v___x_962_;
}
}
else
{
lean_object* v_val_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
v_val_977_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_960_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_val_977_);
lean_dec(v___x_960_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
lean_ctor_set_tag(v___x_979_, 0);
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_val_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_getStarLemmas_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_954_ = stack[0].m_obj;
lean_object* v_a_955_ = stack[1].m_obj;
lean_object* v_a_956_ = stack[2].m_obj;
lean_object* v_a_957_ = stack[3].m_obj;
lean_object* v_res_985_;
v_res_985_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v_a_954_, v_a_955_, v_a_956_, v_a_957_);
stack->m_obj
 = v_res_985_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_getStarLemmas___boxed(lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v_a_986_, v_a_987_, v_a_988_, v_a_989_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
return v_res_991_;
}
}
lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0(uint8_t v___x_992_, lean_object* v___x_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
if (v___x_992_ == 0)
{
lean_object* v___x_999_; 
v___x_999_ = l_Lean_getRemainingHeartbeats___redArg(v___y_996_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1009_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1009_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1009_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
uint8_t v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1007_; 
v___x_1004_ = lean_nat_dec_lt(v_a_1000_, v___x_993_);
lean_dec(v_a_1000_);
v___x_1005_ = lean_box(v___x_1004_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v___x_1005_);
v___x_1007_ = v___x_1002_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
v_a_1010_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_999_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_999_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
else
{
uint8_t v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1018_ = 0;
v___x_1019_ = lean_box(v___x_1018_);
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
return v___x_1020_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_992_ = stack[0].m_num;
lean_object* v___x_993_ = stack[1].m_obj;
lean_object* v___y_994_ = stack[2].m_obj;
lean_object* v___y_995_ = stack[3].m_obj;
lean_object* v___y_996_ = stack[4].m_obj;
lean_object* v___y_997_ = stack[5].m_obj;
lean_object* v_res_1021_;
v_res_1021_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0(v___x_992_, v___x_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
stack->m_obj
 = v_res_1021_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0___boxed(lean_object* v___x_1022_, lean_object* v___x_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
uint8_t v___x_649__boxed_1029_; lean_object* v_res_1030_; 
v___x_649__boxed_1029_ = lean_unbox(v___x_1022_);
v_res_1030_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0(v___x_649__boxed_1029_, v___x_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___x_1023_);
return v_res_1030_;
}
}
lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(lean_object* v_leavePercent_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Lean_getMaxHeartbeats___redArg(v_a_1032_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; lean_object* v___x_1036_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
lean_dec_ref_known(v___x_1034_, 1);
v___x_1036_ = l_Lean_getRemainingHeartbeats___redArg(v_a_1032_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1051_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1039_ = v___x_1036_;
v_isShared_1040_ = v_isSharedCheck_1051_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1036_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1051_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; lean_object* v___x_1046_; lean_object* v___y_1047_; lean_object* v___x_1049_; 
v___x_1041_ = lean_nat_mul(v_a_1037_, v_leavePercent_1031_);
lean_dec(v_a_1037_);
v___x_1042_ = lean_unsigned_to_nat(100u);
v___x_1043_ = lean_nat_div(v___x_1041_, v___x_1042_);
lean_dec(v___x_1041_);
v___x_1044_ = lean_unsigned_to_nat(0u);
v___x_1045_ = lean_nat_dec_eq(v_a_1035_, v___x_1044_);
lean_dec(v_a_1035_);
v___x_1046_ = lean_box(v___x_1045_);
v___y_1047_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___y_1047_, 0, v___x_1046_);
lean_closure_set(v___y_1047_, 1, v___x_1043_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 0, v___y_1047_);
v___x_1049_ = v___x_1039_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___y_1047_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_dec(v_a_1035_);
v_a_1052_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1036_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1036_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
v_a_1060_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1034_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1034_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_leavePercent_1031_ = stack[0].m_obj;
lean_object* v_a_1032_ = stack[1].m_obj;
lean_object* v_res_1068_;
v_res_1068_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercent_1031_, v_a_1032_);
stack->m_obj
 = v_res_1068_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___boxed(lean_object* v_leavePercent_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercent_1069_, v_a_1070_);
lean_dec_ref(v_a_1070_);
lean_dec(v_leavePercent_1069_);
return v_res_1072_;
}
}
lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck(lean_object* v_leavePercent_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercent_1073_, v_a_1076_);
return v___x_1079_;
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_mkHeartbeatCheck_0interp(lean_interpreter_value* stack)
{
lean_object* v_leavePercent_1073_ = stack[0].m_obj;
lean_object* v_a_1074_ = stack[1].m_obj;
lean_object* v_a_1075_ = stack[2].m_obj;
lean_object* v_a_1076_ = stack[3].m_obj;
lean_object* v_a_1077_ = stack[4].m_obj;
lean_object* v_res_1080_;
v_res_1080_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck(v_leavePercent_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
stack->m_obj
 = v_res_1080_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___boxed(lean_object* v_leavePercent_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck(v_leavePercent_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
lean_dec(v_a_1085_);
lean_dec_ref(v_a_1084_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_leavePercent_1081_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(lean_object* v_upperBound_1088_, lean_object* v_x_1089_, lean_object* v_f_1090_, lean_object* v_y_1091_, lean_object* v_g_1092_, lean_object* v_a_1093_, lean_object* v_b_1094_){
_start:
{
uint8_t v___x_1095_; 
v___x_1095_ = lean_nat_dec_lt(v_a_1093_, v_upperBound_1088_);
if (v___x_1095_ == 0)
{
lean_dec(v_a_1093_);
lean_dec(v_g_1092_);
lean_dec(v_f_1090_);
return v_b_1094_;
}
else
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1096_ = lean_array_fget_borrowed(v_x_1089_, v_a_1093_);
lean_inc(v_f_1090_);
lean_inc(v___x_1096_);
v___x_1097_ = lean_apply_1(v_f_1090_, v___x_1096_);
v___x_1098_ = lean_array_push(v_b_1094_, v___x_1097_);
v___x_1099_ = lean_array_fget_borrowed(v_y_1091_, v_a_1093_);
lean_inc(v_g_1092_);
lean_inc(v___x_1099_);
v___x_1100_ = lean_apply_1(v_g_1092_, v___x_1099_);
v___x_1101_ = lean_array_push(v___x_1098_, v___x_1100_);
v___x_1102_ = lean_unsigned_to_nat(1u);
v___x_1103_ = lean_nat_add(v_a_1093_, v___x_1102_);
lean_dec(v_a_1093_);
v_a_1093_ = v___x_1103_;
v_b_1094_ = v___x_1101_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg___boxed(lean_object* v_upperBound_1105_, lean_object* v_x_1106_, lean_object* v_f_1107_, lean_object* v_y_1108_, lean_object* v_g_1109_, lean_object* v_a_1110_, lean_object* v_b_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v_upperBound_1105_, v_x_1106_, v_f_1107_, v_y_1108_, v_g_1109_, v_a_1110_, v_b_1111_);
lean_dec_ref(v_y_1108_);
lean_dec_ref(v_x_1106_);
lean_dec(v_upperBound_1105_);
return v_res_1112_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(lean_object* v_g_1113_, size_t v_sz_1114_, size_t v_i_1115_, lean_object* v_bs_1116_){
_start:
{
uint8_t v___x_1117_; 
v___x_1117_ = lean_usize_dec_lt(v_i_1115_, v_sz_1114_);
if (v___x_1117_ == 0)
{
lean_dec(v_g_1113_);
return v_bs_1116_;
}
else
{
lean_object* v_v_1118_; lean_object* v___x_1119_; lean_object* v_bs_x27_1120_; lean_object* v___x_1121_; size_t v___x_1122_; size_t v___x_1123_; lean_object* v___x_1124_; 
v_v_1118_ = lean_array_uget(v_bs_1116_, v_i_1115_);
v___x_1119_ = lean_unsigned_to_nat(0u);
v_bs_x27_1120_ = lean_array_uset(v_bs_1116_, v_i_1115_, v___x_1119_);
lean_inc(v_g_1113_);
v___x_1121_ = lean_apply_1(v_g_1113_, v_v_1118_);
v___x_1122_ = ((size_t)1ULL);
v___x_1123_ = lean_usize_add(v_i_1115_, v___x_1122_);
v___x_1124_ = lean_array_uset(v_bs_x27_1120_, v_i_1115_, v___x_1121_);
v_i_1115_ = v___x_1123_;
v_bs_1116_ = v___x_1124_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_g_1113_ = stack[0].m_obj;
size_t v_sz_1114_ = stack[1].m_num;
size_t v_i_1115_ = stack[2].m_num;
lean_object* v_bs_1116_ = stack[3].m_obj;
lean_object* v_res_1126_;
v_res_1126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1113_, v_sz_1114_, v_i_1115_, v_bs_1116_);
stack->m_obj
 = v_res_1126_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg___boxed(lean_object* v_g_1127_, lean_object* v_sz_1128_, lean_object* v_i_1129_, lean_object* v_bs_1130_){
_start:
{
size_t v_sz_boxed_1131_; size_t v_i_boxed_1132_; lean_object* v_res_1133_; 
v_sz_boxed_1131_ = lean_unbox_usize(v_sz_1128_);
lean_dec(v_sz_1128_);
v_i_boxed_1132_ = lean_unbox_usize(v_i_1129_);
lean_dec(v_i_1129_);
v_res_1133_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1127_, v_sz_boxed_1131_, v_i_boxed_1132_, v_bs_1130_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___redArg(lean_object* v_f_1134_, lean_object* v_x_1135_, lean_object* v_g_1136_, lean_object* v_y_1137_){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v_res_1141_; lean_object* v___y_1143_; uint8_t v___x_1157_; 
v___x_1138_ = lean_array_get_size(v_x_1135_);
v___x_1139_ = lean_array_get_size(v_y_1137_);
v___x_1140_ = lean_nat_add(v___x_1138_, v___x_1139_);
v_res_1141_ = lean_mk_empty_array_with_capacity(v___x_1140_);
lean_dec(v___x_1140_);
v___x_1157_ = lean_nat_dec_le(v___x_1138_, v___x_1139_);
if (v___x_1157_ == 0)
{
v___y_1143_ = v___x_1139_;
goto v___jp_1142_;
}
else
{
v___y_1143_ = v___x_1138_;
goto v___jp_1142_;
}
v___jp_1142_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; 
v___x_1144_ = lean_unsigned_to_nat(0u);
lean_inc(v_g_1136_);
lean_inc(v_f_1134_);
v___x_1145_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v___y_1143_, v_x_1135_, v_f_1134_, v_y_1137_, v_g_1136_, v___x_1144_, v_res_1141_);
v___x_1146_ = lean_nat_dec_lt(v___y_1143_, v___x_1138_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; size_t v_sz_1148_; size_t v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
lean_dec(v_f_1134_);
v___x_1147_ = l_Array_extract___redArg(v_y_1137_, v___y_1143_, v___x_1139_);
v_sz_1148_ = lean_array_size(v___x_1147_);
v___x_1149_ = ((size_t)0ULL);
v___x_1150_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1136_, v_sz_1148_, v___x_1149_, v___x_1147_);
v___x_1151_ = l_Array_append___redArg(v___x_1145_, v___x_1150_);
lean_dec_ref(v___x_1150_);
return v___x_1151_;
}
else
{
lean_object* v___x_1152_; size_t v_sz_1153_; size_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
lean_dec(v_g_1136_);
v___x_1152_ = l_Array_extract___redArg(v_x_1135_, v___y_1143_, v___x_1138_);
v_sz_1153_ = lean_array_size(v___x_1152_);
v___x_1154_ = ((size_t)0ULL);
v___x_1155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_f_1134_, v_sz_1153_, v___x_1154_, v___x_1152_);
v___x_1156_ = l_Array_append___redArg(v___x_1145_, v___x_1155_);
lean_dec_ref(v___x_1155_);
return v___x_1156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___redArg___boxed(lean_object* v_f_1158_, lean_object* v_x_1159_, lean_object* v_g_1160_, lean_object* v_y_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v_f_1158_, v_x_1159_, v_g_1160_, v_y_1161_);
lean_dec_ref(v_y_1161_);
lean_dec_ref(v_x_1159_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith(lean_object* v_00_u03b1_1163_, lean_object* v_00_u03b2_1164_, lean_object* v_00_u03b3_1165_, lean_object* v_f_1166_, lean_object* v_x_1167_, lean_object* v_g_1168_, lean_object* v_y_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v_f_1166_, v_x_1167_, v_g_1168_, v_y_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___boxed(lean_object* v_00_u03b1_1171_, lean_object* v_00_u03b2_1172_, lean_object* v_00_u03b3_1173_, lean_object* v_f_1174_, lean_object* v_x_1175_, lean_object* v_g_1176_, lean_object* v_y_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_Meta_LibrarySearch_interleaveWith(v_00_u03b1_1171_, v_00_u03b2_1172_, v_00_u03b3_1173_, v_f_1174_, v_x_1175_, v_g_1176_, v_y_1177_);
lean_dec_ref(v_y_1177_);
lean_dec_ref(v_x_1175_);
return v_res_1178_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0(lean_object* v_00_u03b2_1179_, lean_object* v_00_u03b3_1180_, lean_object* v_g_1181_, size_t v_sz_1182_, size_t v_i_1183_, lean_object* v_bs_1184_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1181_, v_sz_1182_, v_i_1183_, v_bs_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_g_1181_ = stack[2].m_obj;
size_t v_sz_1182_ = stack[3].m_num;
size_t v_i_1183_ = stack[4].m_num;
lean_object* v_bs_1184_ = stack[5].m_obj;
lean_object* v_res_1186_;
v_res_1186_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0(lean_box(0), lean_box(0), v_g_1181_, v_sz_1182_, v_i_1183_, v_bs_1184_);
stack->m_obj
 = v_res_1186_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___boxed(lean_object* v_00_u03b2_1187_, lean_object* v_00_u03b3_1188_, lean_object* v_g_1189_, lean_object* v_sz_1190_, lean_object* v_i_1191_, lean_object* v_bs_1192_){
_start:
{
size_t v_sz_boxed_1193_; size_t v_i_boxed_1194_; lean_object* v_res_1195_; 
v_sz_boxed_1193_ = lean_unbox_usize(v_sz_1190_);
lean_dec(v_sz_1190_);
v_i_boxed_1194_ = lean_unbox_usize(v_i_1191_);
lean_dec(v_i_1191_);
v_res_1195_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0(v_00_u03b2_1187_, v_00_u03b3_1188_, v_g_1189_, v_sz_boxed_1193_, v_i_boxed_1194_, v_bs_1192_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1(lean_object* v_00_u03b3_1196_, lean_object* v_upperBound_1197_, lean_object* v_00_u03b1_1198_, lean_object* v_x_1199_, lean_object* v_f_1200_, lean_object* v_00_u03b2_1201_, lean_object* v_y_1202_, lean_object* v_g_1203_, lean_object* v_inst_1204_, lean_object* v_R_1205_, lean_object* v_a_1206_, lean_object* v_b_1207_, lean_object* v_c_1208_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v_upperBound_1197_, v_x_1199_, v_f_1200_, v_y_1202_, v_g_1203_, v_a_1206_, v_b_1207_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___boxed(lean_object* v_00_u03b3_1210_, lean_object* v_upperBound_1211_, lean_object* v_00_u03b1_1212_, lean_object* v_x_1213_, lean_object* v_f_1214_, lean_object* v_00_u03b2_1215_, lean_object* v_y_1216_, lean_object* v_g_1217_, lean_object* v_inst_1218_, lean_object* v_R_1219_, lean_object* v_a_1220_, lean_object* v_b_1221_, lean_object* v_c_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1(v_00_u03b3_1210_, v_upperBound_1211_, v_00_u03b1_1212_, v_x_1213_, v_f_1214_, v_00_u03b2_1215_, v_y_1216_, v_g_1217_, v_inst_1218_, v_R_1219_, v_a_1220_, v_b_1221_, v_c_1222_);
lean_dec_ref(v_y_1216_);
lean_dec_ref(v_x_1213_);
lean_dec(v_upperBound_1211_);
return v_res_1223_;
}
}
lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_));
v___x_1232_ = l_Lean_registerInternalExceptionId(v___x_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1233_;
v_res_1233_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1233_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2____boxed(lean_object* v_a_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_();
return v_res_1235_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0(void){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1236_ = lean_box(0);
v___x_1237_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_abortSpeculationId;
v___x_1238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
lean_ctor_set(v___x_1238_, 1, v___x_1236_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___redArg(lean_object* v_inst_1239_){
_start:
{
lean_object* v_throw_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v_throw_1240_ = lean_ctor_get(v_inst_1239_, 0);
lean_inc(v_throw_1240_);
lean_dec_ref(v_inst_1239_);
v___x_1241_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0, &l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0_once, _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0);
v___x_1242_ = lean_apply_2(v_throw_1240_, lean_box(0), v___x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation(lean_object* v_m_1243_, lean_object* v_00_u03b1_1244_, lean_object* v_inst_1245_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Lean_Meta_LibrarySearch_abortSpeculation___redArg(v_inst_1245_);
return v___x_1246_;
}
}
uint8_t l_Lean_Meta_LibrarySearch_isAbortSpeculation(lean_object* v_x_1247_){
_start:
{
if (lean_obj_tag(v_x_1247_) == 1)
{
lean_object* v_id_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v_id_1248_ = lean_ctor_get(v_x_1247_, 0);
v___x_1249_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_abortSpeculationId;
v___x_1250_ = l_Lean_instBEqInternalExceptionId_beq(v_id_1248_, v___x_1249_);
return v___x_1250_;
}
else
{
uint8_t v___x_1251_; 
v___x_1251_ = 0;
return v___x_1251_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_isAbortSpeculation_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1247_ = stack[0].m_obj;
uint8_t v_res_1252_;
v_res_1252_ = l_Lean_Meta_LibrarySearch_isAbortSpeculation(v_x_1247_);
stack->m_num = v_res_1252_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_isAbortSpeculation___boxed(lean_object* v_x_1253_){
_start:
{
uint8_t v_res_1254_; lean_object* v_r_1255_; 
v_res_1254_ = l_Lean_Meta_LibrarySearch_isAbortSpeculation(v_x_1253_);
lean_dec_ref(v_x_1253_);
v_r_1255_ = lean_box(v_res_1254_);
return v_r_1255_;
}
}
lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(lean_object* v_x_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_Meta_saveState___redArg(v___y_1258_, v___y_1260_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; lean_object* v___x_1264_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_a_1263_);
lean_dec_ref_known(v___x_1262_, 1);
lean_inc(v___y_1260_);
lean_inc_ref(v___y_1259_);
lean_inc(v___y_1258_);
lean_inc_ref(v___y_1257_);
v___x_1264_ = lean_apply_5(v_x_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, lean_box(0));
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1273_; 
lean_dec(v_a_1263_);
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1267_ = v___x_1264_;
v_isShared_1268_ = v_isSharedCheck_1273_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1264_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1273_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; lean_object* v___x_1271_; 
v___x_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1269_, 0, v_a_1265_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v___x_1269_);
v___x_1271_ = v___x_1267_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1269_);
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
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1303_; 
v_a_1274_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1276_ = v___x_1264_;
v_isShared_1277_ = v_isSharedCheck_1303_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1264_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1303_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
uint8_t v___y_1279_; uint8_t v___x_1301_; 
v___x_1301_ = l_Lean_Exception_isInterrupt(v_a_1274_);
if (v___x_1301_ == 0)
{
uint8_t v___x_1302_; 
lean_inc(v_a_1274_);
v___x_1302_ = l_Lean_Exception_isRuntime(v_a_1274_);
v___y_1279_ = v___x_1302_;
goto v___jp_1278_;
}
else
{
v___y_1279_ = v___x_1301_;
goto v___jp_1278_;
}
v___jp_1278_:
{
if (v___y_1279_ == 0)
{
lean_object* v___x_1280_; 
lean_del_object(v___x_1276_);
lean_dec(v_a_1274_);
v___x_1280_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1263_, v___y_1258_, v___y_1260_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1288_; 
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1288_ == 0)
{
lean_object* v_unused_1289_; 
v_unused_1289_ = lean_ctor_get(v___x_1280_, 0);
lean_dec(v_unused_1289_);
v___x_1282_ = v___x_1280_;
v_isShared_1283_ = v_isSharedCheck_1288_;
goto v_resetjp_1281_;
}
else
{
lean_dec(v___x_1280_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1288_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1284_; lean_object* v___x_1286_; 
v___x_1284_ = lean_box(0);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 0, v___x_1284_);
v___x_1286_ = v___x_1282_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
v_a_1290_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1280_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1280_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
else
{
lean_object* v___x_1299_; 
lean_dec(v_a_1263_);
if (v_isShared_1277_ == 0)
{
v___x_1299_ = v___x_1276_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1274_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec_ref(v_x_1256_);
v_a_1304_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1262_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1262_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1256_ = stack[0].m_obj;
lean_object* v___y_1257_ = stack[1].m_obj;
lean_object* v___y_1258_ = stack[2].m_obj;
lean_object* v___y_1259_ = stack[3].m_obj;
lean_object* v___y_1260_ = stack[4].m_obj;
lean_object* v_res_1312_;
v_res_1312_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v_x_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
stack->m_obj
 = v_res_1312_;
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg___boxed(lean_object* v_x_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v_x_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
return v_res_1319_;
}
}
lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0(lean_object* v_00_u03b1_1320_, lean_object* v_x_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v_x_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
return v___x_1327_;
}
}
LEAN_EXPORT void l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1321_ = stack[1].m_obj;
lean_object* v___y_1322_ = stack[2].m_obj;
lean_object* v___y_1323_ = stack[3].m_obj;
lean_object* v___y_1324_ = stack[4].m_obj;
lean_object* v___y_1325_ = stack[5].m_obj;
lean_object* v_res_1328_;
v_res_1328_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0(lean_box(0), v_x_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
stack->m_obj
 = v_res_1328_;
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___boxed(lean_object* v_00_u03b1_1329_, lean_object* v_x_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0(v_00_u03b1_1329_, v_x_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
return v_res_1336_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(lean_object* v_e_1337_, lean_object* v___y_1338_){
_start:
{
uint8_t v___x_1340_; 
v___x_1340_ = l_Lean_Expr_hasMVar(v_e_1337_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v_e_1337_);
return v___x_1341_;
}
else
{
lean_object* v___x_1342_; lean_object* v_mctx_1343_; lean_object* v___x_1344_; lean_object* v_fst_1345_; lean_object* v_snd_1346_; lean_object* v___x_1347_; lean_object* v_cache_1348_; lean_object* v_zetaDeltaFVarIds_1349_; lean_object* v_postponed_1350_; lean_object* v_diag_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1360_; 
v___x_1342_ = lean_st_ref_get(v___y_1338_);
v_mctx_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc_ref(v_mctx_1343_);
lean_dec(v___x_1342_);
v___x_1344_ = l_Lean_instantiateMVarsCore(v_mctx_1343_, v_e_1337_);
v_fst_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_fst_1345_);
v_snd_1346_ = lean_ctor_get(v___x_1344_, 1);
lean_inc(v_snd_1346_);
lean_dec_ref(v___x_1344_);
v___x_1347_ = lean_st_ref_take(v___y_1338_);
v_cache_1348_ = lean_ctor_get(v___x_1347_, 1);
v_zetaDeltaFVarIds_1349_ = lean_ctor_get(v___x_1347_, 2);
v_postponed_1350_ = lean_ctor_get(v___x_1347_, 3);
v_diag_1351_ = lean_ctor_get(v___x_1347_, 4);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1360_ == 0)
{
lean_object* v_unused_1361_; 
v_unused_1361_ = lean_ctor_get(v___x_1347_, 0);
lean_dec(v_unused_1361_);
v___x_1353_ = v___x_1347_;
v_isShared_1354_ = v_isSharedCheck_1360_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_diag_1351_);
lean_inc(v_postponed_1350_);
lean_inc(v_zetaDeltaFVarIds_1349_);
lean_inc(v_cache_1348_);
lean_dec(v___x_1347_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1360_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v_snd_1346_);
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_snd_1346_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_cache_1348_);
lean_ctor_set(v_reuseFailAlloc_1359_, 2, v_zetaDeltaFVarIds_1349_);
lean_ctor_set(v_reuseFailAlloc_1359_, 3, v_postponed_1350_);
lean_ctor_set(v_reuseFailAlloc_1359_, 4, v_diag_1351_);
v___x_1356_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = lean_st_ref_put(v___y_1338_, v___x_1356_);
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v_fst_1345_);
return v___x_1358_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1337_ = stack[0].m_obj;
lean_object* v___y_1338_ = stack[1].m_obj;
lean_object* v_res_1362_;
v_res_1362_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_e_1337_, v___y_1338_);
stack->m_obj
 = v_res_1362_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg___boxed(lean_object* v_e_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_e_1363_, v___y_1364_);
lean_dec(v___y_1364_);
return v_res_1366_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1(lean_object* v_e_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_e_1367_, v___y_1369_);
return v___x_1373_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1367_ = stack[0].m_obj;
lean_object* v___y_1368_ = stack[1].m_obj;
lean_object* v___y_1369_ = stack[2].m_obj;
lean_object* v___y_1370_ = stack[3].m_obj;
lean_object* v___y_1371_ = stack[4].m_obj;
lean_object* v_res_1374_;
v_res_1374_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1(v_e_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
stack->m_obj
 = v_res_1374_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___boxed(lean_object* v_e_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1(v_e_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0(lean_object* v___x_1382_, lean_object* v_x_1383_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1382_);
lean_ctor_set(v___x_1384_, 1, v_x_1383_);
return v___x_1384_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(lean_object* v___x_1385_, size_t v_sz_1386_, size_t v_i_1387_, lean_object* v_bs_1388_){
_start:
{
uint8_t v___x_1389_; 
v___x_1389_ = lean_usize_dec_lt(v_i_1387_, v_sz_1386_);
if (v___x_1389_ == 0)
{
lean_dec_ref(v___x_1385_);
return v_bs_1388_;
}
else
{
lean_object* v_v_1390_; lean_object* v___x_1391_; lean_object* v_bs_x27_1392_; lean_object* v___x_1393_; size_t v___x_1394_; size_t v___x_1395_; lean_object* v___x_1396_; 
v_v_1390_ = lean_array_uget(v_bs_1388_, v_i_1387_);
v___x_1391_ = lean_unsigned_to_nat(0u);
v_bs_x27_1392_ = lean_array_uset(v_bs_1388_, v_i_1387_, v___x_1391_);
lean_inc_ref(v___x_1385_);
v___x_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1385_);
lean_ctor_set(v___x_1393_, 1, v_v_1390_);
v___x_1394_ = ((size_t)1ULL);
v___x_1395_ = lean_usize_add(v_i_1387_, v___x_1394_);
v___x_1396_ = lean_array_uset(v_bs_x27_1392_, v_i_1387_, v___x_1393_);
v_i_1387_ = v___x_1395_;
v_bs_1388_ = v___x_1396_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1385_ = stack[0].m_obj;
size_t v_sz_1386_ = stack[1].m_num;
size_t v_i_1387_ = stack[2].m_num;
lean_object* v_bs_1388_ = stack[3].m_obj;
lean_object* v_res_1398_;
v_res_1398_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(v___x_1385_, v_sz_1386_, v_i_1387_, v_bs_1388_);
stack->m_obj
 = v_res_1398_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2___boxed(lean_object* v___x_1399_, lean_object* v_sz_1400_, lean_object* v_i_1401_, lean_object* v_bs_1402_){
_start:
{
size_t v_sz_boxed_1403_; size_t v_i_boxed_1404_; lean_object* v_res_1405_; 
v_sz_boxed_1403_ = lean_unbox_usize(v_sz_1400_);
lean_dec(v_sz_1400_);
v_i_boxed_1404_ = lean_unbox_usize(v_i_1401_);
lean_dec(v_i_1401_);
v_res_1405_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(v___x_1399_, v_sz_boxed_1403_, v_i_boxed_1404_, v_bs_1402_);
return v_res_1405_;
}
}
lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm(lean_object* v_searchFn_1406_, lean_object* v_goal_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v___x_1413_; 
lean_inc(v_goal_1407_);
v___x_1413_ = l_Lean_MVarId_getType(v_goal_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1415_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_a_1414_);
lean_dec_ref_known(v___x_1413_, 1);
lean_inc_ref(v_searchFn_1406_);
lean_inc(v_a_1411_);
lean_inc_ref(v_a_1410_);
lean_inc(v_a_1409_);
lean_inc_ref(v_a_1408_);
v___x_1415_ = lean_apply_6(v_searchFn_1406_, v_a_1414_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, lean_box(0));
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1417_; lean_object* v_mctx_1418_; lean_object* v___x_1419_; lean_object* v___f_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref_known(v___x_1415_, 1);
v___x_1417_ = lean_st_ref_get(v_a_1409_);
v_mctx_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc_ref_n(v_mctx_1418_, 2);
lean_dec(v___x_1417_);
lean_inc(v_goal_1407_);
v___x_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1419_, 0, v_goal_1407_);
lean_ctor_set(v___x_1419_, 1, v_mctx_1418_);
lean_inc_ref(v___x_1419_);
v___f_1420_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0), 2, 1);
lean_closure_set(v___f_1420_, 0, v___x_1419_);
v___x_1421_ = lean_alloc_closure((void*)(l_Lean_MVarId_applySymm___boxed), 6, 1);
lean_closure_set(v___x_1421_, 0, v_goal_1407_);
v___x_1422_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v___x_1421_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1482_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1425_ = v___x_1422_;
v_isShared_1426_ = v_isSharedCheck_1482_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1422_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1482_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
if (lean_obj_tag(v_a_1423_) == 1)
{
lean_object* v_val_1427_; lean_object* v___x_1428_; 
lean_del_object(v___x_1425_);
lean_dec_ref_known(v___x_1419_, 2);
v_val_1427_ = lean_ctor_get(v_a_1423_, 0);
lean_inc_n(v_val_1427_, 2);
lean_dec_ref_known(v_a_1423_, 1);
v___x_1428_ = l_Lean_MVarId_getType(v_val_1427_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1430_; lean_object* v_a_1431_; lean_object* v___x_1432_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1429_);
lean_dec_ref_known(v___x_1428_, 1);
v___x_1430_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_a_1429_, v_a_1409_);
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref(v___x_1430_);
lean_inc(v_a_1411_);
lean_inc_ref(v_a_1410_);
lean_inc(v_a_1409_);
lean_inc_ref(v_a_1408_);
v___x_1432_ = lean_apply_6(v_searchFn_1406_, v_a_1431_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, lean_box(0));
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1459_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1435_ = v___x_1432_;
v_isShared_1436_ = v_isSharedCheck_1459_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1432_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1459_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1437_; lean_object* v_mctx_1438_; lean_object* v___x_1439_; lean_object* v___f_1440_; lean_object* v___x_1441_; lean_object* v_cache_1442_; lean_object* v_zetaDeltaFVarIds_1443_; lean_object* v_postponed_1444_; lean_object* v_diag_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1457_; 
v___x_1437_ = lean_st_ref_get(v_a_1409_);
v_mctx_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc_ref(v_mctx_1438_);
lean_dec(v___x_1437_);
v___x_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1439_, 0, v_val_1427_);
lean_ctor_set(v___x_1439_, 1, v_mctx_1438_);
v___f_1440_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0), 2, 1);
lean_closure_set(v___f_1440_, 0, v___x_1439_);
v___x_1441_ = lean_st_ref_take(v_a_1409_);
v_cache_1442_ = lean_ctor_get(v___x_1441_, 1);
v_zetaDeltaFVarIds_1443_ = lean_ctor_get(v___x_1441_, 2);
v_postponed_1444_ = lean_ctor_get(v___x_1441_, 3);
v_diag_1445_ = lean_ctor_get(v___x_1441_, 4);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1457_ == 0)
{
lean_object* v_unused_1458_; 
v_unused_1458_ = lean_ctor_get(v___x_1441_, 0);
lean_dec(v_unused_1458_);
v___x_1447_ = v___x_1441_;
v_isShared_1448_ = v_isSharedCheck_1457_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_diag_1445_);
lean_inc(v_postponed_1444_);
lean_inc(v_zetaDeltaFVarIds_1443_);
lean_inc(v_cache_1442_);
lean_dec(v___x_1441_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1457_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 0, v_mctx_1418_);
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_mctx_1418_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_cache_1442_);
lean_ctor_set(v_reuseFailAlloc_1456_, 2, v_zetaDeltaFVarIds_1443_);
lean_ctor_set(v_reuseFailAlloc_1456_, 3, v_postponed_1444_);
lean_ctor_set(v_reuseFailAlloc_1456_, 4, v_diag_1445_);
v___x_1450_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1454_; 
v___x_1451_ = lean_st_ref_put(v_a_1409_, v___x_1450_);
v___x_1452_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v___f_1420_, v_a_1416_, v___f_1440_, v_a_1433_);
lean_dec(v_a_1433_);
lean_dec(v_a_1416_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v___x_1452_);
v___x_1454_ = v___x_1435_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1452_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec(v_val_1427_);
lean_dec_ref(v___f_1420_);
lean_dec_ref(v_mctx_1418_);
lean_dec(v_a_1416_);
v_a_1460_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1432_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1432_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_dec(v_val_1427_);
lean_dec_ref(v___f_1420_);
lean_dec_ref(v_mctx_1418_);
lean_dec(v_a_1416_);
lean_dec_ref(v_searchFn_1406_);
v_a_1468_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1428_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1428_);
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
else
{
size_t v_sz_1476_; size_t v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1480_; 
lean_dec(v_a_1423_);
lean_dec_ref(v___f_1420_);
lean_dec_ref(v_mctx_1418_);
lean_dec_ref(v_searchFn_1406_);
v_sz_1476_ = lean_array_size(v_a_1416_);
v___x_1477_ = ((size_t)0ULL);
v___x_1478_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(v___x_1419_, v_sz_1476_, v___x_1477_, v_a_1416_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1478_);
v___x_1480_ = v___x_1425_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_dec_ref(v___f_1420_);
lean_dec_ref_known(v___x_1419_, 2);
lean_dec_ref(v_mctx_1418_);
lean_dec(v_a_1416_);
lean_dec_ref(v_searchFn_1406_);
v_a_1483_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1422_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1422_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
else
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_dec(v_goal_1407_);
lean_dec_ref(v_searchFn_1406_);
v_a_1491_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1415_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1415_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec(v_goal_1407_);
lean_dec_ref(v_searchFn_1406_);
v_a_1499_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1413_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1413_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_librarySearchSymm_0interp(lean_interpreter_value* stack)
{
lean_object* v_searchFn_1406_ = stack[0].m_obj;
lean_object* v_goal_1407_ = stack[1].m_obj;
lean_object* v_a_1408_ = stack[2].m_obj;
lean_object* v_a_1409_ = stack[3].m_obj;
lean_object* v_a_1410_ = stack[4].m_obj;
lean_object* v_a_1411_ = stack[5].m_obj;
lean_object* v_res_1507_;
v_res_1507_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v_searchFn_1406_, v_goal_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
stack->m_obj
 = v_res_1507_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm___boxed(lean_object* v_searchFn_1508_, lean_object* v_goal_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v_searchFn_1508_, v_goal_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
lean_dec(v_a_1513_);
lean_dec_ref(v_a_1512_);
lean_dec(v_a_1511_);
lean_dec_ref(v_a_1510_);
return v_res_1515_;
}
}
lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0(lean_object* v_e_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1526_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__1));
v___x_1527_ = lean_unsigned_to_nat(1u);
v___x_1528_ = lean_mk_empty_array_with_capacity(v___x_1527_);
v___x_1529_ = lean_array_push(v___x_1528_, v_e_1520_);
v___x_1530_ = l_Lean_Meta_mkAppM(v___x_1526_, v___x_1529_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
return v___x_1530_;
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1520_ = stack[0].m_obj;
lean_object* v___y_1521_ = stack[1].m_obj;
lean_object* v___y_1522_ = stack[2].m_obj;
lean_object* v___y_1523_ = stack[3].m_obj;
lean_object* v___y_1524_ = stack[4].m_obj;
lean_object* v_res_1531_;
v_res_1531_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0(v_e_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
stack->m_obj
 = v_res_1531_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___boxed(lean_object* v_e_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0(v_e_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
return v_res_1538_;
}
}
lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1(lean_object* v_e_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1549_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__1));
v___x_1550_ = lean_unsigned_to_nat(1u);
v___x_1551_ = lean_mk_empty_array_with_capacity(v___x_1550_);
v___x_1552_ = lean_array_push(v___x_1551_, v_e_1543_);
v___x_1553_ = l_Lean_Meta_mkAppM(v___x_1549_, v___x_1552_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
return v___x_1553_;
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1543_ = stack[0].m_obj;
lean_object* v___y_1544_ = stack[1].m_obj;
lean_object* v___y_1545_ = stack[2].m_obj;
lean_object* v___y_1546_ = stack[3].m_obj;
lean_object* v___y_1547_ = stack[4].m_obj;
lean_object* v_res_1554_;
v_res_1554_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1(v_e_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
stack->m_obj
 = v_res_1554_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___boxed(lean_object* v_e_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1(v_e_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
return v_res_1561_;
}
}
lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(lean_object* v_lem_1564_, uint8_t v_mod_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_){
_start:
{
lean_object* v___f_1571_; lean_object* v___f_1572_; lean_object* v___x_1573_; 
v___f_1571_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__0));
v___f_1572_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__1));
v___x_1573_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_lem_1564_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
if (lean_obj_tag(v___x_1573_) == 0)
{
switch(v_mod_1565_)
{
case 0:
{
return v___x_1573_;
}
case 1:
{
lean_object* v_a_1574_; lean_object* v___x_1575_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1574_);
lean_dec_ref_known(v___x_1573_, 1);
v___x_1575_ = l_Lean_Meta_mapForallTelescope(v___f_1571_, v_a_1574_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
return v___x_1575_;
}
default: 
{
lean_object* v_a_1576_; lean_object* v___x_1577_; 
v_a_1576_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v___x_1573_, 1);
v___x_1577_ = l_Lean_Meta_mapForallTelescope(v___f_1572_, v_a_1576_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
return v___x_1577_;
}
}
}
else
{
return v___x_1573_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma_0interp(lean_interpreter_value* stack)
{
lean_object* v_lem_1564_ = stack[0].m_obj;
uint8_t v_mod_1565_ = stack[1].m_num;
lean_object* v_a_1566_ = stack[2].m_obj;
lean_object* v_a_1567_ = stack[3].m_obj;
lean_object* v_a_1568_ = stack[4].m_obj;
lean_object* v_a_1569_ = stack[5].m_obj;
lean_object* v_res_1578_;
v_res_1578_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_lem_1564_, v_mod_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
stack->m_obj
 = v_res_1578_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___boxed(lean_object* v_lem_1579_, lean_object* v_mod_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
uint8_t v_mod_boxed_1586_; lean_object* v_res_1587_; 
v_mod_boxed_1586_ = lean_unbox(v_mod_1580_);
v_res_1587_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_lem_1579_, v_mod_boxed_1586_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
lean_dec(v_a_1584_);
lean_dec_ref(v_a_1583_);
lean_dec(v_a_1582_);
lean_dec_ref(v_a_1581_);
return v_res_1587_;
}
}
uint8_t l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar(lean_object* v_e_1588_){
_start:
{
switch(lean_obj_tag(v_e_1588_))
{
case 0:
{
uint8_t v___x_1589_; 
v___x_1589_ = 1;
return v___x_1589_;
}
case 1:
{
uint8_t v___x_1590_; 
v___x_1590_ = 1;
return v___x_1590_;
}
case 2:
{
uint8_t v___x_1591_; 
v___x_1591_ = 1;
return v___x_1591_;
}
default: 
{
uint8_t v___x_1592_; 
v___x_1592_ = 0;
return v___x_1592_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1588_ = stack[0].m_obj;
uint8_t v_res_1593_;
v_res_1593_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar(v_e_1588_);
stack->m_num = v_res_1593_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar___boxed(lean_object* v_e_1594_){
_start:
{
uint8_t v_res_1595_; lean_object* v_r_1596_; 
v_res_1595_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar(v_e_1594_);
lean_dec_ref(v_e_1594_);
v_r_1596_ = lean_box(v_res_1595_);
return v_r_1596_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1597_ = lean_unsigned_to_nat(32u);
v___x_1598_ = lean_mk_empty_array_with_capacity(v___x_1597_);
v___x_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
return v___x_1599_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1600_ = ((size_t)5ULL);
v___x_1601_ = lean_unsigned_to_nat(0u);
v___x_1602_ = lean_unsigned_to_nat(32u);
v___x_1603_ = lean_mk_empty_array_with_capacity(v___x_1602_);
v___x_1604_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0);
v___x_1605_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
lean_ctor_set(v___x_1605_, 1, v___x_1603_);
lean_ctor_set(v___x_1605_, 2, v___x_1601_);
lean_ctor_set(v___x_1605_, 3, v___x_1601_);
lean_ctor_set_usize(v___x_1605_, 4, v___x_1600_);
return v___x_1605_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(lean_object* v___y_1606_){
_start:
{
lean_object* v___x_1608_; lean_object* v_traceState_1609_; lean_object* v_traces_1610_; lean_object* v___x_1611_; lean_object* v_traceState_1612_; lean_object* v_env_1613_; lean_object* v_nextMacroScope_1614_; lean_object* v_ngen_1615_; lean_object* v_auxDeclNGen_1616_; lean_object* v_cache_1617_; lean_object* v_recordedDeps_1618_; lean_object* v_messages_1619_; lean_object* v_infoState_1620_; lean_object* v_snapshotTasks_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1640_; 
v___x_1608_ = lean_st_ref_get(v___y_1606_);
v_traceState_1609_ = lean_ctor_get(v___x_1608_, 4);
lean_inc_ref(v_traceState_1609_);
lean_dec(v___x_1608_);
v_traces_1610_ = lean_ctor_get(v_traceState_1609_, 0);
lean_inc_ref(v_traces_1610_);
lean_dec_ref(v_traceState_1609_);
v___x_1611_ = lean_st_ref_take(v___y_1606_);
v_traceState_1612_ = lean_ctor_get(v___x_1611_, 4);
v_env_1613_ = lean_ctor_get(v___x_1611_, 0);
v_nextMacroScope_1614_ = lean_ctor_get(v___x_1611_, 1);
v_ngen_1615_ = lean_ctor_get(v___x_1611_, 2);
v_auxDeclNGen_1616_ = lean_ctor_get(v___x_1611_, 3);
v_cache_1617_ = lean_ctor_get(v___x_1611_, 5);
v_recordedDeps_1618_ = lean_ctor_get(v___x_1611_, 6);
v_messages_1619_ = lean_ctor_get(v___x_1611_, 7);
v_infoState_1620_ = lean_ctor_get(v___x_1611_, 8);
v_snapshotTasks_1621_ = lean_ctor_get(v___x_1611_, 9);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1623_ = v___x_1611_;
v_isShared_1624_ = v_isSharedCheck_1640_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_snapshotTasks_1621_);
lean_inc(v_infoState_1620_);
lean_inc(v_messages_1619_);
lean_inc(v_recordedDeps_1618_);
lean_inc(v_cache_1617_);
lean_inc(v_traceState_1612_);
lean_inc(v_auxDeclNGen_1616_);
lean_inc(v_ngen_1615_);
lean_inc(v_nextMacroScope_1614_);
lean_inc(v_env_1613_);
lean_dec(v___x_1611_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1640_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
uint64_t v_tid_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1638_; 
v_tid_1625_ = lean_ctor_get_uint64(v_traceState_1612_, sizeof(void*)*1);
v_isSharedCheck_1638_ = !lean_is_exclusive(v_traceState_1612_);
if (v_isSharedCheck_1638_ == 0)
{
lean_object* v_unused_1639_; 
v_unused_1639_ = lean_ctor_get(v_traceState_1612_, 0);
lean_dec(v_unused_1639_);
v___x_1627_ = v_traceState_1612_;
v_isShared_1628_ = v_isSharedCheck_1638_;
goto v_resetjp_1626_;
}
else
{
lean_dec(v_traceState_1612_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1638_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1629_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v___x_1629_);
v___x_1631_ = v___x_1627_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1629_);
lean_ctor_set_uint64(v_reuseFailAlloc_1637_, sizeof(void*)*1, v_tid_1625_);
v___x_1631_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
lean_object* v___x_1633_; 
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 4, v___x_1631_);
v___x_1633_ = v___x_1623_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_env_1613_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_nextMacroScope_1614_);
lean_ctor_set(v_reuseFailAlloc_1636_, 2, v_ngen_1615_);
lean_ctor_set(v_reuseFailAlloc_1636_, 3, v_auxDeclNGen_1616_);
lean_ctor_set(v_reuseFailAlloc_1636_, 4, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1636_, 5, v_cache_1617_);
lean_ctor_set(v_reuseFailAlloc_1636_, 6, v_recordedDeps_1618_);
lean_ctor_set(v_reuseFailAlloc_1636_, 7, v_messages_1619_);
lean_ctor_set(v_reuseFailAlloc_1636_, 8, v_infoState_1620_);
lean_ctor_set(v_reuseFailAlloc_1636_, 9, v_snapshotTasks_1621_);
v___x_1633_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = lean_st_ref_put(v___y_1606_, v___x_1633_);
v___x_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1635_, 0, v_traces_1610_);
return v___x_1635_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1606_ = stack[0].m_obj;
lean_object* v_res_1641_;
v_res_1641_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v___y_1606_);
stack->m_obj
 = v_res_1641_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___boxed(lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v___y_1642_);
lean_dec(v___y_1642_);
return v_res_1644_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0(lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v___y_1648_);
return v___x_1650_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1645_ = stack[0].m_obj;
lean_object* v___y_1646_ = stack[1].m_obj;
lean_object* v___y_1647_ = stack[2].m_obj;
lean_object* v___y_1648_ = stack[3].m_obj;
lean_object* v_res_1651_;
v_res_1651_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0(v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
stack->m_obj
 = v_res_1651_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___boxed(lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0(v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
return v_res_1657_;
}
}
uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(lean_object* v_opts_1658_, lean_object* v_opt_1659_){
_start:
{
lean_object* v_name_1660_; lean_object* v_defValue_1661_; lean_object* v_map_1662_; lean_object* v___x_1663_; 
v_name_1660_ = lean_ctor_get(v_opt_1659_, 0);
v_defValue_1661_ = lean_ctor_get(v_opt_1659_, 1);
v_map_1662_ = lean_ctor_get(v_opts_1658_, 0);
v___x_1663_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1662_, v_name_1660_);
if (lean_obj_tag(v___x_1663_) == 0)
{
uint8_t v___x_1664_; 
v___x_1664_ = lean_unbox(v_defValue_1661_);
return v___x_1664_;
}
else
{
lean_object* v_val_1665_; 
v_val_1665_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_val_1665_);
lean_dec_ref_known(v___x_1663_, 1);
if (lean_obj_tag(v_val_1665_) == 1)
{
uint8_t v_v_1666_; 
v_v_1666_ = lean_ctor_get_uint8(v_val_1665_, 0);
lean_dec_ref_known(v_val_1665_, 0);
return v_v_1666_;
}
else
{
uint8_t v___x_1667_; 
lean_dec(v_val_1665_);
v___x_1667_ = lean_unbox(v_defValue_1661_);
return v___x_1667_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1658_ = stack[0].m_obj;
lean_object* v_opt_1659_ = stack[1].m_obj;
uint8_t v_res_1668_;
v_res_1668_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1658_, v_opt_1659_);
stack->m_num = v_res_1668_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___boxed(lean_object* v_opts_1669_, lean_object* v_opt_1670_){
_start:
{
uint8_t v_res_1671_; lean_object* v_r_1672_; 
v_res_1671_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1669_, v_opt_1670_);
lean_dec_ref(v_opt_1670_);
lean_dec_ref(v_opts_1669_);
v_r_1672_ = lean_box(v_res_1671_);
return v_r_1672_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__0));
v___x_1675_ = l_Lean_stringToMessageData(v___x_1674_);
return v___x_1675_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__2));
v___x_1678_ = l_Lean_stringToMessageData(v___x_1677_);
return v___x_1678_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__5));
v___x_1683_ = l_Lean_MessageData_ofFormat(v___x_1682_);
return v___x_1683_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__8));
v___x_1688_ = l_Lean_MessageData_ofFormat(v___x_1687_);
return v___x_1688_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12(void){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__11));
v___x_1693_ = l_Lean_MessageData_ofFormat(v___x_1692_);
return v___x_1693_;
}
}
lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0(lean_object* v_fst_1694_, uint8_t v_snd_1695_, lean_object* v_x_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___y_1706_; 
v___x_1702_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1);
v___x_1703_ = l_Lean_MessageData_ofName(v_fst_1694_);
v___x_1704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1702_);
lean_ctor_set(v___x_1704_, 1, v___x_1703_);
switch(v_snd_1695_)
{
case 0:
{
lean_object* v___x_1711_; 
v___x_1711_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6);
v___y_1706_ = v___x_1711_;
goto v___jp_1705_;
}
case 1:
{
lean_object* v___x_1712_; 
v___x_1712_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9);
v___y_1706_ = v___x_1712_;
goto v___jp_1705_;
}
default: 
{
lean_object* v___x_1713_; 
v___x_1713_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12);
v___y_1706_ = v___x_1713_;
goto v___jp_1705_;
}
}
v___jp_1705_:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
lean_inc_ref(v___y_1706_);
v___x_1707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1704_);
lean_ctor_set(v___x_1707_, 1, v___y_1706_);
v___x_1708_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3);
v___x_1709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1707_);
lean_ctor_set(v___x_1709_, 1, v___x_1708_);
v___x_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
return v___x_1710_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_1694_ = stack[0].m_obj;
uint8_t v_snd_1695_ = stack[1].m_num;
lean_object* v_x_1696_ = stack[2].m_obj;
lean_object* v___y_1697_ = stack[3].m_obj;
lean_object* v___y_1698_ = stack[4].m_obj;
lean_object* v___y_1699_ = stack[5].m_obj;
lean_object* v___y_1700_ = stack[6].m_obj;
lean_object* v_res_1714_;
v_res_1714_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0(v_fst_1694_, v_snd_1695_, v_x_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
stack->m_obj
 = v_res_1714_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___boxed(lean_object* v_fst_1715_, lean_object* v_snd_1716_, lean_object* v_x_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
uint8_t v_snd_11217__boxed_1723_; lean_object* v_res_1724_; 
v_snd_11217__boxed_1723_ = lean_unbox(v_snd_1716_);
v_res_1724_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0(v_fst_1715_, v_snd_11217__boxed_1723_, v_x_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec_ref(v_x_1717_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(lean_object* v_opts_1725_, lean_object* v_opt_1726_){
_start:
{
lean_object* v_name_1727_; lean_object* v_defValue_1728_; lean_object* v_map_1729_; lean_object* v___x_1730_; 
v_name_1727_ = lean_ctor_get(v_opt_1726_, 0);
v_defValue_1728_ = lean_ctor_get(v_opt_1726_, 1);
v_map_1729_ = lean_ctor_get(v_opts_1725_, 0);
v___x_1730_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1729_, v_name_1727_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_inc(v_defValue_1728_);
return v_defValue_1728_;
}
else
{
lean_object* v_val_1731_; 
v_val_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_val_1731_);
lean_dec_ref_known(v___x_1730_, 1);
if (lean_obj_tag(v_val_1731_) == 3)
{
lean_object* v_v_1732_; 
v_v_1732_ = lean_ctor_get(v_val_1731_, 0);
lean_inc(v_v_1732_);
lean_dec_ref_known(v_val_1731_, 1);
return v_v_1732_;
}
else
{
lean_dec(v_val_1731_);
lean_inc(v_defValue_1728_);
return v_defValue_1728_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5___boxed(lean_object* v_opts_1733_, lean_object* v_opt_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1733_, v_opt_1734_);
lean_dec_ref(v_opt_1734_);
lean_dec_ref(v_opts_1733_);
return v_res_1735_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(lean_object* v_x_1736_){
_start:
{
if (lean_obj_tag(v_x_1736_) == 0)
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1745_; 
v_a_1738_ = lean_ctor_get(v_x_1736_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v_x_1736_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1740_ = v_x_1736_;
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v_x_1736_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1745_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
lean_ctor_set_tag(v___x_1740_, 1);
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
v_a_1746_ = lean_ctor_get(v_x_1736_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v_x_1736_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v_x_1736_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v_x_1736_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
lean_ctor_set_tag(v___x_1748_, 0);
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1736_ = stack[0].m_obj;
lean_object* v_res_1754_;
v_res_1754_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_x_1736_);
stack->m_obj
 = v_res_1754_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg___boxed(lean_object* v_x_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_x_1755_);
return v_res_1757_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(size_t v_sz_1758_, size_t v_i_1759_, lean_object* v_bs_1760_){
_start:
{
uint8_t v___x_1761_; 
v___x_1761_ = lean_usize_dec_lt(v_i_1759_, v_sz_1758_);
if (v___x_1761_ == 0)
{
return v_bs_1760_;
}
else
{
lean_object* v_v_1762_; lean_object* v_msg_1763_; lean_object* v___x_1764_; lean_object* v_bs_x27_1765_; size_t v___x_1766_; size_t v___x_1767_; lean_object* v___x_1768_; 
v_v_1762_ = lean_array_uget_borrowed(v_bs_1760_, v_i_1759_);
v_msg_1763_ = lean_ctor_get(v_v_1762_, 1);
lean_inc_ref(v_msg_1763_);
v___x_1764_ = lean_unsigned_to_nat(0u);
v_bs_x27_1765_ = lean_array_uset(v_bs_1760_, v_i_1759_, v___x_1764_);
v___x_1766_ = ((size_t)1ULL);
v___x_1767_ = lean_usize_add(v_i_1759_, v___x_1766_);
v___x_1768_ = lean_array_uset(v_bs_x27_1765_, v_i_1759_, v_msg_1763_);
v_i_1759_ = v___x_1767_;
v_bs_1760_ = v___x_1768_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1758_ = stack[0].m_num;
size_t v_i_1759_ = stack[1].m_num;
lean_object* v_bs_1760_ = stack[2].m_obj;
lean_object* v_res_1770_;
v_res_1770_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(v_sz_1758_, v_i_1759_, v_bs_1760_);
stack->m_obj
 = v_res_1770_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1771_, lean_object* v_i_1772_, lean_object* v_bs_1773_){
_start:
{
size_t v_sz_boxed_1774_; size_t v_i_boxed_1775_; lean_object* v_res_1776_; 
v_sz_boxed_1774_ = lean_unbox_usize(v_sz_1771_);
lean_dec(v_sz_1771_);
v_i_boxed_1775_ = lean_unbox_usize(v_i_1772_);
lean_dec(v_i_1772_);
v_res_1776_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(v_sz_boxed_1774_, v_i_boxed_1775_, v_bs_1773_);
return v_res_1776_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(lean_object* v_oldTraces_1777_, lean_object* v_data_1778_, lean_object* v_ref_1779_, lean_object* v_msg_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v_toCold_1786_; lean_object* v_currRecDepth_1787_; lean_object* v_ref_1788_; uint16_t v_optionFlags_1789_; uint8_t v_suppressElabErrors_1790_; uint8_t v_isRecordingDeps_1791_; lean_object* v_ref_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v_traceState_1795_; lean_object* v_traces_1796_; lean_object* v___x_1797_; size_t v_sz_1798_; size_t v___x_1799_; lean_object* v___x_1800_; lean_object* v_msg_1801_; lean_object* v___x_1802_; lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1841_; 
v_toCold_1786_ = lean_ctor_get(v___y_1783_, 0);
v_currRecDepth_1787_ = lean_ctor_get(v___y_1783_, 1);
v_ref_1788_ = lean_ctor_get(v___y_1783_, 2);
v_optionFlags_1789_ = lean_ctor_get_uint16(v___y_1783_, sizeof(void*)*3);
v_suppressElabErrors_1790_ = lean_ctor_get_uint8(v___y_1783_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1791_ = lean_ctor_get_uint8(v___y_1783_, sizeof(void*)*3 + 3);
v_ref_1792_ = l_Lean_replaceRef(v_ref_1779_, v_ref_1788_);
lean_inc(v_currRecDepth_1787_);
lean_inc_ref(v_toCold_1786_);
v___x_1793_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1793_, 0, v_toCold_1786_);
lean_ctor_set(v___x_1793_, 1, v_currRecDepth_1787_);
lean_ctor_set(v___x_1793_, 2, v_ref_1792_);
lean_ctor_set_uint16(v___x_1793_, sizeof(void*)*3, v_optionFlags_1789_);
lean_ctor_set_uint8(v___x_1793_, sizeof(void*)*3 + 2, v_suppressElabErrors_1790_);
lean_ctor_set_uint8(v___x_1793_, sizeof(void*)*3 + 3, v_isRecordingDeps_1791_);
v___x_1794_ = lean_st_ref_get(v___y_1784_);
v_traceState_1795_ = lean_ctor_get(v___x_1794_, 4);
lean_inc_ref(v_traceState_1795_);
lean_dec(v___x_1794_);
v_traces_1796_ = lean_ctor_get(v_traceState_1795_, 0);
lean_inc_ref(v_traces_1796_);
lean_dec_ref(v_traceState_1795_);
v___x_1797_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1796_);
lean_dec_ref(v_traces_1796_);
v_sz_1798_ = lean_array_size(v___x_1797_);
v___x_1799_ = ((size_t)0ULL);
v___x_1800_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(v_sz_1798_, v___x_1799_, v___x_1797_);
v_msg_1801_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1801_, 0, v_data_1778_);
lean_ctor_set(v_msg_1801_, 1, v_msg_1780_);
lean_ctor_set(v_msg_1801_, 2, v___x_1800_);
v___x_1802_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msg_1801_, v___y_1781_, v___y_1782_, v___x_1793_, v___y_1784_);
lean_dec_ref_known(v___x_1793_, 3);
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1805_ = v___x_1802_;
v_isShared_1806_ = v_isSharedCheck_1841_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1802_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1841_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1807_; lean_object* v_traceState_1808_; lean_object* v_env_1809_; lean_object* v_nextMacroScope_1810_; lean_object* v_ngen_1811_; lean_object* v_auxDeclNGen_1812_; lean_object* v_cache_1813_; lean_object* v_recordedDeps_1814_; lean_object* v_messages_1815_; lean_object* v_infoState_1816_; lean_object* v_snapshotTasks_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1840_; 
v___x_1807_ = lean_st_ref_take(v___y_1784_);
v_traceState_1808_ = lean_ctor_get(v___x_1807_, 4);
v_env_1809_ = lean_ctor_get(v___x_1807_, 0);
v_nextMacroScope_1810_ = lean_ctor_get(v___x_1807_, 1);
v_ngen_1811_ = lean_ctor_get(v___x_1807_, 2);
v_auxDeclNGen_1812_ = lean_ctor_get(v___x_1807_, 3);
v_cache_1813_ = lean_ctor_get(v___x_1807_, 5);
v_recordedDeps_1814_ = lean_ctor_get(v___x_1807_, 6);
v_messages_1815_ = lean_ctor_get(v___x_1807_, 7);
v_infoState_1816_ = lean_ctor_get(v___x_1807_, 8);
v_snapshotTasks_1817_ = lean_ctor_get(v___x_1807_, 9);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1819_ = v___x_1807_;
v_isShared_1820_ = v_isSharedCheck_1840_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_snapshotTasks_1817_);
lean_inc(v_infoState_1816_);
lean_inc(v_messages_1815_);
lean_inc(v_recordedDeps_1814_);
lean_inc(v_cache_1813_);
lean_inc(v_traceState_1808_);
lean_inc(v_auxDeclNGen_1812_);
lean_inc(v_ngen_1811_);
lean_inc(v_nextMacroScope_1810_);
lean_inc(v_env_1809_);
lean_dec(v___x_1807_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1840_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
uint64_t v_tid_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1838_; 
v_tid_1821_ = lean_ctor_get_uint64(v_traceState_1808_, sizeof(void*)*1);
v_isSharedCheck_1838_ = !lean_is_exclusive(v_traceState_1808_);
if (v_isSharedCheck_1838_ == 0)
{
lean_object* v_unused_1839_; 
v_unused_1839_ = lean_ctor_get(v_traceState_1808_, 0);
lean_dec(v_unused_1839_);
v___x_1823_ = v_traceState_1808_;
v_isShared_1824_ = v_isSharedCheck_1838_;
goto v_resetjp_1822_;
}
else
{
lean_dec(v_traceState_1808_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1838_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1829_; 
v___x_1825_ = lean_box(0);
v___x_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1826_, 0, v_ref_1779_);
lean_ctor_set(v___x_1826_, 1, v_a_1803_);
v___x_1827_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1777_, v___x_1826_);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 0, v___x_1827_);
v___x_1829_ = v___x_1823_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1827_);
lean_ctor_set_uint64(v_reuseFailAlloc_1837_, sizeof(void*)*1, v_tid_1821_);
v___x_1829_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
lean_object* v___x_1831_; 
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 4, v___x_1829_);
v___x_1831_ = v___x_1819_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_env_1809_);
lean_ctor_set(v_reuseFailAlloc_1836_, 1, v_nextMacroScope_1810_);
lean_ctor_set(v_reuseFailAlloc_1836_, 2, v_ngen_1811_);
lean_ctor_set(v_reuseFailAlloc_1836_, 3, v_auxDeclNGen_1812_);
lean_ctor_set(v_reuseFailAlloc_1836_, 4, v___x_1829_);
lean_ctor_set(v_reuseFailAlloc_1836_, 5, v_cache_1813_);
lean_ctor_set(v_reuseFailAlloc_1836_, 6, v_recordedDeps_1814_);
lean_ctor_set(v_reuseFailAlloc_1836_, 7, v_messages_1815_);
lean_ctor_set(v_reuseFailAlloc_1836_, 8, v_infoState_1816_);
lean_ctor_set(v_reuseFailAlloc_1836_, 9, v_snapshotTasks_1817_);
v___x_1831_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
lean_object* v___x_1832_; lean_object* v___x_1834_; 
v___x_1832_ = lean_st_ref_put(v___y_1784_, v___x_1831_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1825_);
v___x_1834_ = v___x_1805_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1825_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_1777_ = stack[0].m_obj;
lean_object* v_data_1778_ = stack[1].m_obj;
lean_object* v_ref_1779_ = stack[2].m_obj;
lean_object* v_msg_1780_ = stack[3].m_obj;
lean_object* v___y_1781_ = stack[4].m_obj;
lean_object* v___y_1782_ = stack[5].m_obj;
lean_object* v___y_1783_ = stack[6].m_obj;
lean_object* v___y_1784_ = stack[7].m_obj;
lean_object* v_res_1842_;
v_res_1842_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_1777_, v_data_1778_, v_ref_1779_, v_msg_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
stack->m_obj
 = v_res_1842_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2___boxed(lean_object* v_oldTraces_1843_, lean_object* v_data_1844_, lean_object* v_ref_1845_, lean_object* v_msg_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_1843_, v_data_1844_, v_ref_1845_, v_msg_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
return v_res_1852_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(lean_object* v_e_1853_){
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
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1853_ = stack[0].m_obj;
uint8_t v_res_1856_;
v_res_1856_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(v_e_1853_);
stack->m_num = v_res_1856_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___boxed(lean_object* v_e_1857_){
_start:
{
uint8_t v_res_1858_; lean_object* v_r_1859_; 
v_res_1858_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(v_e_1857_);
lean_dec_ref(v_e_1857_);
v_r_1859_ = lean_box(v_res_1858_);
return v_r_1859_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1860_; double v___x_1861_; 
v___x_1860_ = lean_unsigned_to_nat(0u);
v___x_1861_ = lean_float_of_nat(v___x_1860_);
return v___x_1861_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__1));
v___x_1864_ = l_Lean_stringToMessageData(v___x_1863_);
return v___x_1864_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1865_; double v___x_1866_; 
v___x_1865_ = lean_unsigned_to_nat(1000u);
v___x_1866_ = lean_float_of_nat(v___x_1865_);
return v___x_1866_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(lean_object* v_cls_1867_, uint8_t v_collapsed_1868_, lean_object* v_tag_1869_, lean_object* v_opts_1870_, uint8_t v_clsEnabled_1871_, lean_object* v_oldTraces_1872_, lean_object* v_msg_1873_, lean_object* v_resStartStop_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v_fst_1880_; lean_object* v_snd_1881_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v_data_1885_; lean_object* v_fst_1896_; lean_object* v_snd_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; lean_object* v___y_1901_; lean_object* v_a_1902_; uint8_t v___y_1917_; double v___y_1949_; 
v_fst_1880_ = lean_ctor_get(v_resStartStop_1874_, 0);
lean_inc(v_fst_1880_);
v_snd_1881_ = lean_ctor_get(v_resStartStop_1874_, 1);
lean_inc(v_snd_1881_);
lean_dec_ref(v_resStartStop_1874_);
v_fst_1896_ = lean_ctor_get(v_snd_1881_, 0);
lean_inc(v_fst_1896_);
v_snd_1897_ = lean_ctor_get(v_snd_1881_, 1);
lean_inc(v_snd_1897_);
lean_dec(v_snd_1881_);
v___x_1898_ = l_Lean_trace_profiler;
v___x_1899_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1870_, v___x_1898_);
if (v___x_1899_ == 0)
{
v___y_1917_ = v___x_1899_;
goto v___jp_1916_;
}
else
{
lean_object* v___x_1954_; uint8_t v___x_1955_; 
v___x_1954_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1955_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1870_, v___x_1954_);
if (v___x_1955_ == 0)
{
lean_object* v___x_1956_; lean_object* v___x_1957_; double v___x_1958_; double v___x_1959_; double v___x_1960_; 
v___x_1956_ = l_Lean_trace_profiler_threshold;
v___x_1957_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1870_, v___x_1956_);
v___x_1958_ = lean_float_of_nat(v___x_1957_);
v___x_1959_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3);
v___x_1960_ = lean_float_div(v___x_1958_, v___x_1959_);
v___y_1949_ = v___x_1960_;
goto v___jp_1948_;
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; double v___x_1963_; 
v___x_1961_ = l_Lean_trace_profiler_threshold;
v___x_1962_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1870_, v___x_1961_);
v___x_1963_ = lean_float_of_nat(v___x_1962_);
v___y_1949_ = v___x_1963_;
goto v___jp_1948_;
}
}
v___jp_1882_:
{
lean_object* v___x_1886_; 
lean_inc(v___y_1883_);
v___x_1886_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_1872_, v_data_1885_, v___y_1883_, v___y_1884_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v___x_1887_; 
lean_dec_ref_known(v___x_1886_, 1);
v___x_1887_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_1880_);
return v___x_1887_;
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_dec(v_fst_1880_);
v_a_1888_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1886_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1886_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
v___jp_1900_:
{
uint8_t v_result_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; double v___x_1906_; lean_object* v_data_1907_; 
v_result_1903_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(v_fst_1880_);
v___x_1904_ = lean_box(v_result_1903_);
v___x_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
v___x_1906_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0);
lean_inc_ref(v_tag_1869_);
lean_inc_ref(v___x_1905_);
lean_inc(v_cls_1867_);
v_data_1907_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1907_, 0, v_cls_1867_);
lean_ctor_set(v_data_1907_, 1, v___x_1905_);
lean_ctor_set(v_data_1907_, 2, v_tag_1869_);
lean_ctor_set_float(v_data_1907_, sizeof(void*)*3, v___x_1906_);
lean_ctor_set_float(v_data_1907_, sizeof(void*)*3 + 8, v___x_1906_);
lean_ctor_set_uint8(v_data_1907_, sizeof(void*)*3 + 16, v_collapsed_1868_);
if (v___x_1899_ == 0)
{
lean_dec_ref_known(v___x_1905_, 1);
lean_dec(v_snd_1897_);
lean_dec(v_fst_1896_);
lean_dec_ref(v_tag_1869_);
lean_dec(v_cls_1867_);
v___y_1883_ = v___y_1901_;
v___y_1884_ = v_a_1902_;
v_data_1885_ = v_data_1907_;
goto v___jp_1882_;
}
else
{
lean_object* v_data_1908_; double v___x_1909_; double v___x_1910_; 
lean_dec_ref_known(v_data_1907_, 3);
v_data_1908_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1908_, 0, v_cls_1867_);
lean_ctor_set(v_data_1908_, 1, v___x_1905_);
lean_ctor_set(v_data_1908_, 2, v_tag_1869_);
v___x_1909_ = lean_unbox_float(v_fst_1896_);
lean_dec(v_fst_1896_);
lean_ctor_set_float(v_data_1908_, sizeof(void*)*3, v___x_1909_);
v___x_1910_ = lean_unbox_float(v_snd_1897_);
lean_dec(v_snd_1897_);
lean_ctor_set_float(v_data_1908_, sizeof(void*)*3 + 8, v___x_1910_);
lean_ctor_set_uint8(v_data_1908_, sizeof(void*)*3 + 16, v_collapsed_1868_);
v___y_1883_ = v___y_1901_;
v___y_1884_ = v_a_1902_;
v_data_1885_ = v_data_1908_;
goto v___jp_1882_;
}
}
v___jp_1911_:
{
lean_object* v_ref_1912_; lean_object* v___x_1913_; 
v_ref_1912_ = lean_ctor_get(v___y_1877_, 2);
lean_inc(v___y_1878_);
lean_inc_ref(v___y_1877_);
lean_inc(v___y_1876_);
lean_inc_ref(v___y_1875_);
lean_inc(v_fst_1880_);
v___x_1913_ = lean_apply_6(v_msg_1873_, v_fst_1880_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, lean_box(0));
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref_known(v___x_1913_, 1);
v___y_1901_ = v_ref_1912_;
v_a_1902_ = v_a_1914_;
goto v___jp_1900_;
}
else
{
lean_object* v___x_1915_; 
lean_dec_ref_known(v___x_1913_, 1);
v___x_1915_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2);
v___y_1901_ = v_ref_1912_;
v_a_1902_ = v___x_1915_;
goto v___jp_1900_;
}
}
v___jp_1916_:
{
if (v_clsEnabled_1871_ == 0)
{
if (v___y_1917_ == 0)
{
lean_object* v___x_1918_; lean_object* v_traceState_1919_; lean_object* v_env_1920_; lean_object* v_nextMacroScope_1921_; lean_object* v_ngen_1922_; lean_object* v_auxDeclNGen_1923_; lean_object* v_cache_1924_; lean_object* v_recordedDeps_1925_; lean_object* v_messages_1926_; lean_object* v_infoState_1927_; lean_object* v_snapshotTasks_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1947_; 
lean_dec(v_snd_1897_);
lean_dec(v_fst_1896_);
lean_dec_ref(v_msg_1873_);
lean_dec_ref(v_tag_1869_);
lean_dec(v_cls_1867_);
v___x_1918_ = lean_st_ref_take(v___y_1878_);
v_traceState_1919_ = lean_ctor_get(v___x_1918_, 4);
v_env_1920_ = lean_ctor_get(v___x_1918_, 0);
v_nextMacroScope_1921_ = lean_ctor_get(v___x_1918_, 1);
v_ngen_1922_ = lean_ctor_get(v___x_1918_, 2);
v_auxDeclNGen_1923_ = lean_ctor_get(v___x_1918_, 3);
v_cache_1924_ = lean_ctor_get(v___x_1918_, 5);
v_recordedDeps_1925_ = lean_ctor_get(v___x_1918_, 6);
v_messages_1926_ = lean_ctor_get(v___x_1918_, 7);
v_infoState_1927_ = lean_ctor_get(v___x_1918_, 8);
v_snapshotTasks_1928_ = lean_ctor_get(v___x_1918_, 9);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1930_ = v___x_1918_;
v_isShared_1931_ = v_isSharedCheck_1947_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_snapshotTasks_1928_);
lean_inc(v_infoState_1927_);
lean_inc(v_messages_1926_);
lean_inc(v_recordedDeps_1925_);
lean_inc(v_cache_1924_);
lean_inc(v_traceState_1919_);
lean_inc(v_auxDeclNGen_1923_);
lean_inc(v_ngen_1922_);
lean_inc(v_nextMacroScope_1921_);
lean_inc(v_env_1920_);
lean_dec(v___x_1918_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1947_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
uint64_t v_tid_1932_; lean_object* v_traces_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1946_; 
v_tid_1932_ = lean_ctor_get_uint64(v_traceState_1919_, sizeof(void*)*1);
v_traces_1933_ = lean_ctor_get(v_traceState_1919_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v_traceState_1919_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1935_ = v_traceState_1919_;
v_isShared_1936_ = v_isSharedCheck_1946_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_traces_1933_);
lean_dec(v_traceState_1919_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1946_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1937_; lean_object* v___x_1939_; 
v___x_1937_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1872_, v_traces_1933_);
lean_dec_ref(v_traces_1933_);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 0, v___x_1937_);
v___x_1939_ = v___x_1935_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1937_);
lean_ctor_set_uint64(v_reuseFailAlloc_1945_, sizeof(void*)*1, v_tid_1932_);
v___x_1939_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
lean_object* v___x_1941_; 
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 4, v___x_1939_);
v___x_1941_ = v___x_1930_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_env_1920_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v_nextMacroScope_1921_);
lean_ctor_set(v_reuseFailAlloc_1944_, 2, v_ngen_1922_);
lean_ctor_set(v_reuseFailAlloc_1944_, 3, v_auxDeclNGen_1923_);
lean_ctor_set(v_reuseFailAlloc_1944_, 4, v___x_1939_);
lean_ctor_set(v_reuseFailAlloc_1944_, 5, v_cache_1924_);
lean_ctor_set(v_reuseFailAlloc_1944_, 6, v_recordedDeps_1925_);
lean_ctor_set(v_reuseFailAlloc_1944_, 7, v_messages_1926_);
lean_ctor_set(v_reuseFailAlloc_1944_, 8, v_infoState_1927_);
lean_ctor_set(v_reuseFailAlloc_1944_, 9, v_snapshotTasks_1928_);
v___x_1941_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = lean_st_ref_put(v___y_1878_, v___x_1941_);
v___x_1943_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_1880_);
return v___x_1943_;
}
}
}
}
}
else
{
goto v___jp_1911_;
}
}
else
{
goto v___jp_1911_;
}
}
v___jp_1948_:
{
double v___x_1950_; double v___x_1951_; double v___x_1952_; uint8_t v___x_1953_; 
v___x_1950_ = lean_unbox_float(v_snd_1897_);
v___x_1951_ = lean_unbox_float(v_fst_1896_);
v___x_1952_ = lean_float_sub(v___x_1950_, v___x_1951_);
v___x_1953_ = lean_float_decLt(v___y_1949_, v___x_1952_);
v___y_1917_ = v___x_1953_;
goto v___jp_1916_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1867_ = stack[0].m_obj;
uint8_t v_collapsed_1868_ = stack[1].m_num;
lean_object* v_tag_1869_ = stack[2].m_obj;
lean_object* v_opts_1870_ = stack[3].m_obj;
uint8_t v_clsEnabled_1871_ = stack[4].m_num;
lean_object* v_oldTraces_1872_ = stack[5].m_obj;
lean_object* v_msg_1873_ = stack[6].m_obj;
lean_object* v_resStartStop_1874_ = stack[7].m_obj;
lean_object* v___y_1875_ = stack[8].m_obj;
lean_object* v___y_1876_ = stack[9].m_obj;
lean_object* v___y_1877_ = stack[10].m_obj;
lean_object* v___y_1878_ = stack[11].m_obj;
lean_object* v_res_1964_;
v_res_1964_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v_cls_1867_, v_collapsed_1868_, v_tag_1869_, v_opts_1870_, v_clsEnabled_1871_, v_oldTraces_1872_, v_msg_1873_, v_resStartStop_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
stack->m_obj
 = v_res_1964_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___boxed(lean_object* v_cls_1965_, lean_object* v_collapsed_1966_, lean_object* v_tag_1967_, lean_object* v_opts_1968_, lean_object* v_clsEnabled_1969_, lean_object* v_oldTraces_1970_, lean_object* v_msg_1971_, lean_object* v_resStartStop_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
uint8_t v_collapsed_boxed_1978_; uint8_t v_clsEnabled_boxed_1979_; lean_object* v_res_1980_; 
v_collapsed_boxed_1978_ = lean_unbox(v_collapsed_1966_);
v_clsEnabled_boxed_1979_ = lean_unbox(v_clsEnabled_1969_);
v_res_1980_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v_cls_1965_, v_collapsed_boxed_1978_, v_tag_1967_, v_opts_1968_, v_clsEnabled_boxed_1979_, v_oldTraces_1970_, v_msg_1971_, v_resStartStop_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec_ref(v_opts_1968_);
return v_res_1980_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2(void){
_start:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1984_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_1985_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__1));
v___x_1986_ = l_Lean_Name_append(v___x_1985_, v___x_1984_);
return v___x_1986_;
}
}
static double _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3(void){
_start:
{
lean_object* v___x_1987_; double v___x_1988_; 
v___x_1987_ = lean_unsigned_to_nat(1000000000u);
v___x_1988_ = lean_float_of_nat(v___x_1987_);
return v___x_1988_;
}
}
lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(lean_object* v_cfg_1989_, lean_object* v_act_1990_, lean_object* v_allowFailure_1991_, lean_object* v_cand_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_){
_start:
{
lean_object* v_fst_1998_; lean_object* v_snd_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2286_; 
v_fst_1998_ = lean_ctor_get(v_cand_1992_, 0);
v_snd_1999_ = lean_ctor_get(v_cand_1992_, 1);
v_isSharedCheck_2286_ = !lean_is_exclusive(v_cand_1992_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2001_ = v_cand_1992_;
v_isShared_2002_ = v_isSharedCheck_2286_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_snd_1999_);
lean_inc(v_fst_1998_);
lean_dec(v_cand_1992_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2286_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v_toCold_2003_; lean_object* v_options_2004_; uint8_t v_hasTrace_2005_; 
v_toCold_2003_ = lean_ctor_get(v_a_1995_, 0);
v_options_2004_ = lean_ctor_get(v_toCold_2003_, 2);
v_hasTrace_2005_ = lean_ctor_get_uint8(v_options_2004_, sizeof(void*)*1);
if (v_hasTrace_2005_ == 0)
{
lean_object* v_fst_2006_; lean_object* v_snd_2007_; lean_object* v_fst_2008_; lean_object* v_snd_2009_; lean_object* v___x_2010_; lean_object* v_cache_2011_; lean_object* v_zetaDeltaFVarIds_2012_; lean_object* v_postponed_2013_; lean_object* v_diag_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2062_; 
lean_del_object(v___x_2001_);
v_fst_2006_ = lean_ctor_get(v_fst_1998_, 0);
lean_inc(v_fst_2006_);
v_snd_2007_ = lean_ctor_get(v_fst_1998_, 1);
lean_inc(v_snd_2007_);
lean_dec(v_fst_1998_);
v_fst_2008_ = lean_ctor_get(v_snd_1999_, 0);
lean_inc(v_fst_2008_);
v_snd_2009_ = lean_ctor_get(v_snd_1999_, 1);
lean_inc(v_snd_2009_);
lean_dec(v_snd_1999_);
v___x_2010_ = lean_st_ref_take(v_a_1994_);
v_cache_2011_ = lean_ctor_get(v___x_2010_, 1);
v_zetaDeltaFVarIds_2012_ = lean_ctor_get(v___x_2010_, 2);
v_postponed_2013_ = lean_ctor_get(v___x_2010_, 3);
v_diag_2014_ = lean_ctor_get(v___x_2010_, 4);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2062_ == 0)
{
lean_object* v_unused_2063_; 
v_unused_2063_ = lean_ctor_get(v___x_2010_, 0);
lean_dec(v_unused_2063_);
v___x_2016_ = v___x_2010_;
v_isShared_2017_ = v_isSharedCheck_2062_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_diag_2014_);
lean_inc(v_postponed_2013_);
lean_inc(v_zetaDeltaFVarIds_2012_);
lean_inc(v_cache_2011_);
lean_dec(v___x_2010_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2062_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v_snd_2007_);
v___x_2019_ = v___x_2016_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_snd_2007_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v_cache_2011_);
lean_ctor_set(v_reuseFailAlloc_2061_, 2, v_zetaDeltaFVarIds_2012_);
lean_ctor_set(v_reuseFailAlloc_2061_, 3, v_postponed_2013_);
lean_ctor_set(v_reuseFailAlloc_2061_, 4, v_diag_2014_);
v___x_2019_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_object* v___x_2020_; uint8_t v___x_2021_; lean_object* v___x_2022_; 
v___x_2020_ = lean_st_ref_put(v_a_1994_, v___x_2019_);
v___x_2021_ = lean_unbox(v_snd_2009_);
lean_dec(v_snd_2009_);
v___x_2022_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2008_, v___x_2021_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref_known(v___x_2022_, 1);
v___x_2024_ = lean_box(0);
lean_inc(v_fst_2006_);
v___x_2025_ = l_Lean_MVarId_apply(v_fst_2006_, v_a_2023_, v_cfg_1989_, v___x_2024_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2027_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc_n(v_a_2026_, 2);
lean_dec_ref_known(v___x_2025_, 1);
lean_inc(v_a_1996_);
lean_inc_ref(v_a_1995_);
lean_inc(v_a_1994_);
lean_inc_ref(v_a_1993_);
v___x_2027_ = lean_apply_6(v_act_1990_, v_a_2026_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, lean_box(0));
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_dec(v_a_2026_);
lean_dec(v_fst_2006_);
lean_dec_ref(v_allowFailure_1991_);
return v___x_2027_;
}
else
{
lean_object* v_a_2028_; uint8_t v___y_2030_; uint8_t v___x_2051_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
v___x_2051_ = l_Lean_Exception_isInterrupt(v_a_2028_);
if (v___x_2051_ == 0)
{
uint8_t v___x_2052_; 
v___x_2052_ = l_Lean_Exception_isRuntime(v_a_2028_);
v___y_2030_ = v___x_2052_;
goto v___jp_2029_;
}
else
{
lean_dec(v_a_2028_);
v___y_2030_ = v___x_2051_;
goto v___jp_2029_;
}
v___jp_2029_:
{
if (v___y_2030_ == 0)
{
lean_object* v___x_2031_; 
lean_dec_ref_known(v___x_2027_, 1);
lean_inc(v_a_1996_);
lean_inc_ref(v_a_1995_);
lean_inc(v_a_1994_);
lean_inc_ref(v_a_1993_);
v___x_2031_ = lean_apply_6(v_allowFailure_1991_, v_fst_2006_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, lean_box(0));
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2042_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2034_ = v___x_2031_;
v_isShared_2035_ = v_isSharedCheck_2042_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2031_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2042_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
uint8_t v___x_2036_; 
v___x_2036_ = lean_unbox(v_a_2032_);
lean_dec(v_a_2032_);
if (v___x_2036_ == 0)
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
lean_del_object(v___x_2034_);
lean_dec(v_a_2026_);
v___x_2037_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1);
v___x_2038_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2037_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
return v___x_2038_;
}
else
{
lean_object* v___x_2040_; 
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 0, v_a_2026_);
v___x_2040_ = v___x_2034_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2026_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_dec(v_a_2026_);
v_a_2043_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_2031_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2031_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
else
{
lean_dec(v_a_2026_);
lean_dec(v_fst_2006_);
lean_dec_ref(v_allowFailure_1991_);
return v___x_2027_;
}
}
}
}
else
{
lean_dec(v_fst_2006_);
lean_dec_ref(v_allowFailure_1991_);
lean_dec_ref(v_act_1990_);
return v___x_2025_;
}
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v_fst_2006_);
lean_dec_ref(v_allowFailure_1991_);
lean_dec_ref(v_act_1990_);
lean_dec_ref(v_cfg_1989_);
v_a_2053_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2022_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2022_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
}
}
else
{
lean_object* v_fst_2064_; lean_object* v_snd_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2285_; 
v_fst_2064_ = lean_ctor_get(v_fst_1998_, 0);
v_snd_2065_ = lean_ctor_get(v_fst_1998_, 1);
v_isSharedCheck_2285_ = !lean_is_exclusive(v_fst_1998_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2067_ = v_fst_1998_;
v_isShared_2068_ = v_isSharedCheck_2285_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_snd_2065_);
lean_inc(v_fst_2064_);
lean_dec(v_fst_1998_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2285_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v_fst_2069_; lean_object* v_snd_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2284_; 
v_fst_2069_ = lean_ctor_get(v_snd_1999_, 0);
v_snd_2070_ = lean_ctor_get(v_snd_1999_, 1);
v_isSharedCheck_2284_ = !lean_is_exclusive(v_snd_1999_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2072_ = v_snd_1999_;
v_isShared_2073_ = v_isSharedCheck_2284_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_snd_2070_);
lean_inc(v_fst_2069_);
lean_dec(v_snd_1999_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2284_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v_inheritedTraceOptions_2074_; lean_object* v___f_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v_a_2083_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v_a_2102_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v_a_2107_; lean_object* v___y_2110_; lean_object* v___y_2111_; lean_object* v___y_2112_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; uint8_t v___y_2120_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v_a_2130_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v_a_2144_; lean_object* v___y_2147_; lean_object* v___y_2148_; lean_object* v_a_2149_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; uint8_t v___y_2162_; 
v_inheritedTraceOptions_2074_ = lean_ctor_get(v_toCold_2003_, 11);
lean_inc(v_snd_2070_);
lean_inc(v_fst_2069_);
v___f_2075_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2075_, 0, v_fst_2069_);
lean_closure_set(v___f_2075_, 1, v_snd_2070_);
v___x_2076_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_2077_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4));
v___x_2078_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2);
v___x_2079_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2074_, v_options_2004_, v___x_2078_);
if (v___x_2079_ == 0)
{
lean_object* v___x_2228_; uint8_t v___x_2229_; 
v___x_2228_ = l_Lean_trace_profiler;
v___x_2229_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_2004_, v___x_2228_);
if (v___x_2229_ == 0)
{
lean_object* v___x_2230_; lean_object* v_cache_2231_; lean_object* v_zetaDeltaFVarIds_2232_; lean_object* v_postponed_2233_; lean_object* v_diag_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2282_; 
lean_dec_ref(v___f_2075_);
lean_del_object(v___x_2072_);
lean_del_object(v___x_2067_);
lean_del_object(v___x_2001_);
v___x_2230_ = lean_st_ref_take(v_a_1994_);
v_cache_2231_ = lean_ctor_get(v___x_2230_, 1);
v_zetaDeltaFVarIds_2232_ = lean_ctor_get(v___x_2230_, 2);
v_postponed_2233_ = lean_ctor_get(v___x_2230_, 3);
v_diag_2234_ = lean_ctor_get(v___x_2230_, 4);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2282_ == 0)
{
lean_object* v_unused_2283_; 
v_unused_2283_ = lean_ctor_get(v___x_2230_, 0);
lean_dec(v_unused_2283_);
v___x_2236_ = v___x_2230_;
v_isShared_2237_ = v_isSharedCheck_2282_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_diag_2234_);
lean_inc(v_postponed_2233_);
lean_inc(v_zetaDeltaFVarIds_2232_);
lean_inc(v_cache_2231_);
lean_dec(v___x_2230_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2282_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
lean_ctor_set(v___x_2236_, 0, v_snd_2065_);
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_snd_2065_);
lean_ctor_set(v_reuseFailAlloc_2281_, 1, v_cache_2231_);
lean_ctor_set(v_reuseFailAlloc_2281_, 2, v_zetaDeltaFVarIds_2232_);
lean_ctor_set(v_reuseFailAlloc_2281_, 3, v_postponed_2233_);
lean_ctor_set(v_reuseFailAlloc_2281_, 4, v_diag_2234_);
v___x_2239_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
lean_object* v___x_2240_; uint8_t v___x_2241_; lean_object* v___x_2242_; 
v___x_2240_ = lean_st_ref_put(v_a_1994_, v___x_2239_);
v___x_2241_ = lean_unbox(v_snd_2070_);
lean_dec(v_snd_2070_);
v___x_2242_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2069_, v___x_2241_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v_a_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
lean_inc(v_a_2243_);
lean_dec_ref_known(v___x_2242_, 1);
v___x_2244_ = lean_box(0);
lean_inc(v_fst_2064_);
v___x_2245_ = l_Lean_MVarId_apply(v_fst_2064_, v_a_2243_, v_cfg_1989_, v___x_2244_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; lean_object* v___x_2247_; 
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc_n(v_a_2246_, 2);
lean_dec_ref_known(v___x_2245_, 1);
lean_inc(v_a_1996_);
lean_inc_ref(v_a_1995_);
lean_inc(v_a_1994_);
lean_inc_ref(v_a_1993_);
v___x_2247_ = lean_apply_6(v_act_1990_, v_a_2246_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, lean_box(0));
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_dec(v_a_2246_);
lean_dec(v_fst_2064_);
lean_dec_ref(v_allowFailure_1991_);
return v___x_2247_;
}
else
{
lean_object* v_a_2248_; uint8_t v___y_2250_; uint8_t v___x_2271_; 
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_a_2248_);
v___x_2271_ = l_Lean_Exception_isInterrupt(v_a_2248_);
if (v___x_2271_ == 0)
{
uint8_t v___x_2272_; 
v___x_2272_ = l_Lean_Exception_isRuntime(v_a_2248_);
v___y_2250_ = v___x_2272_;
goto v___jp_2249_;
}
else
{
lean_dec(v_a_2248_);
v___y_2250_ = v___x_2271_;
goto v___jp_2249_;
}
v___jp_2249_:
{
if (v___y_2250_ == 0)
{
lean_object* v___x_2251_; 
lean_dec_ref_known(v___x_2247_, 1);
lean_inc(v_a_1996_);
lean_inc_ref(v_a_1995_);
lean_inc(v_a_1994_);
lean_inc_ref(v_a_1993_);
v___x_2251_ = lean_apply_6(v_allowFailure_1991_, v_fst_2064_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, lean_box(0));
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2262_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2254_ = v___x_2251_;
v_isShared_2255_ = v_isSharedCheck_2262_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2251_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2262_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
uint8_t v___x_2256_; 
v___x_2256_ = lean_unbox(v_a_2252_);
lean_dec(v_a_2252_);
if (v___x_2256_ == 0)
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
lean_del_object(v___x_2254_);
lean_dec(v_a_2246_);
v___x_2257_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1);
v___x_2258_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2257_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
return v___x_2258_;
}
else
{
lean_object* v___x_2260_; 
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 0, v_a_2246_);
v___x_2260_ = v___x_2254_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2246_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
lean_dec(v_a_2246_);
v_a_2263_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2251_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2251_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
else
{
lean_dec(v_a_2246_);
lean_dec(v_fst_2064_);
lean_dec_ref(v_allowFailure_1991_);
return v___x_2247_;
}
}
}
}
else
{
lean_dec(v_fst_2064_);
lean_dec_ref(v_allowFailure_1991_);
lean_dec_ref(v_act_1990_);
return v___x_2245_;
}
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
lean_dec(v_fst_2064_);
lean_dec_ref(v_allowFailure_1991_);
lean_dec_ref(v_act_1990_);
lean_dec_ref(v_cfg_1989_);
v_a_2273_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2242_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2242_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
}
}
else
{
goto v___jp_2169_;
}
}
else
{
goto v___jp_2169_;
}
v___jp_2080_:
{
lean_object* v___x_2084_; double v___x_2085_; double v___x_2086_; double v___x_2087_; double v___x_2088_; double v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2093_; 
v___x_2084_ = lean_io_mono_nanos_now();
v___x_2085_ = lean_float_of_nat(v___y_2082_);
v___x_2086_ = lean_float_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3);
v___x_2087_ = lean_float_div(v___x_2085_, v___x_2086_);
v___x_2088_ = lean_float_of_nat(v___x_2084_);
v___x_2089_ = lean_float_div(v___x_2088_, v___x_2086_);
v___x_2090_ = lean_box_float(v___x_2087_);
v___x_2091_ = lean_box_float(v___x_2089_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 1, v___x_2091_);
lean_ctor_set(v___x_2072_, 0, v___x_2090_);
v___x_2093_ = v___x_2072_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2090_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
lean_object* v___x_2095_; 
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 1, v___x_2093_);
lean_ctor_set(v___x_2067_, 0, v_a_2083_);
v___x_2095_ = v___x_2067_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2083_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
lean_object* v___x_2096_; 
v___x_2096_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v___x_2076_, v_hasTrace_2005_, v___x_2077_, v_options_2004_, v___x_2079_, v___y_2081_, v___f_2075_, v___x_2095_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
return v___x_2096_;
}
}
}
v___jp_2099_:
{
lean_object* v___x_2103_; 
v___x_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2103_, 0, v_a_2102_);
v___y_2081_ = v___y_2100_;
v___y_2082_ = v___y_2101_;
v_a_2083_ = v___x_2103_;
goto v___jp_2080_;
}
v___jp_2104_:
{
lean_object* v___x_2108_; 
v___x_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2108_, 0, v_a_2107_);
v___y_2081_ = v___y_2105_;
v___y_2082_ = v___y_2106_;
v_a_2083_ = v___x_2108_;
goto v___jp_2080_;
}
v___jp_2109_:
{
if (lean_obj_tag(v___y_2112_) == 0)
{
lean_object* v_a_2113_; 
v_a_2113_ = lean_ctor_get(v___y_2112_, 0);
lean_inc(v_a_2113_);
lean_dec_ref_known(v___y_2112_, 1);
v___y_2100_ = v___y_2110_;
v___y_2101_ = v___y_2111_;
v_a_2102_ = v_a_2113_;
goto v___jp_2099_;
}
else
{
lean_object* v_a_2114_; 
v_a_2114_ = lean_ctor_get(v___y_2112_, 0);
lean_inc(v_a_2114_);
lean_dec_ref_known(v___y_2112_, 1);
v___y_2105_ = v___y_2110_;
v___y_2106_ = v___y_2111_;
v_a_2107_ = v_a_2114_;
goto v___jp_2104_;
}
}
v___jp_2115_:
{
if (v___y_2120_ == 0)
{
lean_object* v___x_2121_; 
lean_dec_ref(v___y_2116_);
lean_inc(v_a_1996_);
lean_inc_ref(v_a_1995_);
lean_inc(v_a_1994_);
lean_inc_ref(v_a_1993_);
v___x_2121_ = lean_apply_6(v_allowFailure_1991_, v_fst_2064_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, lean_box(0));
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; uint8_t v___x_2123_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref_known(v___x_2121_, 1);
v___x_2123_ = lean_unbox(v_a_2122_);
lean_dec(v_a_2122_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
lean_dec(v___y_2118_);
v___x_2124_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1);
v___x_2125_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2124_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
v___y_2110_ = v___y_2117_;
v___y_2111_ = v___y_2119_;
v___y_2112_ = v___x_2125_;
goto v___jp_2109_;
}
else
{
v___y_2100_ = v___y_2117_;
v___y_2101_ = v___y_2119_;
v_a_2102_ = v___y_2118_;
goto v___jp_2099_;
}
}
else
{
lean_object* v_a_2126_; 
lean_dec(v___y_2118_);
v_a_2126_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2121_, 1);
v___y_2105_ = v___y_2117_;
v___y_2106_ = v___y_2119_;
v_a_2107_ = v_a_2126_;
goto v___jp_2104_;
}
}
else
{
lean_dec(v___y_2118_);
lean_dec(v_fst_2064_);
lean_dec_ref(v_allowFailure_1991_);
v___y_2105_ = v___y_2117_;
v___y_2106_ = v___y_2119_;
v_a_2107_ = v___y_2116_;
goto v___jp_2104_;
}
}
v___jp_2127_:
{
lean_object* v___x_2131_; double v___x_2132_; double v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2137_; 
v___x_2131_ = lean_io_get_num_heartbeats();
v___x_2132_ = lean_float_of_nat(v___y_2128_);
v___x_2133_ = lean_float_of_nat(v___x_2131_);
v___x_2134_ = lean_box_float(v___x_2132_);
v___x_2135_ = lean_box_float(v___x_2133_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 1, v___x_2135_);
lean_ctor_set(v___x_2001_, 0, v___x_2134_);
v___x_2137_ = v___x_2001_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2134_);
lean_ctor_set(v_reuseFailAlloc_2140_, 1, v___x_2135_);
v___x_2137_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2138_, 0, v_a_2130_);
lean_ctor_set(v___x_2138_, 1, v___x_2137_);
v___x_2139_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v___x_2076_, v_hasTrace_2005_, v___x_2077_, v_options_2004_, v___x_2079_, v___y_2129_, v___f_2075_, v___x_2138_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
return v___x_2139_;
}
}
v___jp_2141_:
{
lean_object* v___x_2145_; 
v___x_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2145_, 0, v_a_2144_);
v___y_2128_ = v___y_2142_;
v___y_2129_ = v___y_2143_;
v_a_2130_ = v___x_2145_;
goto v___jp_2127_;
}
v___jp_2146_:
{
lean_object* v___x_2150_; 
v___x_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2150_, 0, v_a_2149_);
v___y_2128_ = v___y_2147_;
v___y_2129_ = v___y_2148_;
v_a_2130_ = v___x_2150_;
goto v___jp_2127_;
}
v___jp_2151_:
{
if (lean_obj_tag(v___y_2154_) == 0)
{
lean_object* v_a_2155_; 
v_a_2155_ = lean_ctor_get(v___y_2154_, 0);
lean_inc(v_a_2155_);
lean_dec_ref_known(v___y_2154_, 1);
v___y_2142_ = v___y_2152_;
v___y_2143_ = v___y_2153_;
v_a_2144_ = v_a_2155_;
goto v___jp_2141_;
}
else
{
lean_object* v_a_2156_; 
v_a_2156_ = lean_ctor_get(v___y_2154_, 0);
lean_inc(v_a_2156_);
lean_dec_ref_known(v___y_2154_, 1);
v___y_2147_ = v___y_2152_;
v___y_2148_ = v___y_2153_;
v_a_2149_ = v_a_2156_;
goto v___jp_2146_;
}
}
v___jp_2157_:
{
if (v___y_2162_ == 0)
{
lean_object* v___x_2163_; 
lean_dec_ref(v___y_2161_);
lean_inc(v_a_1996_);
lean_inc_ref(v_a_1995_);
lean_inc(v_a_1994_);
lean_inc_ref(v_a_1993_);
v___x_2163_ = lean_apply_6(v_allowFailure_1991_, v_fst_2064_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, lean_box(0));
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; uint8_t v___x_2165_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2164_);
lean_dec_ref_known(v___x_2163_, 1);
v___x_2165_ = lean_unbox(v_a_2164_);
lean_dec(v_a_2164_);
if (v___x_2165_ == 0)
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
lean_dec(v___y_2160_);
v___x_2166_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1);
v___x_2167_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2166_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
v___y_2152_ = v___y_2158_;
v___y_2153_ = v___y_2159_;
v___y_2154_ = v___x_2167_;
goto v___jp_2151_;
}
else
{
v___y_2142_ = v___y_2158_;
v___y_2143_ = v___y_2159_;
v_a_2144_ = v___y_2160_;
goto v___jp_2141_;
}
}
else
{
lean_object* v_a_2168_; 
lean_dec(v___y_2160_);
v_a_2168_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2168_);
lean_dec_ref_known(v___x_2163_, 1);
v___y_2147_ = v___y_2158_;
v___y_2148_ = v___y_2159_;
v_a_2149_ = v_a_2168_;
goto v___jp_2146_;
}
}
else
{
lean_dec(v___y_2160_);
lean_dec(v_fst_2064_);
lean_dec_ref(v_allowFailure_1991_);
v___y_2147_ = v___y_2158_;
v___y_2148_ = v___y_2159_;
v_a_2149_ = v___y_2161_;
goto v___jp_2146_;
}
}
v___jp_2169_:
{
lean_object* v___x_2170_; lean_object* v_a_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2170_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v_a_1996_);
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref(v___x_2170_);
v___x_2172_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2173_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_2004_, v___x_2172_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v_cache_2176_; lean_object* v_zetaDeltaFVarIds_2177_; lean_object* v_postponed_2178_; lean_object* v_diag_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2199_; 
lean_del_object(v___x_2001_);
v___x_2174_ = lean_io_mono_nanos_now();
v___x_2175_ = lean_st_ref_take(v_a_1994_);
v_cache_2176_ = lean_ctor_get(v___x_2175_, 1);
v_zetaDeltaFVarIds_2177_ = lean_ctor_get(v___x_2175_, 2);
v_postponed_2178_ = lean_ctor_get(v___x_2175_, 3);
v_diag_2179_ = lean_ctor_get(v___x_2175_, 4);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2199_ == 0)
{
lean_object* v_unused_2200_; 
v_unused_2200_ = lean_ctor_get(v___x_2175_, 0);
lean_dec(v_unused_2200_);
v___x_2181_ = v___x_2175_;
v_isShared_2182_ = v_isSharedCheck_2199_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_diag_2179_);
lean_inc(v_postponed_2178_);
lean_inc(v_zetaDeltaFVarIds_2177_);
lean_inc(v_cache_2176_);
lean_dec(v___x_2175_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2199_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v_snd_2065_);
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_snd_2065_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_cache_2176_);
lean_ctor_set(v_reuseFailAlloc_2198_, 2, v_zetaDeltaFVarIds_2177_);
lean_ctor_set(v_reuseFailAlloc_2198_, 3, v_postponed_2178_);
lean_ctor_set(v_reuseFailAlloc_2198_, 4, v_diag_2179_);
v___x_2184_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2185_; uint8_t v___x_2186_; lean_object* v___x_2187_; 
v___x_2185_ = lean_st_ref_put(v_a_1994_, v___x_2184_);
v___x_2186_ = lean_unbox(v_snd_2070_);
lean_dec(v_snd_2070_);
v___x_2187_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2069_, v___x_2186_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_a_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_a_2188_);
lean_dec_ref_known(v___x_2187_, 1);
v___x_2189_ = lean_box(0);
lean_inc(v_fst_2064_);
v___x_2190_ = l_Lean_MVarId_apply(v_fst_2064_, v_a_2188_, v_cfg_1989_, v___x_2189_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v___x_2192_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc_n(v_a_2191_, 2);
lean_dec_ref_known(v___x_2190_, 1);
lean_inc(v_a_1996_);
lean_inc_ref(v_a_1995_);
lean_inc(v_a_1994_);
lean_inc_ref(v_a_1993_);
v___x_2192_ = lean_apply_6(v_act_1990_, v_a_2191_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, lean_box(0));
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; 
lean_dec(v_a_2191_);
lean_dec(v_fst_2064_);
lean_dec_ref(v_allowFailure_1991_);
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___x_2192_, 1);
v___y_2100_ = v_a_2171_;
v___y_2101_ = v___x_2174_;
v_a_2102_ = v_a_2193_;
goto v___jp_2099_;
}
else
{
lean_object* v_a_2194_; uint8_t v___x_2195_; 
v_a_2194_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2194_);
lean_dec_ref_known(v___x_2192_, 1);
v___x_2195_ = l_Lean_Exception_isInterrupt(v_a_2194_);
if (v___x_2195_ == 0)
{
uint8_t v___x_2196_; 
lean_inc(v_a_2194_);
v___x_2196_ = l_Lean_Exception_isRuntime(v_a_2194_);
v___y_2116_ = v_a_2194_;
v___y_2117_ = v_a_2171_;
v___y_2118_ = v_a_2191_;
v___y_2119_ = v___x_2174_;
v___y_2120_ = v___x_2196_;
goto v___jp_2115_;
}
else
{
v___y_2116_ = v_a_2194_;
v___y_2117_ = v_a_2171_;
v___y_2118_ = v_a_2191_;
v___y_2119_ = v___x_2174_;
v___y_2120_ = v___x_2195_;
goto v___jp_2115_;
}
}
}
else
{
lean_dec(v_fst_2064_);
lean_dec_ref(v_allowFailure_1991_);
lean_dec_ref(v_act_1990_);
v___y_2110_ = v_a_2171_;
v___y_2111_ = v___x_2174_;
v___y_2112_ = v___x_2190_;
goto v___jp_2109_;
}
}
else
{
lean_object* v_a_2197_; 
lean_dec(v_fst_2064_);
lean_dec_ref(v_allowFailure_1991_);
lean_dec_ref(v_act_1990_);
lean_dec_ref(v_cfg_1989_);
v_a_2197_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_a_2197_);
lean_dec_ref_known(v___x_2187_, 1);
v___y_2105_ = v_a_2171_;
v___y_2106_ = v___x_2174_;
v_a_2107_ = v_a_2197_;
goto v___jp_2104_;
}
}
}
}
else
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v_cache_2203_; lean_object* v_zetaDeltaFVarIds_2204_; lean_object* v_postponed_2205_; lean_object* v_diag_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2226_; 
lean_del_object(v___x_2072_);
lean_del_object(v___x_2067_);
v___x_2201_ = lean_io_get_num_heartbeats();
v___x_2202_ = lean_st_ref_take(v_a_1994_);
v_cache_2203_ = lean_ctor_get(v___x_2202_, 1);
v_zetaDeltaFVarIds_2204_ = lean_ctor_get(v___x_2202_, 2);
v_postponed_2205_ = lean_ctor_get(v___x_2202_, 3);
v_diag_2206_ = lean_ctor_get(v___x_2202_, 4);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2226_ == 0)
{
lean_object* v_unused_2227_; 
v_unused_2227_ = lean_ctor_get(v___x_2202_, 0);
lean_dec(v_unused_2227_);
v___x_2208_ = v___x_2202_;
v_isShared_2209_ = v_isSharedCheck_2226_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_diag_2206_);
lean_inc(v_postponed_2205_);
lean_inc(v_zetaDeltaFVarIds_2204_);
lean_inc(v_cache_2203_);
lean_dec(v___x_2202_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2226_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v_snd_2065_);
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_snd_2065_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v_cache_2203_);
lean_ctor_set(v_reuseFailAlloc_2225_, 2, v_zetaDeltaFVarIds_2204_);
lean_ctor_set(v_reuseFailAlloc_2225_, 3, v_postponed_2205_);
lean_ctor_set(v_reuseFailAlloc_2225_, 4, v_diag_2206_);
v___x_2211_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
lean_object* v___x_2212_; uint8_t v___x_2213_; lean_object* v___x_2214_; 
v___x_2212_ = lean_st_ref_put(v_a_1994_, v___x_2211_);
v___x_2213_ = lean_unbox(v_snd_2070_);
lean_dec(v_snd_2070_);
v___x_2214_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2069_, v___x_2213_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
lean_dec_ref_known(v___x_2214_, 1);
v___x_2216_ = lean_box(0);
lean_inc(v_fst_2064_);
v___x_2217_ = l_Lean_MVarId_apply(v_fst_2064_, v_a_2215_, v_cfg_1989_, v___x_2216_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___x_2219_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc_n(v_a_2218_, 2);
lean_dec_ref_known(v___x_2217_, 1);
lean_inc(v_a_1996_);
lean_inc_ref(v_a_1995_);
lean_inc(v_a_1994_);
lean_inc_ref(v_a_1993_);
v___x_2219_ = lean_apply_6(v_act_1990_, v_a_2218_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, lean_box(0));
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; 
lean_dec(v_a_2218_);
lean_dec(v_fst_2064_);
lean_dec_ref(v_allowFailure_1991_);
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2220_);
lean_dec_ref_known(v___x_2219_, 1);
v___y_2142_ = v___x_2201_;
v___y_2143_ = v_a_2171_;
v_a_2144_ = v_a_2220_;
goto v___jp_2141_;
}
else
{
lean_object* v_a_2221_; uint8_t v___x_2222_; 
v_a_2221_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2221_);
lean_dec_ref_known(v___x_2219_, 1);
v___x_2222_ = l_Lean_Exception_isInterrupt(v_a_2221_);
if (v___x_2222_ == 0)
{
uint8_t v___x_2223_; 
lean_inc(v_a_2221_);
v___x_2223_ = l_Lean_Exception_isRuntime(v_a_2221_);
v___y_2158_ = v___x_2201_;
v___y_2159_ = v_a_2171_;
v___y_2160_ = v_a_2218_;
v___y_2161_ = v_a_2221_;
v___y_2162_ = v___x_2223_;
goto v___jp_2157_;
}
else
{
v___y_2158_ = v___x_2201_;
v___y_2159_ = v_a_2171_;
v___y_2160_ = v_a_2218_;
v___y_2161_ = v_a_2221_;
v___y_2162_ = v___x_2222_;
goto v___jp_2157_;
}
}
}
else
{
lean_dec(v_fst_2064_);
lean_dec_ref(v_allowFailure_1991_);
lean_dec_ref(v_act_1990_);
v___y_2152_ = v___x_2201_;
v___y_2153_ = v_a_2171_;
v___y_2154_ = v___x_2217_;
goto v___jp_2151_;
}
}
else
{
lean_object* v_a_2224_; 
lean_dec(v_fst_2064_);
lean_dec_ref(v_allowFailure_1991_);
lean_dec_ref(v_act_1990_);
lean_dec_ref(v_cfg_1989_);
v_a_2224_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2224_);
lean_dec_ref_known(v___x_2214_, 1);
v___y_2147_ = v___x_2201_;
v___y_2148_ = v_a_2171_;
v_a_2149_ = v_a_2224_;
goto v___jp_2146_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_1989_ = stack[0].m_obj;
lean_object* v_act_1990_ = stack[1].m_obj;
lean_object* v_allowFailure_1991_ = stack[2].m_obj;
lean_object* v_cand_1992_ = stack[3].m_obj;
lean_object* v_a_1993_ = stack[4].m_obj;
lean_object* v_a_1994_ = stack[5].m_obj;
lean_object* v_a_1995_ = stack[6].m_obj;
lean_object* v_a_1996_ = stack[7].m_obj;
lean_object* v_res_2287_;
v_res_2287_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(v_cfg_1989_, v_act_1990_, v_allowFailure_1991_, v_cand_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
stack->m_obj
 = v_res_2287_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___boxed(lean_object* v_cfg_2288_, lean_object* v_act_2289_, lean_object* v_allowFailure_2290_, lean_object* v_cand_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(v_cfg_2288_, v_act_2289_, v_allowFailure_2290_, v_cand_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
return v_res_2297_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(lean_object* v_00_u03b1_2298_, lean_object* v_x_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v___x_2305_; 
v___x_2305_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_x_2299_);
return v___x_2305_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2299_ = stack[1].m_obj;
lean_object* v___y_2300_ = stack[2].m_obj;
lean_object* v___y_2301_ = stack[3].m_obj;
lean_object* v___y_2302_ = stack[4].m_obj;
lean_object* v___y_2303_ = stack[5].m_obj;
lean_object* v_res_2306_;
v_res_2306_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(lean_box(0), v_x_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
stack->m_obj
 = v_res_2306_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2307_, lean_object* v_x_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(v_00_u03b1_2307_, v_x_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
return v_res_2314_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(lean_object* v_act_2317_, lean_object* v_a_2318_, uint8_t v_collectAll_2319_, lean_object* v_as_2320_, size_t v_sz_2321_, size_t v_i_2322_, lean_object* v_b_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v_a_2330_; uint8_t v___x_2334_; 
v___x_2334_ = lean_usize_dec_lt(v_i_2322_, v_sz_2321_);
if (v___x_2334_ == 0)
{
lean_object* v___x_2335_; 
lean_dec_ref(v_a_2318_);
lean_dec_ref(v_act_2317_);
v___x_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2335_, 0, v_b_2323_);
return v___x_2335_;
}
else
{
lean_object* v_snd_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2409_; 
v_snd_2336_ = lean_ctor_get(v_b_2323_, 1);
v_isSharedCheck_2409_ = !lean_is_exclusive(v_b_2323_);
if (v_isSharedCheck_2409_ == 0)
{
lean_object* v_unused_2410_; 
v_unused_2410_ = lean_ctor_get(v_b_2323_, 0);
lean_dec(v_unused_2410_);
v___x_2338_ = v_b_2323_;
v_isShared_2339_ = v_isSharedCheck_2409_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_snd_2336_);
lean_dec(v_b_2323_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2409_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2340_; lean_object* v_a_2341_; lean_object* v___x_2342_; 
v___x_2340_ = lean_box(0);
v_a_2341_ = lean_array_uget_borrowed(v_as_2320_, v_i_2322_);
lean_inc_ref(v_act_2317_);
lean_inc(v___y_2327_);
lean_inc_ref(v___y_2326_);
lean_inc(v___y_2325_);
lean_inc_ref(v___y_2324_);
lean_inc(v_a_2341_);
v___x_2342_ = lean_apply_6(v_act_2317_, v_a_2341_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, lean_box(0));
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2372_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2345_ = v___x_2342_;
v_isShared_2346_ = v_isSharedCheck_2372_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2342_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2372_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
uint8_t v___y_2365_; uint8_t v___x_2371_; 
v___x_2371_ = l_List_isEmpty___redArg(v_a_2343_);
if (v___x_2371_ == 0)
{
v___y_2365_ = v___x_2371_;
goto v___jp_2364_;
}
else
{
if (v_collectAll_2319_ == 0)
{
v___y_2365_ = v___x_2371_;
goto v___jp_2364_;
}
else
{
lean_del_object(v___x_2345_);
goto v___jp_2347_;
}
}
v___jp_2347_:
{
lean_object* v___x_2348_; lean_object* v_mctx_2349_; lean_object* v___x_2350_; 
v___x_2348_ = lean_st_ref_get(v___y_2325_);
v_mctx_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc_ref(v_mctx_2349_);
lean_dec(v___x_2348_);
lean_inc_ref(v_a_2318_);
v___x_2350_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2318_, v___y_2325_, v___y_2327_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v___x_2352_; 
lean_dec_ref_known(v___x_2350_, 1);
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 1, v_mctx_2349_);
lean_ctor_set(v___x_2338_, 0, v_a_2343_);
v___x_2352_ = v___x_2338_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2343_);
lean_ctor_set(v_reuseFailAlloc_2355_, 1, v_mctx_2349_);
v___x_2352_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2353_ = lean_array_push(v_snd_2336_, v___x_2352_);
v___x_2354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2340_);
lean_ctor_set(v___x_2354_, 1, v___x_2353_);
v_a_2330_ = v___x_2354_;
goto v___jp_2329_;
}
}
else
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
lean_dec_ref(v_mctx_2349_);
lean_dec(v_a_2343_);
lean_del_object(v___x_2338_);
lean_dec(v_snd_2336_);
lean_dec_ref(v_a_2318_);
lean_dec_ref(v_act_2317_);
v_a_2356_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2350_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2350_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
v___jp_2364_:
{
if (v___y_2365_ == 0)
{
lean_del_object(v___x_2345_);
goto v___jp_2347_;
}
else
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; 
lean_dec(v_a_2343_);
lean_del_object(v___x_2338_);
lean_dec_ref(v_a_2318_);
lean_dec_ref(v_act_2317_);
v___x_2366_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___closed__0));
v___x_2367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
lean_ctor_set(v___x_2367_, 1, v_snd_2336_);
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 0, v___x_2367_);
v___x_2369_ = v___x_2345_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2408_; 
v_a_2373_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2375_ = v___x_2342_;
v_isShared_2376_ = v_isSharedCheck_2408_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2342_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2408_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
uint8_t v___y_2378_; uint8_t v___x_2406_; 
v___x_2406_ = l_Lean_Exception_isInterrupt(v_a_2373_);
if (v___x_2406_ == 0)
{
uint8_t v___x_2407_; 
lean_inc(v_a_2373_);
v___x_2407_ = l_Lean_Exception_isRuntime(v_a_2373_);
v___y_2378_ = v___x_2407_;
goto v___jp_2377_;
}
else
{
v___y_2378_ = v___x_2406_;
goto v___jp_2377_;
}
v___jp_2377_:
{
if (v___y_2378_ == 0)
{
lean_object* v___x_2379_; 
lean_del_object(v___x_2375_);
lean_inc_ref(v_a_2318_);
v___x_2379_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2318_, v___y_2325_, v___y_2327_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2393_; 
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2393_ == 0)
{
lean_object* v_unused_2394_; 
v_unused_2394_ = lean_ctor_get(v___x_2379_, 0);
lean_dec(v_unused_2394_);
v___x_2381_ = v___x_2379_;
v_isShared_2382_ = v_isSharedCheck_2393_;
goto v_resetjp_2380_;
}
else
{
lean_dec(v___x_2379_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2393_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
uint8_t v___x_2383_; 
v___x_2383_ = l_Lean_Meta_LibrarySearch_isAbortSpeculation(v_a_2373_);
lean_dec(v_a_2373_);
if (v___x_2383_ == 0)
{
lean_object* v___x_2385_; 
lean_del_object(v___x_2381_);
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 0, v___x_2340_);
v___x_2385_ = v___x_2338_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2340_);
lean_ctor_set(v_reuseFailAlloc_2386_, 1, v_snd_2336_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
v_a_2330_ = v___x_2385_;
goto v___jp_2329_;
}
}
else
{
lean_object* v___x_2388_; 
lean_dec_ref(v_a_2318_);
lean_dec_ref(v_act_2317_);
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 0, v___x_2340_);
v___x_2388_ = v___x_2338_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2340_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v_snd_2336_);
v___x_2388_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v___x_2390_; 
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 0, v___x_2388_);
v___x_2390_ = v___x_2381_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2388_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
}
else
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
lean_dec(v_a_2373_);
lean_del_object(v___x_2338_);
lean_dec(v_snd_2336_);
lean_dec_ref(v_a_2318_);
lean_dec_ref(v_act_2317_);
v_a_2395_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2379_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2379_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
else
{
lean_object* v___x_2404_; 
lean_del_object(v___x_2338_);
lean_dec(v_snd_2336_);
lean_dec_ref(v_a_2318_);
lean_dec_ref(v_act_2317_);
if (v_isShared_2376_ == 0)
{
v___x_2404_ = v___x_2375_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2373_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
}
}
}
v___jp_2329_:
{
size_t v___x_2331_; size_t v___x_2332_; 
v___x_2331_ = ((size_t)1ULL);
v___x_2332_ = lean_usize_add(v_i_2322_, v___x_2331_);
v_i_2322_ = v___x_2332_;
v_b_2323_ = v_a_2330_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_2317_ = stack[0].m_obj;
lean_object* v_a_2318_ = stack[1].m_obj;
uint8_t v_collectAll_2319_ = stack[2].m_num;
lean_object* v_as_2320_ = stack[3].m_obj;
size_t v_sz_2321_ = stack[4].m_num;
size_t v_i_2322_ = stack[5].m_num;
lean_object* v_b_2323_ = stack[6].m_obj;
lean_object* v___y_2324_ = stack[7].m_obj;
lean_object* v___y_2325_ = stack[8].m_obj;
lean_object* v___y_2326_ = stack[9].m_obj;
lean_object* v___y_2327_ = stack[10].m_obj;
lean_object* v_res_2411_;
v_res_2411_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(v_act_2317_, v_a_2318_, v_collectAll_2319_, v_as_2320_, v_sz_2321_, v_i_2322_, v_b_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
stack->m_obj
 = v_res_2411_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___boxed(lean_object* v_act_2412_, lean_object* v_a_2413_, lean_object* v_collectAll_2414_, lean_object* v_as_2415_, lean_object* v_sz_2416_, lean_object* v_i_2417_, lean_object* v_b_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
uint8_t v_collectAll_boxed_2424_; size_t v_sz_boxed_2425_; size_t v_i_boxed_2426_; lean_object* v_res_2427_; 
v_collectAll_boxed_2424_ = lean_unbox(v_collectAll_2414_);
v_sz_boxed_2425_ = lean_unbox_usize(v_sz_2416_);
lean_dec(v_sz_2416_);
v_i_boxed_2426_ = lean_unbox_usize(v_i_2417_);
lean_dec(v_i_2417_);
v_res_2427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(v_act_2412_, v_a_2413_, v_collectAll_boxed_2424_, v_as_2415_, v_sz_boxed_2425_, v_i_boxed_2426_, v_b_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec_ref(v_as_2415_);
return v_res_2427_;
}
}
lean_object* l_Lean_Meta_LibrarySearch_tryOnEach(lean_object* v_act_2433_, lean_object* v_candidates_2434_, uint8_t v_collectAll_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Lean_Meta_saveState___redArg(v_a_2437_, v_a_2439_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v_a_2442_; lean_object* v___x_2443_; size_t v_sz_2444_; size_t v___x_2445_; lean_object* v___x_2446_; 
v_a_2442_ = lean_ctor_get(v___x_2441_, 0);
lean_inc(v_a_2442_);
lean_dec_ref_known(v___x_2441_, 1);
v___x_2443_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryOnEach___closed__1));
v_sz_2444_ = lean_array_size(v_candidates_2434_);
v___x_2445_ = ((size_t)0ULL);
v___x_2446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(v_act_2433_, v_a_2442_, v_collectAll_2435_, v_candidates_2434_, v_sz_2444_, v___x_2445_, v___x_2443_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2461_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2449_ = v___x_2446_;
v_isShared_2450_ = v_isSharedCheck_2461_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___x_2446_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2461_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v_fst_2451_; 
v_fst_2451_ = lean_ctor_get(v_a_2447_, 0);
if (lean_obj_tag(v_fst_2451_) == 0)
{
lean_object* v_snd_2452_; lean_object* v___x_2453_; lean_object* v___x_2455_; 
v_snd_2452_ = lean_ctor_get(v_a_2447_, 1);
lean_inc(v_snd_2452_);
lean_dec(v_a_2447_);
v___x_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2453_, 0, v_snd_2452_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 0, v___x_2453_);
v___x_2455_ = v___x_2449_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2453_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
else
{
lean_object* v_val_2457_; lean_object* v___x_2459_; 
lean_inc_ref(v_fst_2451_);
lean_dec(v_a_2447_);
v_val_2457_ = lean_ctor_get(v_fst_2451_, 0);
lean_inc(v_val_2457_);
lean_dec_ref_known(v_fst_2451_, 1);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 0, v_val_2457_);
v___x_2459_ = v___x_2449_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_val_2457_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
v_a_2462_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2446_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2446_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
lean_dec_ref(v_act_2433_);
v_a_2470_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2441_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2441_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_tryOnEach_0interp(lean_interpreter_value* stack)
{
lean_object* v_act_2433_ = stack[0].m_obj;
lean_object* v_candidates_2434_ = stack[1].m_obj;
uint8_t v_collectAll_2435_ = stack[2].m_num;
lean_object* v_a_2436_ = stack[3].m_obj;
lean_object* v_a_2437_ = stack[4].m_obj;
lean_object* v_a_2438_ = stack[5].m_obj;
lean_object* v_a_2439_ = stack[6].m_obj;
lean_object* v_res_2478_;
v_res_2478_ = l_Lean_Meta_LibrarySearch_tryOnEach(v_act_2433_, v_candidates_2434_, v_collectAll_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_);
stack->m_obj
 = v_res_2478_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryOnEach___boxed(lean_object* v_act_2479_, lean_object* v_candidates_2480_, lean_object* v_collectAll_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_){
_start:
{
uint8_t v_collectAll_boxed_2487_; lean_object* v_res_2488_; 
v_collectAll_boxed_2487_ = lean_unbox(v_collectAll_2481_);
v_res_2488_ = l_Lean_Meta_LibrarySearch_tryOnEach(v_act_2479_, v_candidates_2480_, v_collectAll_boxed_2487_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_);
lean_dec(v_a_2485_);
lean_dec_ref(v_a_2484_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
lean_dec_ref(v_candidates_2480_);
return v_res_2488_;
}
}
lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg(){
_start:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2490_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0, &l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0_once, _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0);
v___x_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2490_);
return v___x_2491_;
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2492_;
v_res_2492_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
stack->m_obj
 = v_res_2492_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg___boxed(lean_object* v___y_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
return v_res_2494_;
}
}
lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(lean_object* v_00_u03b1_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v___x_2501_; 
v___x_2501_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
return v___x_2501_;
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2496_ = stack[1].m_obj;
lean_object* v___y_2497_ = stack[2].m_obj;
lean_object* v___y_2498_ = stack[3].m_obj;
lean_object* v___y_2499_ = stack[4].m_obj;
lean_object* v_res_2502_;
v_res_2502_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(lean_box(0), v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
stack->m_obj
 = v_res_2502_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___boxed(lean_object* v_00_u03b1_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(v_00_u03b1_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
return v_res_2509_;
}
}
lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(lean_object* v_category_2510_, lean_object* v_opts_2511_, lean_object* v_act_2512_, lean_object* v_decl_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
lean_inc(v___y_2517_);
lean_inc_ref(v___y_2516_);
lean_inc(v___y_2515_);
lean_inc_ref(v___y_2514_);
v___x_2519_ = lean_apply_4(v_act_2512_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
v___x_2520_ = l_Lean_profileitIOUnsafe___redArg(v_category_2510_, v_opts_2511_, v___x_2519_, v_decl_2513_);
return v___x_2520_;
}
}
LEAN_EXPORT void l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_category_2510_ = stack[0].m_obj;
lean_object* v_opts_2511_ = stack[1].m_obj;
lean_object* v_act_2512_ = stack[2].m_obj;
lean_object* v_decl_2513_ = stack[3].m_obj;
lean_object* v___y_2514_ = stack[4].m_obj;
lean_object* v___y_2515_ = stack[5].m_obj;
lean_object* v___y_2516_ = stack[6].m_obj;
lean_object* v___y_2517_ = stack[7].m_obj;
lean_object* v_res_2521_;
v_res_2521_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v_category_2510_, v_opts_2511_, v_act_2512_, v_decl_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
stack->m_obj
 = v_res_2521_;
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg___boxed(lean_object* v_category_2522_, lean_object* v_opts_2523_, lean_object* v_act_2524_, lean_object* v_decl_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v_category_2522_, v_opts_2523_, v_act_2524_, v_decl_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec_ref(v_opts_2523_);
lean_dec_ref(v_category_2522_);
return v_res_2531_;
}
}
lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(lean_object* v_00_u03b1_2532_, lean_object* v_category_2533_, lean_object* v_opts_2534_, lean_object* v_act_2535_, lean_object* v_decl_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v___x_2542_; 
v___x_2542_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v_category_2533_, v_opts_2534_, v_act_2535_, v_decl_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
return v___x_2542_;
}
}
LEAN_EXPORT void l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_category_2533_ = stack[1].m_obj;
lean_object* v_opts_2534_ = stack[2].m_obj;
lean_object* v_act_2535_ = stack[3].m_obj;
lean_object* v_decl_2536_ = stack[4].m_obj;
lean_object* v___y_2537_ = stack[5].m_obj;
lean_object* v___y_2538_ = stack[6].m_obj;
lean_object* v___y_2539_ = stack[7].m_obj;
lean_object* v___y_2540_ = stack[8].m_obj;
lean_object* v_res_2543_;
v_res_2543_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(lean_box(0), v_category_2533_, v_opts_2534_, v_act_2535_, v_decl_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
stack->m_obj
 = v_res_2543_;
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___boxed(lean_object* v_00_u03b1_2544_, lean_object* v_category_2545_, lean_object* v_opts_2546_, lean_object* v_act_2547_, lean_object* v_decl_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(v_00_u03b1_2544_, v_category_2545_, v_opts_2546_, v_act_2547_, v_decl_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec_ref(v_opts_2546_);
lean_dec_ref(v_category_2545_);
return v_res_2554_;
}
}
lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0(lean_object* v_a_2555_, lean_object* v___x_2556_, lean_object* v_tactic_2557_, lean_object* v_allowFailure_2558_, lean_object* v_cand_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v___x_2565_; 
lean_inc(v___y_2563_);
lean_inc_ref(v___y_2562_);
lean_inc(v___y_2561_);
lean_inc_ref(v___y_2560_);
v___x_2565_ = lean_apply_5(v_a_2555_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, lean_box(0));
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; uint8_t v___x_2567_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec_ref_known(v___x_2565_, 1);
v___x_2567_ = lean_unbox(v_a_2566_);
lean_dec(v_a_2566_);
if (v___x_2567_ == 0)
{
lean_object* v___x_2568_; 
v___x_2568_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(v___x_2556_, v_tactic_2557_, v_allowFailure_2558_, v_cand_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
return v___x_2568_;
}
else
{
lean_object* v___x_2569_; lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
lean_dec_ref(v_cand_2559_);
lean_dec_ref(v_allowFailure_2558_);
lean_dec_ref(v_tactic_2557_);
lean_dec_ref(v___x_2556_);
v___x_2569_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___x_2569_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2569_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
lean_dec_ref(v_cand_2559_);
lean_dec_ref(v_allowFailure_2558_);
lean_dec_ref(v_tactic_2557_);
lean_dec_ref(v___x_2556_);
v_a_2578_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2565_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2565_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2555_ = stack[0].m_obj;
lean_object* v___x_2556_ = stack[1].m_obj;
lean_object* v_tactic_2557_ = stack[2].m_obj;
lean_object* v_allowFailure_2558_ = stack[3].m_obj;
lean_object* v_cand_2559_ = stack[4].m_obj;
lean_object* v___y_2560_ = stack[5].m_obj;
lean_object* v___y_2561_ = stack[6].m_obj;
lean_object* v___y_2562_ = stack[7].m_obj;
lean_object* v___y_2563_ = stack[8].m_obj;
lean_object* v_res_2586_;
v_res_2586_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0(v_a_2555_, v___x_2556_, v_tactic_2557_, v_allowFailure_2558_, v_cand_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
stack->m_obj
 = v_res_2586_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed(lean_object* v_a_2587_, lean_object* v___x_2588_, lean_object* v_tactic_2589_, lean_object* v_allowFailure_2590_, lean_object* v_cand_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0(v_a_2587_, v___x_2588_, v_tactic_2589_, v_allowFailure_2590_, v_cand_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
return v_res_2597_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(lean_object* v_as_2598_, size_t v_i_2599_, size_t v_stop_2600_){
_start:
{
uint8_t v___x_2601_; 
v___x_2601_ = lean_usize_dec_eq(v_i_2599_, v_stop_2600_);
if (v___x_2601_ == 0)
{
lean_object* v___x_2602_; lean_object* v_fst_2603_; uint8_t v___x_2604_; 
v___x_2602_ = lean_array_uget_borrowed(v_as_2598_, v_i_2599_);
v_fst_2603_ = lean_ctor_get(v___x_2602_, 0);
v___x_2604_ = l_List_isEmpty___redArg(v_fst_2603_);
if (v___x_2604_ == 0)
{
size_t v___x_2605_; size_t v___x_2606_; 
v___x_2605_ = ((size_t)1ULL);
v___x_2606_ = lean_usize_add(v_i_2599_, v___x_2605_);
v_i_2599_ = v___x_2606_;
goto _start;
}
else
{
return v___x_2604_;
}
}
else
{
uint8_t v___x_2608_; 
v___x_2608_ = 0;
return v___x_2608_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2598_ = stack[0].m_obj;
size_t v_i_2599_ = stack[1].m_num;
size_t v_stop_2600_ = stack[2].m_num;
uint8_t v_res_2609_;
v_res_2609_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_as_2598_, v_i_2599_, v_stop_2600_);
stack->m_num = v_res_2609_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2___boxed(lean_object* v_as_2610_, lean_object* v_i_2611_, lean_object* v_stop_2612_){
_start:
{
size_t v_i_boxed_2613_; size_t v_stop_boxed_2614_; uint8_t v_res_2615_; lean_object* v_r_2616_; 
v_i_boxed_2613_ = lean_unbox_usize(v_i_2611_);
lean_dec(v_i_2611_);
v_stop_boxed_2614_ = lean_unbox_usize(v_stop_2612_);
lean_dec(v_stop_2612_);
v_res_2615_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_as_2610_, v_i_boxed_2613_, v_stop_boxed_2614_);
lean_dec_ref(v_as_2610_);
v_r_2616_ = lean_box(v_res_2615_);
return v_r_2616_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(lean_object* v_goal_2617_, lean_object* v___x_2618_, size_t v_sz_2619_, size_t v_i_2620_, lean_object* v_bs_2621_){
_start:
{
uint8_t v___x_2622_; 
v___x_2622_ = lean_usize_dec_lt(v_i_2620_, v_sz_2619_);
if (v___x_2622_ == 0)
{
lean_dec_ref(v___x_2618_);
lean_dec(v_goal_2617_);
return v_bs_2621_;
}
else
{
lean_object* v_v_2623_; lean_object* v___x_2624_; lean_object* v_bs_x27_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; size_t v___x_2628_; size_t v___x_2629_; lean_object* v___x_2630_; 
v_v_2623_ = lean_array_uget(v_bs_2621_, v_i_2620_);
v___x_2624_ = lean_unsigned_to_nat(0u);
v_bs_x27_2625_ = lean_array_uset(v_bs_2621_, v_i_2620_, v___x_2624_);
lean_inc_ref(v___x_2618_);
lean_inc(v_goal_2617_);
v___x_2626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2626_, 0, v_goal_2617_);
lean_ctor_set(v___x_2626_, 1, v___x_2618_);
v___x_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
lean_ctor_set(v___x_2627_, 1, v_v_2623_);
v___x_2628_ = ((size_t)1ULL);
v___x_2629_ = lean_usize_add(v_i_2620_, v___x_2628_);
v___x_2630_ = lean_array_uset(v_bs_x27_2625_, v_i_2620_, v___x_2627_);
v_i_2620_ = v___x_2629_;
v_bs_2621_ = v___x_2630_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_2617_ = stack[0].m_obj;
lean_object* v___x_2618_ = stack[1].m_obj;
size_t v_sz_2619_ = stack[2].m_num;
size_t v_i_2620_ = stack[3].m_num;
lean_object* v_bs_2621_ = stack[4].m_obj;
lean_object* v_res_2632_;
v_res_2632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2617_, v___x_2618_, v_sz_2619_, v_i_2620_, v_bs_2621_);
stack->m_obj
 = v_res_2632_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1___boxed(lean_object* v_goal_2633_, lean_object* v___x_2634_, lean_object* v_sz_2635_, lean_object* v_i_2636_, lean_object* v_bs_2637_){
_start:
{
size_t v_sz_boxed_2638_; size_t v_i_boxed_2639_; lean_object* v_res_2640_; 
v_sz_boxed_2638_ = lean_unbox_usize(v_sz_2635_);
lean_dec(v_sz_2635_);
v_i_boxed_2639_ = lean_unbox_usize(v_i_2636_);
lean_dec(v_i_2636_);
v_res_2640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2633_, v___x_2634_, v_sz_boxed_2638_, v_i_boxed_2639_, v_bs_2637_);
return v_res_2640_;
}
}
lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(lean_object* v_leavePercentHeartbeats_2642_, lean_object* v___x_2643_, lean_object* v_tactic_2644_, lean_object* v_allowFailure_2645_, lean_object* v_goal_2646_, uint8_t v_collectAll_2647_, uint8_t v_includeStar_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2642_, v___y_2651_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v___f_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2658_);
lean_dec_ref_known(v___x_2657_, 1);
v___f_2659_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2659_, 0, v_a_2658_);
lean_closure_set(v___f_2659_, 1, v___x_2643_);
lean_closure_set(v___f_2659_, 2, v_tactic_2644_);
lean_closure_set(v___f_2659_, 3, v_allowFailure_2645_);
v___x_2660_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0));
lean_inc(v_goal_2646_);
v___x_2661_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2660_, v_goal_2646_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; lean_object* v___x_2663_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2662_);
lean_dec_ref_known(v___x_2661_, 1);
lean_inc_ref(v___f_2659_);
v___x_2663_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2659_, v_a_2662_, v_collectAll_2647_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
lean_dec(v_a_2662_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v_a_2664_; 
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
if (lean_obj_tag(v_a_2664_) == 0)
{
lean_dec_ref_known(v___x_2663_, 1);
lean_dec_ref(v___f_2659_);
lean_dec(v_goal_2646_);
goto v___jp_2654_;
}
else
{
lean_object* v_val_2665_; lean_object* v___x_2714_; lean_object* v___x_2715_; uint8_t v___x_2716_; 
v_val_2665_ = lean_ctor_get(v_a_2664_, 0);
v___x_2714_ = lean_unsigned_to_nat(0u);
v___x_2715_ = lean_array_get_size(v_val_2665_);
v___x_2716_ = lean_nat_dec_lt(v___x_2714_, v___x_2715_);
if (v___x_2716_ == 0)
{
goto v___jp_2710_;
}
else
{
if (v___x_2716_ == 0)
{
goto v___jp_2710_;
}
else
{
size_t v___x_2717_; size_t v___x_2718_; uint8_t v___x_2719_; 
v___x_2717_ = ((size_t)0ULL);
v___x_2718_ = lean_usize_of_nat(v___x_2715_);
v___x_2719_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_val_2665_, v___x_2717_, v___x_2718_);
if (v___x_2719_ == 0)
{
goto v___jp_2710_;
}
else
{
lean_dec_ref(v___f_2659_);
lean_dec(v_goal_2646_);
return v___x_2663_;
}
}
}
v___jp_2666_:
{
if (v_includeStar_2648_ == 0)
{
lean_dec_ref(v___f_2659_);
lean_dec(v_goal_2646_);
return v___x_2663_;
}
else
{
lean_object* v___x_2667_; 
lean_inc_ref(v_a_2664_);
lean_dec_ref_known(v___x_2663_, 1);
v___x_2667_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2701_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2670_ = v___x_2667_;
v_isShared_2671_ = v_isSharedCheck_2701_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2667_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2701_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; uint8_t v___x_2674_; 
v___x_2672_ = lean_array_get_size(v_a_2668_);
v___x_2673_ = lean_unsigned_to_nat(0u);
v___x_2674_ = lean_nat_dec_eq(v___x_2672_, v___x_2673_);
if (v___x_2674_ == 0)
{
lean_object* v___x_2675_; lean_object* v_mctx_2676_; size_t v_sz_2677_; size_t v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
lean_inc(v_val_2665_);
lean_del_object(v___x_2670_);
lean_dec_ref_known(v_a_2664_, 1);
v___x_2675_ = lean_st_ref_get(v___y_2650_);
v_mctx_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc_ref(v_mctx_2676_);
lean_dec(v___x_2675_);
v_sz_2677_ = lean_array_size(v_a_2668_);
v___x_2678_ = ((size_t)0ULL);
v___x_2679_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2646_, v_mctx_2676_, v_sz_2677_, v___x_2678_, v_a_2668_);
v___x_2680_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2659_, v___x_2679_, v_collectAll_2647_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
lean_dec_ref(v___x_2679_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2697_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2683_ = v___x_2680_;
v_isShared_2684_ = v_isSharedCheck_2697_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2680_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2697_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
if (lean_obj_tag(v_a_2681_) == 0)
{
lean_del_object(v___x_2683_);
lean_dec(v_val_2665_);
goto v___jp_2654_;
}
else
{
lean_object* v_val_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2696_; 
v_val_2685_ = lean_ctor_get(v_a_2681_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v_a_2681_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2687_ = v_a_2681_;
v_isShared_2688_ = v_isSharedCheck_2696_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_val_2685_);
lean_dec(v_a_2681_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2696_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2689_; lean_object* v___x_2691_; 
v___x_2689_ = l_Array_append___redArg(v_val_2665_, v_val_2685_);
lean_dec(v_val_2685_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v___x_2689_);
v___x_2691_ = v___x_2687_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2689_);
v___x_2691_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
lean_object* v___x_2693_; 
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 0, v___x_2691_);
v___x_2693_ = v___x_2683_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2691_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2665_);
return v___x_2680_;
}
}
else
{
lean_object* v___x_2699_; 
lean_dec(v_a_2668_);
lean_dec_ref(v___f_2659_);
lean_dec(v_goal_2646_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 0, v_a_2664_);
v___x_2699_ = v___x_2670_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2664_);
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
else
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
lean_dec_ref_known(v_a_2664_, 1);
lean_dec_ref(v___f_2659_);
lean_dec(v_goal_2646_);
v_a_2702_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2667_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2667_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
}
v___jp_2710_:
{
if (v_collectAll_2647_ == 0)
{
lean_object* v___x_2711_; lean_object* v___x_2712_; uint8_t v___x_2713_; 
v___x_2711_ = lean_array_get_size(v_val_2665_);
v___x_2712_ = lean_unsigned_to_nat(0u);
v___x_2713_ = lean_nat_dec_eq(v___x_2711_, v___x_2712_);
if (v___x_2713_ == 0)
{
lean_dec_ref(v___f_2659_);
lean_dec(v_goal_2646_);
return v___x_2663_;
}
else
{
goto v___jp_2666_;
}
}
else
{
goto v___jp_2666_;
}
}
}
}
else
{
lean_dec_ref(v___f_2659_);
lean_dec(v_goal_2646_);
return v___x_2663_;
}
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec_ref(v___f_2659_);
lean_dec(v_goal_2646_);
v_a_2720_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2661_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2661_);
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
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
lean_dec(v_goal_2646_);
lean_dec_ref(v_allowFailure_2645_);
lean_dec_ref(v_tactic_2644_);
lean_dec_ref(v___x_2643_);
v_a_2728_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2657_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2657_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
v___jp_2654_:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2655_ = lean_box(0);
v___x_2656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2655_);
return v___x_2656_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_leavePercentHeartbeats_2642_ = stack[0].m_obj;
lean_object* v___x_2643_ = stack[1].m_obj;
lean_object* v_tactic_2644_ = stack[2].m_obj;
lean_object* v_allowFailure_2645_ = stack[3].m_obj;
lean_object* v_goal_2646_ = stack[4].m_obj;
uint8_t v_collectAll_2647_ = stack[5].m_num;
uint8_t v_includeStar_2648_ = stack[6].m_num;
lean_object* v___y_2649_ = stack[7].m_obj;
lean_object* v___y_2650_ = stack[8].m_obj;
lean_object* v___y_2651_ = stack[9].m_obj;
lean_object* v___y_2652_ = stack[10].m_obj;
lean_object* v_res_2736_;
v_res_2736_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(v_leavePercentHeartbeats_2642_, v___x_2643_, v_tactic_2644_, v_allowFailure_2645_, v_goal_2646_, v_collectAll_2647_, v_includeStar_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
stack->m_obj
 = v_res_2736_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed(lean_object* v_leavePercentHeartbeats_2737_, lean_object* v___x_2738_, lean_object* v_tactic_2739_, lean_object* v_allowFailure_2740_, lean_object* v_goal_2741_, lean_object* v_collectAll_2742_, lean_object* v_includeStar_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
uint8_t v_collectAll_boxed_2749_; uint8_t v_includeStar_boxed_2750_; lean_object* v_res_2751_; 
v_collectAll_boxed_2749_ = lean_unbox(v_collectAll_2742_);
v_includeStar_boxed_2750_ = lean_unbox(v_includeStar_2743_);
v_res_2751_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(v_leavePercentHeartbeats_2737_, v___x_2738_, v_tactic_2739_, v_allowFailure_2740_, v_goal_2741_, v_collectAll_boxed_2749_, v_includeStar_boxed_2750_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v_leavePercentHeartbeats_2737_);
return v_res_2751_;
}
}
lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2(lean_object* v_goal_2752_, lean_object* v_x_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v___x_2759_; 
v___x_2759_ = l_Lean_MVarId_getType(v_goal_2752_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2768_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2762_ = v___x_2759_;
v_isShared_2763_ = v_isSharedCheck_2768_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2759_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2768_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2764_; lean_object* v___x_2766_; 
v___x_2764_ = l_Lean_MessageData_ofExpr(v_a_2760_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 0, v___x_2764_);
v___x_2766_ = v___x_2762_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v___x_2764_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
v_a_2769_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2759_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2759_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_2752_ = stack[0].m_obj;
lean_object* v_x_2753_ = stack[1].m_obj;
lean_object* v___y_2754_ = stack[2].m_obj;
lean_object* v___y_2755_ = stack[3].m_obj;
lean_object* v___y_2756_ = stack[4].m_obj;
lean_object* v___y_2757_ = stack[5].m_obj;
lean_object* v_res_2777_;
v_res_2777_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2(v_goal_2752_, v_x_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
stack->m_obj
 = v_res_2777_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___boxed(lean_object* v_goal_2778_, lean_object* v_x_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2(v_goal_2778_, v_x_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
lean_dec_ref(v_x_2779_);
return v_res_2785_;
}
}
lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__6(lean_object* v_leavePercentHeartbeats_2786_, lean_object* v___x_2787_, lean_object* v_tactic_2788_, lean_object* v_allowFailure_2789_, lean_object* v_goal_2790_, uint8_t v_collectAll_2791_, uint8_t v_includeStar_2792_, uint8_t v___x_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v___x_2802_; 
v___x_2802_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2786_, v___y_2796_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; lean_object* v___f_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2803_);
lean_dec_ref_known(v___x_2802_, 1);
v___f_2804_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2804_, 0, v_a_2803_);
lean_closure_set(v___f_2804_, 1, v___x_2787_);
lean_closure_set(v___f_2804_, 2, v_tactic_2788_);
lean_closure_set(v___f_2804_, 3, v_allowFailure_2789_);
v___x_2805_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0));
lean_inc(v_goal_2790_);
v___x_2806_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2805_, v_goal_2790_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; lean_object* v___x_2808_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___x_2806_, 1);
lean_inc_ref(v___f_2804_);
v___x_2808_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2804_, v_a_2807_, v_collectAll_2791_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
lean_dec(v_a_2807_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
if (lean_obj_tag(v_a_2809_) == 0)
{
lean_dec_ref_known(v___x_2808_, 1);
lean_dec_ref(v___f_2804_);
lean_dec(v_goal_2790_);
goto v___jp_2799_;
}
else
{
lean_object* v_val_2810_; lean_object* v___x_2860_; lean_object* v___x_2861_; uint8_t v___x_2862_; 
v_val_2810_ = lean_ctor_get(v_a_2809_, 0);
v___x_2860_ = lean_unsigned_to_nat(0u);
v___x_2861_ = lean_array_get_size(v_val_2810_);
v___x_2862_ = lean_nat_dec_lt(v___x_2860_, v___x_2861_);
if (v___x_2862_ == 0)
{
goto v___jp_2856_;
}
else
{
if (v___x_2862_ == 0)
{
goto v___jp_2856_;
}
else
{
size_t v___x_2863_; size_t v___x_2864_; uint8_t v___x_2865_; 
v___x_2863_ = ((size_t)0ULL);
v___x_2864_ = lean_usize_of_nat(v___x_2861_);
v___x_2865_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_val_2810_, v___x_2863_, v___x_2864_);
if (v___x_2865_ == 0)
{
goto v___jp_2856_;
}
else
{
if (v___x_2793_ == 0)
{
goto v___jp_2855_;
}
else
{
lean_dec_ref(v___f_2804_);
lean_dec(v_goal_2790_);
return v___x_2808_;
}
}
}
}
v___jp_2811_:
{
lean_object* v___x_2812_; 
v___x_2812_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2846_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2815_ = v___x_2812_;
v_isShared_2816_ = v_isSharedCheck_2846_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2812_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2846_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; uint8_t v___x_2819_; 
v___x_2817_ = lean_array_get_size(v_a_2813_);
v___x_2818_ = lean_unsigned_to_nat(0u);
v___x_2819_ = lean_nat_dec_eq(v___x_2817_, v___x_2818_);
if (v___x_2819_ == 0)
{
lean_object* v___x_2820_; lean_object* v_mctx_2821_; size_t v_sz_2822_; size_t v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
lean_inc(v_val_2810_);
lean_del_object(v___x_2815_);
lean_dec_ref_known(v_a_2809_, 1);
v___x_2820_ = lean_st_ref_get(v___y_2795_);
v_mctx_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc_ref(v_mctx_2821_);
lean_dec(v___x_2820_);
v_sz_2822_ = lean_array_size(v_a_2813_);
v___x_2823_ = ((size_t)0ULL);
v___x_2824_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2790_, v_mctx_2821_, v_sz_2822_, v___x_2823_, v_a_2813_);
v___x_2825_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2804_, v___x_2824_, v_collectAll_2791_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
lean_dec_ref(v___x_2824_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2842_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2828_ = v___x_2825_;
v_isShared_2829_ = v_isSharedCheck_2842_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2825_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2842_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
if (lean_obj_tag(v_a_2826_) == 0)
{
lean_del_object(v___x_2828_);
lean_dec(v_val_2810_);
goto v___jp_2799_;
}
else
{
lean_object* v_val_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2841_; 
v_val_2830_ = lean_ctor_get(v_a_2826_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v_a_2826_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2832_ = v_a_2826_;
v_isShared_2833_ = v_isSharedCheck_2841_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_val_2830_);
lean_dec(v_a_2826_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2841_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2834_; lean_object* v___x_2836_; 
v___x_2834_ = l_Array_append___redArg(v_val_2810_, v_val_2830_);
lean_dec(v_val_2830_);
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 0, v___x_2834_);
v___x_2836_ = v___x_2832_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2834_);
v___x_2836_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
lean_object* v___x_2838_; 
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 0, v___x_2836_);
v___x_2838_ = v___x_2828_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2836_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2810_);
return v___x_2825_;
}
}
else
{
lean_object* v___x_2844_; 
lean_dec(v_a_2813_);
lean_dec_ref(v___f_2804_);
lean_dec(v_goal_2790_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 0, v_a_2809_);
v___x_2844_ = v___x_2815_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2809_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_dec_ref_known(v_a_2809_, 1);
lean_dec_ref(v___f_2804_);
lean_dec(v_goal_2790_);
v_a_2847_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2812_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2812_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
v___jp_2855_:
{
if (v_includeStar_2792_ == 0)
{
if (v___x_2793_ == 0)
{
lean_inc_ref(v_a_2809_);
lean_dec_ref_known(v___x_2808_, 1);
goto v___jp_2811_;
}
else
{
lean_dec_ref(v___f_2804_);
lean_dec(v_goal_2790_);
return v___x_2808_;
}
}
else
{
lean_inc_ref(v_a_2809_);
lean_dec_ref_known(v___x_2808_, 1);
goto v___jp_2811_;
}
}
v___jp_2856_:
{
if (v_collectAll_2791_ == 0)
{
if (v___x_2793_ == 0)
{
goto v___jp_2855_;
}
else
{
lean_object* v___x_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; 
v___x_2857_ = lean_array_get_size(v_val_2810_);
v___x_2858_ = lean_unsigned_to_nat(0u);
v___x_2859_ = lean_nat_dec_eq(v___x_2857_, v___x_2858_);
if (v___x_2859_ == 0)
{
lean_dec_ref(v___f_2804_);
lean_dec(v_goal_2790_);
return v___x_2808_;
}
else
{
goto v___jp_2855_;
}
}
}
else
{
goto v___jp_2855_;
}
}
}
}
else
{
lean_dec_ref(v___f_2804_);
lean_dec(v_goal_2790_);
return v___x_2808_;
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_dec_ref(v___f_2804_);
lean_dec(v_goal_2790_);
v_a_2866_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2806_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2806_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
else
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_dec(v_goal_2790_);
lean_dec_ref(v_allowFailure_2789_);
lean_dec_ref(v_tactic_2788_);
lean_dec_ref(v___x_2787_);
v_a_2874_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2802_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2802_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
v___jp_2799_:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2800_ = lean_box(0);
v___x_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
return v___x_2801_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_leavePercentHeartbeats_2786_ = stack[0].m_obj;
lean_object* v___x_2787_ = stack[1].m_obj;
lean_object* v_tactic_2788_ = stack[2].m_obj;
lean_object* v_allowFailure_2789_ = stack[3].m_obj;
lean_object* v_goal_2790_ = stack[4].m_obj;
uint8_t v_collectAll_2791_ = stack[5].m_num;
uint8_t v_includeStar_2792_ = stack[6].m_num;
uint8_t v___x_2793_ = stack[7].m_num;
lean_object* v___y_2794_ = stack[8].m_obj;
lean_object* v___y_2795_ = stack[9].m_obj;
lean_object* v___y_2796_ = stack[10].m_obj;
lean_object* v___y_2797_ = stack[11].m_obj;
lean_object* v_res_2882_;
v_res_2882_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__6(v_leavePercentHeartbeats_2786_, v___x_2787_, v_tactic_2788_, v_allowFailure_2789_, v_goal_2790_, v_collectAll_2791_, v_includeStar_2792_, v___x_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
stack->m_obj
 = v_res_2882_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__6___boxed(lean_object* v_leavePercentHeartbeats_2883_, lean_object* v___x_2884_, lean_object* v_tactic_2885_, lean_object* v_allowFailure_2886_, lean_object* v_goal_2887_, lean_object* v_collectAll_2888_, lean_object* v_includeStar_2889_, lean_object* v___x_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
uint8_t v_collectAll_boxed_2896_; uint8_t v_includeStar_boxed_2897_; uint8_t v___x_14211__boxed_2898_; lean_object* v_res_2899_; 
v_collectAll_boxed_2896_ = lean_unbox(v_collectAll_2888_);
v_includeStar_boxed_2897_ = lean_unbox(v_includeStar_2889_);
v___x_14211__boxed_2898_ = lean_unbox(v___x_2890_);
v_res_2899_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__6(v_leavePercentHeartbeats_2883_, v___x_2884_, v_tactic_2885_, v_allowFailure_2886_, v_goal_2887_, v_collectAll_boxed_2896_, v_includeStar_boxed_2897_, v___x_14211__boxed_2898_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
lean_dec(v___y_2894_);
lean_dec_ref(v___y_2893_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v_leavePercentHeartbeats_2883_);
return v_res_2899_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(lean_object* v_e_2900_){
_start:
{
if (lean_obj_tag(v_e_2900_) == 0)
{
uint8_t v___x_2901_; 
v___x_2901_ = 2;
return v___x_2901_;
}
else
{
lean_object* v_a_2902_; 
v_a_2902_ = lean_ctor_get(v_e_2900_, 0);
if (lean_obj_tag(v_a_2902_) == 0)
{
uint8_t v___x_2903_; 
v___x_2903_ = 1;
return v___x_2903_;
}
else
{
uint8_t v___x_2904_; 
v___x_2904_ = 0;
return v___x_2904_;
}
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2900_ = stack[0].m_obj;
uint8_t v_res_2905_;
v_res_2905_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(v_e_2900_);
stack->m_num = v_res_2905_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4___boxed(lean_object* v_e_2906_){
_start:
{
uint8_t v_res_2907_; lean_object* v_r_2908_; 
v_res_2907_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(v_e_2906_);
lean_dec_ref(v_e_2906_);
v_r_2908_ = lean_box(v_res_2907_);
return v_r_2908_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(lean_object* v_cls_2909_, uint8_t v_collapsed_2910_, lean_object* v_tag_2911_, lean_object* v_opts_2912_, uint8_t v_clsEnabled_2913_, lean_object* v_oldTraces_2914_, lean_object* v_msg_2915_, lean_object* v_resStartStop_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v_fst_2922_; lean_object* v_snd_2923_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v_data_2927_; lean_object* v_fst_2938_; lean_object* v_snd_2939_; lean_object* v___x_2940_; uint8_t v___x_2941_; lean_object* v___y_2943_; lean_object* v_a_2944_; uint8_t v___y_2959_; double v___y_2991_; 
v_fst_2922_ = lean_ctor_get(v_resStartStop_2916_, 0);
lean_inc(v_fst_2922_);
v_snd_2923_ = lean_ctor_get(v_resStartStop_2916_, 1);
lean_inc(v_snd_2923_);
lean_dec_ref(v_resStartStop_2916_);
v_fst_2938_ = lean_ctor_get(v_snd_2923_, 0);
lean_inc(v_fst_2938_);
v_snd_2939_ = lean_ctor_get(v_snd_2923_, 1);
lean_inc(v_snd_2939_);
lean_dec(v_snd_2923_);
v___x_2940_ = l_Lean_trace_profiler;
v___x_2941_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_2912_, v___x_2940_);
if (v___x_2941_ == 0)
{
v___y_2959_ = v___x_2941_;
goto v___jp_2958_;
}
else
{
lean_object* v___x_2996_; uint8_t v___x_2997_; 
v___x_2996_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2997_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_2912_, v___x_2996_);
if (v___x_2997_ == 0)
{
lean_object* v___x_2998_; lean_object* v___x_2999_; double v___x_3000_; double v___x_3001_; double v___x_3002_; 
v___x_2998_ = l_Lean_trace_profiler_threshold;
v___x_2999_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_2912_, v___x_2998_);
v___x_3000_ = lean_float_of_nat(v___x_2999_);
v___x_3001_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3);
v___x_3002_ = lean_float_div(v___x_3000_, v___x_3001_);
v___y_2991_ = v___x_3002_;
goto v___jp_2990_;
}
else
{
lean_object* v___x_3003_; lean_object* v___x_3004_; double v___x_3005_; 
v___x_3003_ = l_Lean_trace_profiler_threshold;
v___x_3004_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_2912_, v___x_3003_);
v___x_3005_ = lean_float_of_nat(v___x_3004_);
v___y_2991_ = v___x_3005_;
goto v___jp_2990_;
}
}
v___jp_2924_:
{
lean_object* v___x_2928_; 
lean_inc(v___y_2926_);
v___x_2928_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_2914_, v_data_2927_, v___y_2926_, v___y_2925_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_object* v___x_2929_; 
lean_dec_ref_known(v___x_2928_, 1);
v___x_2929_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_2922_);
return v___x_2929_;
}
else
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
lean_dec(v_fst_2922_);
v_a_2930_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2928_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2928_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
v___jp_2942_:
{
uint8_t v_result_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; double v___x_2948_; lean_object* v_data_2949_; 
v_result_2945_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(v_fst_2922_);
v___x_2946_ = lean_box(v_result_2945_);
v___x_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2946_);
v___x_2948_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0);
lean_inc_ref(v_tag_2911_);
lean_inc_ref(v___x_2947_);
lean_inc(v_cls_2909_);
v_data_2949_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2949_, 0, v_cls_2909_);
lean_ctor_set(v_data_2949_, 1, v___x_2947_);
lean_ctor_set(v_data_2949_, 2, v_tag_2911_);
lean_ctor_set_float(v_data_2949_, sizeof(void*)*3, v___x_2948_);
lean_ctor_set_float(v_data_2949_, sizeof(void*)*3 + 8, v___x_2948_);
lean_ctor_set_uint8(v_data_2949_, sizeof(void*)*3 + 16, v_collapsed_2910_);
if (v___x_2941_ == 0)
{
lean_dec_ref_known(v___x_2947_, 1);
lean_dec(v_snd_2939_);
lean_dec(v_fst_2938_);
lean_dec_ref(v_tag_2911_);
lean_dec(v_cls_2909_);
v___y_2925_ = v_a_2944_;
v___y_2926_ = v___y_2943_;
v_data_2927_ = v_data_2949_;
goto v___jp_2924_;
}
else
{
lean_object* v_data_2950_; double v___x_2951_; double v___x_2952_; 
lean_dec_ref_known(v_data_2949_, 3);
v_data_2950_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2950_, 0, v_cls_2909_);
lean_ctor_set(v_data_2950_, 1, v___x_2947_);
lean_ctor_set(v_data_2950_, 2, v_tag_2911_);
v___x_2951_ = lean_unbox_float(v_fst_2938_);
lean_dec(v_fst_2938_);
lean_ctor_set_float(v_data_2950_, sizeof(void*)*3, v___x_2951_);
v___x_2952_ = lean_unbox_float(v_snd_2939_);
lean_dec(v_snd_2939_);
lean_ctor_set_float(v_data_2950_, sizeof(void*)*3 + 8, v___x_2952_);
lean_ctor_set_uint8(v_data_2950_, sizeof(void*)*3 + 16, v_collapsed_2910_);
v___y_2925_ = v_a_2944_;
v___y_2926_ = v___y_2943_;
v_data_2927_ = v_data_2950_;
goto v___jp_2924_;
}
}
v___jp_2953_:
{
lean_object* v_ref_2954_; lean_object* v___x_2955_; 
v_ref_2954_ = lean_ctor_get(v___y_2919_, 2);
lean_inc(v___y_2920_);
lean_inc_ref(v___y_2919_);
lean_inc(v___y_2918_);
lean_inc_ref(v___y_2917_);
lean_inc(v_fst_2922_);
v___x_2955_ = lean_apply_6(v_msg_2915_, v_fst_2922_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, lean_box(0));
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc(v_a_2956_);
lean_dec_ref_known(v___x_2955_, 1);
v___y_2943_ = v_ref_2954_;
v_a_2944_ = v_a_2956_;
goto v___jp_2942_;
}
else
{
lean_object* v___x_2957_; 
lean_dec_ref_known(v___x_2955_, 1);
v___x_2957_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2);
v___y_2943_ = v_ref_2954_;
v_a_2944_ = v___x_2957_;
goto v___jp_2942_;
}
}
v___jp_2958_:
{
if (v_clsEnabled_2913_ == 0)
{
if (v___y_2959_ == 0)
{
lean_object* v___x_2960_; lean_object* v_traceState_2961_; lean_object* v_env_2962_; lean_object* v_nextMacroScope_2963_; lean_object* v_ngen_2964_; lean_object* v_auxDeclNGen_2965_; lean_object* v_cache_2966_; lean_object* v_recordedDeps_2967_; lean_object* v_messages_2968_; lean_object* v_infoState_2969_; lean_object* v_snapshotTasks_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2989_; 
lean_dec(v_snd_2939_);
lean_dec(v_fst_2938_);
lean_dec_ref(v_msg_2915_);
lean_dec_ref(v_tag_2911_);
lean_dec(v_cls_2909_);
v___x_2960_ = lean_st_ref_take(v___y_2920_);
v_traceState_2961_ = lean_ctor_get(v___x_2960_, 4);
v_env_2962_ = lean_ctor_get(v___x_2960_, 0);
v_nextMacroScope_2963_ = lean_ctor_get(v___x_2960_, 1);
v_ngen_2964_ = lean_ctor_get(v___x_2960_, 2);
v_auxDeclNGen_2965_ = lean_ctor_get(v___x_2960_, 3);
v_cache_2966_ = lean_ctor_get(v___x_2960_, 5);
v_recordedDeps_2967_ = lean_ctor_get(v___x_2960_, 6);
v_messages_2968_ = lean_ctor_get(v___x_2960_, 7);
v_infoState_2969_ = lean_ctor_get(v___x_2960_, 8);
v_snapshotTasks_2970_ = lean_ctor_get(v___x_2960_, 9);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2972_ = v___x_2960_;
v_isShared_2973_ = v_isSharedCheck_2989_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_snapshotTasks_2970_);
lean_inc(v_infoState_2969_);
lean_inc(v_messages_2968_);
lean_inc(v_recordedDeps_2967_);
lean_inc(v_cache_2966_);
lean_inc(v_traceState_2961_);
lean_inc(v_auxDeclNGen_2965_);
lean_inc(v_ngen_2964_);
lean_inc(v_nextMacroScope_2963_);
lean_inc(v_env_2962_);
lean_dec(v___x_2960_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2989_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
uint64_t v_tid_2974_; lean_object* v_traces_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2988_; 
v_tid_2974_ = lean_ctor_get_uint64(v_traceState_2961_, sizeof(void*)*1);
v_traces_2975_ = lean_ctor_get(v_traceState_2961_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v_traceState_2961_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2977_ = v_traceState_2961_;
v_isShared_2978_ = v_isSharedCheck_2988_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_traces_2975_);
lean_dec(v_traceState_2961_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2988_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2979_; lean_object* v___x_2981_; 
v___x_2979_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2914_, v_traces_2975_);
lean_dec_ref(v_traces_2975_);
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 0, v___x_2979_);
v___x_2981_ = v___x_2977_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2979_);
lean_ctor_set_uint64(v_reuseFailAlloc_2987_, sizeof(void*)*1, v_tid_2974_);
v___x_2981_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
lean_object* v___x_2983_; 
if (v_isShared_2973_ == 0)
{
lean_ctor_set(v___x_2972_, 4, v___x_2981_);
v___x_2983_ = v___x_2972_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_env_2962_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_nextMacroScope_2963_);
lean_ctor_set(v_reuseFailAlloc_2986_, 2, v_ngen_2964_);
lean_ctor_set(v_reuseFailAlloc_2986_, 3, v_auxDeclNGen_2965_);
lean_ctor_set(v_reuseFailAlloc_2986_, 4, v___x_2981_);
lean_ctor_set(v_reuseFailAlloc_2986_, 5, v_cache_2966_);
lean_ctor_set(v_reuseFailAlloc_2986_, 6, v_recordedDeps_2967_);
lean_ctor_set(v_reuseFailAlloc_2986_, 7, v_messages_2968_);
lean_ctor_set(v_reuseFailAlloc_2986_, 8, v_infoState_2969_);
lean_ctor_set(v_reuseFailAlloc_2986_, 9, v_snapshotTasks_2970_);
v___x_2983_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = lean_st_ref_put(v___y_2920_, v___x_2983_);
v___x_2985_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_2922_);
return v___x_2985_;
}
}
}
}
}
else
{
goto v___jp_2953_;
}
}
else
{
goto v___jp_2953_;
}
}
v___jp_2990_:
{
double v___x_2992_; double v___x_2993_; double v___x_2994_; uint8_t v___x_2995_; 
v___x_2992_ = lean_unbox_float(v_snd_2939_);
v___x_2993_ = lean_unbox_float(v_fst_2938_);
v___x_2994_ = lean_float_sub(v___x_2992_, v___x_2993_);
v___x_2995_ = lean_float_decLt(v___y_2991_, v___x_2994_);
v___y_2959_ = v___x_2995_;
goto v___jp_2958_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2909_ = stack[0].m_obj;
uint8_t v_collapsed_2910_ = stack[1].m_num;
lean_object* v_tag_2911_ = stack[2].m_obj;
lean_object* v_opts_2912_ = stack[3].m_obj;
uint8_t v_clsEnabled_2913_ = stack[4].m_num;
lean_object* v_oldTraces_2914_ = stack[5].m_obj;
lean_object* v_msg_2915_ = stack[6].m_obj;
lean_object* v_resStartStop_2916_ = stack[7].m_obj;
lean_object* v___y_2917_ = stack[8].m_obj;
lean_object* v___y_2918_ = stack[9].m_obj;
lean_object* v___y_2919_ = stack[10].m_obj;
lean_object* v___y_2920_ = stack[11].m_obj;
lean_object* v_res_3006_;
v_res_3006_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v_cls_2909_, v_collapsed_2910_, v_tag_2911_, v_opts_2912_, v_clsEnabled_2913_, v_oldTraces_2914_, v_msg_2915_, v_resStartStop_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_);
stack->m_obj
 = v_res_3006_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4___boxed(lean_object* v_cls_3007_, lean_object* v_collapsed_3008_, lean_object* v_tag_3009_, lean_object* v_opts_3010_, lean_object* v_clsEnabled_3011_, lean_object* v_oldTraces_3012_, lean_object* v_msg_3013_, lean_object* v_resStartStop_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
uint8_t v_collapsed_boxed_3020_; uint8_t v_clsEnabled_boxed_3021_; lean_object* v_res_3022_; 
v_collapsed_boxed_3020_ = lean_unbox(v_collapsed_3008_);
v_clsEnabled_boxed_3021_ = lean_unbox(v_clsEnabled_3011_);
v_res_3022_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v_cls_3007_, v_collapsed_boxed_3020_, v_tag_3009_, v_opts_3010_, v_clsEnabled_boxed_3021_, v_oldTraces_3012_, v_msg_3013_, v_resStartStop_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec_ref(v_opts_3010_);
return v_res_3022_;
}
}
lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(lean_object* v_goal_3026_, lean_object* v_tactic_3027_, lean_object* v_allowFailure_3028_, lean_object* v_leavePercentHeartbeats_3029_, uint8_t v_includeStar_3030_, uint8_t v_collectAll_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_){
_start:
{
lean_object* v_toCold_3037_; lean_object* v_options_3038_; lean_object* v_inheritedTraceOptions_3039_; uint8_t v_hasTrace_3040_; lean_object* v___x_3041_; 
v_toCold_3037_ = lean_ctor_get(v_a_3034_, 0);
v_options_3038_ = lean_ctor_get(v_toCold_3037_, 2);
v_inheritedTraceOptions_3039_ = lean_ctor_get(v_toCold_3037_, 11);
v_hasTrace_3040_ = lean_ctor_get_uint8(v_options_3038_, sizeof(void*)*1);
v___x_3041_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
if (v_hasTrace_3040_ == 0)
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___f_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3042_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_3034_);
v___x_3043_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___closed__0));
v___x_3044_ = lean_box(v_collectAll_3031_);
v___x_3045_ = lean_box(v_includeStar_3030_);
v___f_3046_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed), 12, 7);
lean_closure_set(v___f_3046_, 0, v_leavePercentHeartbeats_3029_);
lean_closure_set(v___f_3046_, 1, v___x_3043_);
lean_closure_set(v___f_3046_, 2, v_tactic_3027_);
lean_closure_set(v___f_3046_, 3, v_allowFailure_3028_);
lean_closure_set(v___f_3046_, 4, v_goal_3026_);
lean_closure_set(v___f_3046_, 5, v___x_3044_);
lean_closure_set(v___f_3046_, 6, v___x_3045_);
v___x_3047_ = lean_box(0);
v___x_3048_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_3041_, v___x_3042_, v___f_3046_, v___x_3047_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_);
lean_dec_ref(v___x_3042_);
return v___x_3048_;
}
else
{
lean_object* v___f_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; uint8_t v___x_3053_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v_a_3057_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v_a_3072_; 
lean_inc(v_goal_3026_);
v___f_3049_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___boxed), 7, 1);
lean_closure_set(v___f_3049_, 0, v_goal_3026_);
v___x_3050_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_3051_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4));
v___x_3052_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2);
v___x_3053_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3039_, v_options_3038_, v___x_3052_);
if (v___x_3053_ == 0)
{
lean_object* v___x_3137_; uint8_t v___x_3138_; 
v___x_3137_ = l_Lean_trace_profiler;
v___x_3138_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_3038_, v___x_3137_);
if (v___x_3138_ == 0)
{
lean_object* v___x_3139_; uint8_t v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___f_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
lean_dec_ref(v___f_3049_);
v___x_3139_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_3034_);
v___x_3140_ = 0;
v___x_3141_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3141_, 0, v___x_3140_);
lean_ctor_set_uint8(v___x_3141_, 1, v_hasTrace_3040_);
lean_ctor_set_uint8(v___x_3141_, 2, v_hasTrace_3040_);
lean_ctor_set_uint8(v___x_3141_, 3, v_hasTrace_3040_);
v___x_3142_ = lean_box(v_collectAll_3031_);
v___x_3143_ = lean_box(v_includeStar_3030_);
v___f_3144_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed), 12, 7);
lean_closure_set(v___f_3144_, 0, v_leavePercentHeartbeats_3029_);
lean_closure_set(v___f_3144_, 1, v___x_3141_);
lean_closure_set(v___f_3144_, 2, v_tactic_3027_);
lean_closure_set(v___f_3144_, 3, v_allowFailure_3028_);
lean_closure_set(v___f_3144_, 4, v_goal_3026_);
lean_closure_set(v___f_3144_, 5, v___x_3142_);
lean_closure_set(v___f_3144_, 6, v___x_3143_);
v___x_3145_ = lean_box(0);
v___x_3146_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_3041_, v___x_3139_, v___f_3144_, v___x_3145_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_);
lean_dec_ref(v___x_3139_);
return v___x_3146_;
}
else
{
goto v___jp_3081_;
}
}
else
{
goto v___jp_3081_;
}
v___jp_3054_:
{
lean_object* v___x_3058_; double v___x_3059_; double v___x_3060_; double v___x_3061_; double v___x_3062_; double v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3058_ = lean_io_mono_nanos_now();
v___x_3059_ = lean_float_of_nat(v___y_3055_);
v___x_3060_ = lean_float_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3);
v___x_3061_ = lean_float_div(v___x_3059_, v___x_3060_);
v___x_3062_ = lean_float_of_nat(v___x_3058_);
v___x_3063_ = lean_float_div(v___x_3062_, v___x_3060_);
v___x_3064_ = lean_box_float(v___x_3061_);
v___x_3065_ = lean_box_float(v___x_3063_);
v___x_3066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3064_);
lean_ctor_set(v___x_3066_, 1, v___x_3065_);
v___x_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3067_, 0, v_a_3057_);
lean_ctor_set(v___x_3067_, 1, v___x_3066_);
v___x_3068_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v___x_3050_, v_hasTrace_3040_, v___x_3051_, v_options_3038_, v___x_3053_, v___y_3056_, v___f_3049_, v___x_3067_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_);
return v___x_3068_;
}
v___jp_3069_:
{
lean_object* v___x_3073_; double v___x_3074_; double v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3073_ = lean_io_get_num_heartbeats();
v___x_3074_ = lean_float_of_nat(v___y_3071_);
v___x_3075_ = lean_float_of_nat(v___x_3073_);
v___x_3076_ = lean_box_float(v___x_3074_);
v___x_3077_ = lean_box_float(v___x_3075_);
v___x_3078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3076_);
lean_ctor_set(v___x_3078_, 1, v___x_3077_);
v___x_3079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3079_, 0, v_a_3072_);
lean_ctor_set(v___x_3079_, 1, v___x_3078_);
v___x_3080_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v___x_3050_, v_hasTrace_3040_, v___x_3051_, v_options_3038_, v___x_3053_, v___y_3070_, v___f_3049_, v___x_3079_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_);
return v___x_3080_;
}
v___jp_3081_:
{
lean_object* v___x_3082_; lean_object* v_a_3083_; lean_object* v___x_3084_; uint8_t v___x_3085_; 
v___x_3082_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v_a_3035_);
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_a_3083_);
lean_dec_ref(v___x_3082_);
v___x_3084_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3085_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_3038_, v___x_3084_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; lean_object* v___x_3087_; uint8_t v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___f_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3086_ = lean_io_mono_nanos_now();
v___x_3087_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_3034_);
v___x_3088_ = 0;
v___x_3089_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3089_, 0, v___x_3088_);
lean_ctor_set_uint8(v___x_3089_, 1, v_hasTrace_3040_);
lean_ctor_set_uint8(v___x_3089_, 2, v_hasTrace_3040_);
lean_ctor_set_uint8(v___x_3089_, 3, v_hasTrace_3040_);
v___x_3090_ = lean_box(v_collectAll_3031_);
v___x_3091_ = lean_box(v_includeStar_3030_);
v___f_3092_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed), 12, 7);
lean_closure_set(v___f_3092_, 0, v_leavePercentHeartbeats_3029_);
lean_closure_set(v___f_3092_, 1, v___x_3089_);
lean_closure_set(v___f_3092_, 2, v_tactic_3027_);
lean_closure_set(v___f_3092_, 3, v_allowFailure_3028_);
lean_closure_set(v___f_3092_, 4, v_goal_3026_);
lean_closure_set(v___f_3092_, 5, v___x_3090_);
lean_closure_set(v___f_3092_, 6, v___x_3091_);
v___x_3093_ = lean_box(0);
v___x_3094_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_3041_, v___x_3087_, v___f_3092_, v___x_3093_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_);
lean_dec_ref(v___x_3087_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_3094_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3094_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
lean_ctor_set_tag(v___x_3097_, 1);
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
v___y_3055_ = v___x_3086_;
v___y_3056_ = v_a_3083_;
v_a_3057_ = v___x_3100_;
goto v___jp_3054_;
}
}
}
else
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
v_a_3103_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3105_ = v___x_3094_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3094_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
lean_ctor_set_tag(v___x_3105_, 0);
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
v___y_3055_ = v___x_3086_;
v___y_3056_ = v_a_3083_;
v_a_3057_ = v___x_3108_;
goto v___jp_3054_;
}
}
}
}
else
{
lean_object* v___x_3111_; lean_object* v___x_3112_; uint8_t v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___f_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3111_ = lean_io_get_num_heartbeats();
v___x_3112_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_3034_);
v___x_3113_ = 0;
v___x_3114_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3114_, 0, v___x_3113_);
lean_ctor_set_uint8(v___x_3114_, 1, v___x_3085_);
lean_ctor_set_uint8(v___x_3114_, 2, v___x_3085_);
lean_ctor_set_uint8(v___x_3114_, 3, v___x_3085_);
v___x_3115_ = lean_box(v_collectAll_3031_);
v___x_3116_ = lean_box(v_includeStar_3030_);
v___x_3117_ = lean_box(v___x_3085_);
v___f_3118_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__6___boxed), 13, 8);
lean_closure_set(v___f_3118_, 0, v_leavePercentHeartbeats_3029_);
lean_closure_set(v___f_3118_, 1, v___x_3114_);
lean_closure_set(v___f_3118_, 2, v_tactic_3027_);
lean_closure_set(v___f_3118_, 3, v_allowFailure_3028_);
lean_closure_set(v___f_3118_, 4, v_goal_3026_);
lean_closure_set(v___f_3118_, 5, v___x_3115_);
lean_closure_set(v___f_3118_, 6, v___x_3116_);
lean_closure_set(v___f_3118_, 7, v___x_3117_);
v___x_3119_ = lean_box(0);
v___x_3120_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_3041_, v___x_3112_, v___f_3118_, v___x_3119_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_);
lean_dec_ref(v___x_3112_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3120_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3120_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
lean_ctor_set_tag(v___x_3123_, 1);
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
v___y_3070_ = v_a_3083_;
v___y_3071_ = v___x_3111_;
v_a_3072_ = v___x_3126_;
goto v___jp_3069_;
}
}
}
else
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
v_a_3129_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3120_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3120_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
lean_ctor_set_tag(v___x_3131_, 0);
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
v___y_3070_ = v_a_3083_;
v___y_3071_ = v___x_3111_;
v_a_3072_ = v___x_3134_;
goto v___jp_3069_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_3026_ = stack[0].m_obj;
lean_object* v_tactic_3027_ = stack[1].m_obj;
lean_object* v_allowFailure_3028_ = stack[2].m_obj;
lean_object* v_leavePercentHeartbeats_3029_ = stack[3].m_obj;
uint8_t v_includeStar_3030_ = stack[4].m_num;
uint8_t v_collectAll_3031_ = stack[5].m_num;
lean_object* v_a_3032_ = stack[6].m_obj;
lean_object* v_a_3033_ = stack[7].m_obj;
lean_object* v_a_3034_ = stack[8].m_obj;
lean_object* v_a_3035_ = stack[9].m_obj;
lean_object* v_res_3147_;
v_res_3147_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(v_goal_3026_, v_tactic_3027_, v_allowFailure_3028_, v_leavePercentHeartbeats_3029_, v_includeStar_3030_, v_collectAll_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_);
stack->m_obj
 = v_res_3147_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___boxed(lean_object* v_goal_3148_, lean_object* v_tactic_3149_, lean_object* v_allowFailure_3150_, lean_object* v_leavePercentHeartbeats_3151_, lean_object* v_includeStar_3152_, lean_object* v_collectAll_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_){
_start:
{
uint8_t v_includeStar_boxed_3159_; uint8_t v_collectAll_boxed_3160_; lean_object* v_res_3161_; 
v_includeStar_boxed_3159_ = lean_unbox(v_includeStar_3152_);
v_collectAll_boxed_3160_ = lean_unbox(v_collectAll_3153_);
v_res_3161_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(v_goal_3148_, v_tactic_3149_, v_allowFailure_3150_, v_leavePercentHeartbeats_3151_, v_includeStar_boxed_3159_, v_collectAll_boxed_3160_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_);
lean_dec(v_a_3157_);
lean_dec_ref(v_a_3156_);
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
return v_res_3161_;
}
}
lean_object* l_Lean_Meta_LibrarySearch_librarySearch(lean_object* v_goal_3162_, lean_object* v_tactic_3163_, lean_object* v_allowFailure_3164_, lean_object* v_leavePercentHeartbeats_3165_, uint8_t v_includeStar_3166_, uint8_t v_collectAll_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_){
_start:
{
lean_object* v___x_3173_; 
v___x_3173_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(v_goal_3162_, v_tactic_3163_, v_allowFailure_3164_, v_leavePercentHeartbeats_3165_, v_includeStar_3166_, v_collectAll_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_);
return v___x_3173_;
}
}
LEAN_EXPORT void l_Lean_Meta_LibrarySearch_librarySearch_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_3162_ = stack[0].m_obj;
lean_object* v_tactic_3163_ = stack[1].m_obj;
lean_object* v_allowFailure_3164_ = stack[2].m_obj;
lean_object* v_leavePercentHeartbeats_3165_ = stack[3].m_obj;
uint8_t v_includeStar_3166_ = stack[4].m_num;
uint8_t v_collectAll_3167_ = stack[5].m_num;
lean_object* v_a_3168_ = stack[6].m_obj;
lean_object* v_a_3169_ = stack[7].m_obj;
lean_object* v_a_3170_ = stack[8].m_obj;
lean_object* v_a_3171_ = stack[9].m_obj;
lean_object* v_res_3174_;
v_res_3174_ = l_Lean_Meta_LibrarySearch_librarySearch(v_goal_3162_, v_tactic_3163_, v_allowFailure_3164_, v_leavePercentHeartbeats_3165_, v_includeStar_3166_, v_collectAll_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_);
stack->m_obj
 = v_res_3174_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearch___boxed(lean_object* v_goal_3175_, lean_object* v_tactic_3176_, lean_object* v_allowFailure_3177_, lean_object* v_leavePercentHeartbeats_3178_, lean_object* v_includeStar_3179_, lean_object* v_collectAll_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_){
_start:
{
uint8_t v_includeStar_boxed_3186_; uint8_t v_collectAll_boxed_3187_; lean_object* v_res_3188_; 
v_includeStar_boxed_3186_ = lean_unbox(v_includeStar_3179_);
v_collectAll_boxed_3187_ = lean_unbox(v_collectAll_3180_);
v_res_3188_ = l_Lean_Meta_LibrarySearch_librarySearch(v_goal_3175_, v_tactic_3176_, v_allowFailure_3177_, v_leavePercentHeartbeats_3178_, v_includeStar_boxed_3186_, v_collectAll_boxed_3187_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_);
lean_dec(v_a_3184_);
lean_dec_ref(v_a_3183_);
lean_dec(v_a_3182_);
lean_dec_ref(v_a_3181_);
return v_res_3188_;
}
}
lean_object* runtime_initialize_Lean_Meta_LazyDiscrTree(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_SolveByElim(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_Heartbeats(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Try(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_LibrarySearch(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_LazyDiscrTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_SolveByElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_Heartbeats(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Try(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_LibrarySearch_instInhabitedDeclMod_default = _init_l_Lean_Meta_LibrarySearch_instInhabitedDeclMod_default();
l_Lean_Meta_LibrarySearch_instInhabitedDeclMod = _init_l_Lean_Meta_LibrarySearch_instInhabitedDeclMod();
res = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_858108106____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_ext = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_ext);
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_constantsPerImportTask = _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_constantsPerImportTask();
lean_mark_persistent(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_constantsPerImportTask);
res = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2955776588____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_abortSpeculationId = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_abortSpeculationId);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_LibrarySearch(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_LazyDiscrTree(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_SolveByElim(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin);
lean_object* initialize_Lean_Util_Heartbeats(uint8_t builtin);
lean_object* initialize_Init_Grind_Util(uint8_t builtin);
lean_object* initialize_Init_Try(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_LibrarySearch(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_LazyDiscrTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_SolveByElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Heartbeats(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Try(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_LibrarySearch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_LibrarySearch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_LibrarySearch(builtin);
}
#ifdef __cplusplus
}
#endif
