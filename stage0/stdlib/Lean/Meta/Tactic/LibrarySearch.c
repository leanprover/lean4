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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_(){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2____boxed(lean_object* v_a_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_();
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_96_; uint8_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_96_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_));
v___x_97_ = 0;
v___x_98_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__5_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_));
v___x_99_ = l_Lean_registerTraceClass(v___x_96_, v___x_97_, v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2____boxed(lean_object* v_a_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_472600257____hygCtx___hyg_2_();
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(lean_object* v_x_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___lam__0___closed__0));
v___x_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_grindDischarger___lam__0___boxed(lean_object* v_x_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(v_x_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v_x_112_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_grindDischarger(lean_object* v_mvarId_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v___y_150_; uint8_t v___y_151_; lean_object* v_a_156_; lean_object* v___y_160_; lean_object* v___x_170_; 
lean_inc(v_mvarId_143_);
v___x_170_ = l_Lean_MVarId_getType(v_mvarId_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v_a_171_; lean_object* v___x_172_; 
v_a_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc_n(v_a_171_, 2);
lean_dec_ref_known(v___x_170_, 1);
v___x_172_ = l_Lean_Meta_getLevel(v_a_171_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_a_173_);
lean_dec_ref_known(v___x_172_, 1);
v___x_174_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__2));
v___x_175_ = lean_box(0);
v___x_176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_176_, 0, v_a_173_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v___x_177_ = l_Lean_Expr_const___override(v___x_174_, v___x_176_);
v___x_178_ = l_Lean_Expr_app___override(v___x_177_, v_a_171_);
v___x_179_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__3));
v___x_180_ = lean_box(0);
v___x_181_ = l_Lean_MVarId_apply(v_mvarId_143_, v___x_178_, v___x_179_, v___x_180_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_a_182_);
lean_dec_ref_known(v___x_181_, 1);
if (lean_obj_tag(v_a_182_) == 1)
{
lean_object* v_tail_183_; 
v_tail_183_ = lean_ctor_get(v_a_182_, 1);
if (lean_obj_tag(v_tail_183_) == 0)
{
lean_object* v_head_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
lean_inc(v_tail_183_);
v_head_184_ = lean_ctor_get(v_a_182_, 0);
lean_inc(v_head_184_);
lean_dec_ref_known(v_a_182_, 2);
v___x_185_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__4));
v___x_186_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_185_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_208_; 
v_a_187_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_208_ == 0)
{
v___x_189_ = v___x_186_;
v_isShared_190_ = v_isSharedCheck_208_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_186_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_208_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_Meta_Grind_main(v_head_184_, v_a_187_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_206_; 
v_a_192_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_206_ == 0)
{
v___x_194_ = v___x_191_;
v_isShared_195_ = v_isSharedCheck_206_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_191_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_206_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
uint8_t v___x_196_; 
v___x_196_ = l_Lean_Meta_Grind_Result_hasFailed(v_a_192_);
lean_dec(v_a_192_);
if (v___x_196_ == 0)
{
lean_object* v___x_198_; 
if (v_isShared_190_ == 0)
{
lean_ctor_set_tag(v___x_189_, 1);
lean_ctor_set(v___x_189_, 0, v_tail_183_);
v___x_198_ = v___x_189_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_tail_183_);
v___x_198_ = v_reuseFailAlloc_202_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_200_; 
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 0, v___x_198_);
v___x_200_ = v___x_194_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_198_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
else
{
lean_object* v___x_204_; 
lean_del_object(v___x_189_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 0, v___x_180_);
v___x_204_ = v___x_194_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_180_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
else
{
lean_object* v_a_207_; 
lean_del_object(v___x_189_);
v_a_207_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_a_207_);
lean_dec_ref_known(v___x_191_, 1);
v_a_156_ = v_a_207_;
goto v___jp_155_;
}
}
}
else
{
lean_object* v_a_209_; 
lean_dec(v_head_184_);
v_a_209_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_a_209_);
lean_dec_ref_known(v___x_186_, 1);
v_a_156_ = v_a_209_;
goto v___jp_155_;
}
}
else
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(v_a_182_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
lean_dec_ref_known(v_a_182_, 2);
v___y_160_ = v___x_210_;
goto v___jp_159_;
}
}
else
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(v_a_182_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
lean_dec(v_a_182_);
v___y_160_ = v___x_211_;
goto v___jp_159_;
}
}
else
{
lean_object* v_a_212_; 
v_a_212_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_a_212_);
lean_dec_ref_known(v___x_181_, 1);
v_a_156_ = v_a_212_;
goto v___jp_155_;
}
}
else
{
lean_object* v_a_213_; 
lean_dec(v_a_171_);
lean_dec(v_mvarId_143_);
v_a_213_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_a_213_);
lean_dec_ref_known(v___x_172_, 1);
v_a_156_ = v_a_213_;
goto v___jp_155_;
}
}
else
{
lean_object* v_a_214_; 
lean_dec(v_mvarId_143_);
v_a_214_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_a_214_);
lean_dec_ref_known(v___x_170_, 1);
v_a_156_ = v_a_214_;
goto v___jp_155_;
}
v___jp_149_:
{
if (v___y_151_ == 0)
{
lean_object* v___x_152_; lean_object* v___x_153_; 
lean_dec_ref(v___y_150_);
v___x_152_ = lean_box(0);
v___x_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
return v___x_153_;
}
else
{
lean_object* v___x_154_; 
v___x_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_154_, 0, v___y_150_);
return v___x_154_;
}
}
v___jp_155_:
{
uint8_t v___x_157_; 
v___x_157_ = l_Lean_Exception_isInterrupt(v_a_156_);
if (v___x_157_ == 0)
{
uint8_t v___x_158_; 
lean_inc_ref(v_a_156_);
v___x_158_ = l_Lean_Exception_isRuntime(v_a_156_);
v___y_150_ = v_a_156_;
v___y_151_ = v___x_158_;
goto v___jp_149_;
}
else
{
v___y_150_ = v_a_156_;
v___y_151_ = v___x_157_;
goto v___jp_149_;
}
}
v___jp_159_:
{
lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_169_; 
v_a_161_ = lean_ctor_get(v___y_160_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___y_160_);
if (v_isSharedCheck_169_ == 0)
{
v___x_163_ = v___y_160_;
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___y_160_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v_a_165_; lean_object* v___x_167_; 
v_a_165_ = lean_ctor_get(v_a_161_, 0);
lean_inc(v_a_165_);
lean_dec(v_a_161_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 0, v_a_165_);
v___x_167_ = v___x_163_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_a_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_grindDischarger___boxed(lean_object* v_mvarId_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Meta_LibrarySearch_grindDischarger(v_mvarId_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
return v_res_221_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_tryDischarger___lam__1(uint8_t v___x_222_, lean_object* v_x_223_){
_start:
{
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryDischarger___lam__1___boxed(lean_object* v___x_224_, lean_object* v_x_225_){
_start:
{
uint8_t v___x_3817__boxed_226_; uint8_t v_res_227_; lean_object* v_r_228_; 
v___x_3817__boxed_226_ = lean_unbox(v___x_224_);
v_res_227_ = l_Lean_Meta_LibrarySearch_tryDischarger___lam__1(v___x_3817__boxed_226_, v_x_225_);
lean_dec(v_x_225_);
v_r_228_ = lean_box(v_res_227_);
return v_r_228_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_tryDischarger___closed__11(void){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Array_mkArray0___redArg();
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryDischarger(lean_object* v_mvarId_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v___y_272_; uint8_t v___y_273_; lean_object* v_a_278_; lean_object* v___y_282_; lean_object* v___x_292_; 
lean_inc(v_mvarId_265_);
v___x_292_ = l_Lean_MVarId_getType(v_mvarId_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_294_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc_n(v_a_293_, 2);
lean_dec_ref_known(v___x_292_, 1);
v___x_294_ = l_Lean_Meta_getLevel(v_a_293_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_a_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_a_295_);
lean_dec_ref_known(v___x_294_, 1);
v___x_296_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__1));
v___x_297_ = lean_box(0);
v___x_298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_298_, 0, v_a_295_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = l_Lean_Expr_const___override(v___x_296_, v___x_298_);
v___x_300_ = l_Lean_Expr_app___override(v___x_299_, v_a_293_);
v___x_301_ = 0;
v___x_302_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__3));
v___x_303_ = lean_box(0);
v___x_304_ = l_Lean_MVarId_apply(v_mvarId_265_, v___x_300_, v___x_302_, v___x_303_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_355_; 
v_a_305_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_355_ == 0)
{
v___x_307_ = v___x_304_;
v_isShared_308_ = v_isSharedCheck_355_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_304_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_355_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
if (lean_obj_tag(v_a_305_) == 1)
{
lean_object* v_tail_309_; 
v_tail_309_ = lean_ctor_get(v_a_305_, 1);
if (lean_obj_tag(v_tail_309_) == 0)
{
lean_object* v_head_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_351_; 
lean_inc(v_tail_309_);
v_head_310_ = lean_ctor_get(v_a_305_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v_a_305_);
if (v_isSharedCheck_351_ == 0)
{
lean_object* v_unused_352_; 
v_unused_352_ = lean_ctor_get(v_a_305_, 1);
lean_dec(v_unused_352_);
v___x_312_ = v_a_305_;
v_isShared_313_ = v_isSharedCheck_351_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_head_310_);
lean_dec(v_a_305_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_351_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v_ref_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_319_; 
v_ref_314_ = lean_ctor_get(v_a_268_, 2);
v___x_315_ = l_Lean_SourceInfo_fromRef(v_ref_314_, v___x_301_);
v___x_316_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__5));
v___x_317_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__6));
lean_inc(v___x_315_);
if (v_isShared_313_ == 0)
{
lean_ctor_set_tag(v___x_312_, 2);
lean_ctor_set(v___x_312_, 1, v___x_317_);
lean_ctor_set(v___x_312_, 0, v___x_315_);
v___x_319_ = v___x_312_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_315_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v___x_317_);
v___x_319_ = v_reuseFailAlloc_350_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_320_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__8));
v___x_321_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__10));
v___x_322_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_tryDischarger___closed__11, &l_Lean_Meta_LibrarySearch_tryDischarger___closed__11_once, _init_l_Lean_Meta_LibrarySearch_tryDischarger___closed__11);
lean_inc_n(v___x_315_, 2);
v___x_323_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_323_, 0, v___x_315_);
lean_ctor_set(v___x_323_, 1, v___x_321_);
lean_ctor_set(v___x_323_, 2, v___x_322_);
v___x_324_ = l_Lean_Syntax_node1(v___x_315_, v___x_320_, v___x_323_);
v___x_325_ = l_Lean_Syntax_node2(v___x_315_, v___x_316_, v___x_319_, v___x_324_);
v___x_326_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_326_, 0, v___x_325_);
v___x_327_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSuppressedMessages___boxed), 11, 2);
lean_closure_set(v___x_327_, 0, lean_box(0));
lean_closure_set(v___x_327_, 1, v___x_326_);
v___x_328_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___boxed), 9, 2);
lean_closure_set(v___x_328_, 0, v_head_310_);
lean_closure_set(v___x_328_, 1, v___x_327_);
v___x_329_ = lean_box(1);
v___x_330_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__13));
v___x_331_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_331_, 0, v___x_297_);
lean_ctor_set(v___x_331_, 1, v___x_329_);
lean_ctor_set(v___x_331_, 2, v_tail_309_);
lean_ctor_set(v___x_331_, 3, v___x_297_);
lean_ctor_set(v___x_331_, 4, v___x_297_);
lean_ctor_set(v___x_331_, 5, v___x_329_);
lean_ctor_set(v___x_331_, 6, v___x_297_);
v___x_332_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_328_, v___x_330_, v___x_331_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_348_; 
v_a_333_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_348_ == 0)
{
v___x_335_ = v___x_332_;
v_isShared_336_ = v_isSharedCheck_348_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_332_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_348_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v_fst_337_; uint8_t v___x_338_; 
v_fst_337_ = lean_ctor_get(v_a_333_, 0);
lean_inc(v_fst_337_);
lean_dec(v_a_333_);
v___x_338_ = l_List_isEmpty___redArg(v_fst_337_);
lean_dec(v_fst_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_340_; 
lean_del_object(v___x_307_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_303_);
v___x_340_ = v___x_335_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_303_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
else
{
lean_object* v___x_343_; 
if (v_isShared_308_ == 0)
{
lean_ctor_set_tag(v___x_307_, 1);
lean_ctor_set(v___x_307_, 0, v_tail_309_);
v___x_343_ = v___x_307_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_tail_309_);
v___x_343_ = v_reuseFailAlloc_347_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_345_; 
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_343_);
v___x_345_ = v___x_335_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
else
{
lean_object* v_a_349_; 
lean_del_object(v___x_307_);
v_a_349_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_a_349_);
lean_dec_ref_known(v___x_332_, 1);
v_a_278_ = v_a_349_;
goto v___jp_277_;
}
}
}
}
else
{
lean_object* v___x_353_; 
lean_del_object(v___x_307_);
v___x_353_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(v_a_305_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
lean_dec_ref_known(v_a_305_, 2);
v___y_282_ = v___x_353_;
goto v___jp_281_;
}
}
else
{
lean_object* v___x_354_; 
lean_del_object(v___x_307_);
v___x_354_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(v_a_305_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
lean_dec(v_a_305_);
v___y_282_ = v___x_354_;
goto v___jp_281_;
}
}
}
else
{
lean_object* v_a_356_; 
v_a_356_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_a_356_);
lean_dec_ref_known(v___x_304_, 1);
v_a_278_ = v_a_356_;
goto v___jp_277_;
}
}
else
{
lean_object* v_a_357_; 
lean_dec(v_a_293_);
lean_dec(v_mvarId_265_);
v_a_357_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_a_357_);
lean_dec_ref_known(v___x_294_, 1);
v_a_278_ = v_a_357_;
goto v___jp_277_;
}
}
else
{
lean_object* v_a_358_; 
lean_dec(v_mvarId_265_);
v_a_358_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_a_358_);
lean_dec_ref_known(v___x_292_, 1);
v_a_278_ = v_a_358_;
goto v___jp_277_;
}
v___jp_271_:
{
if (v___y_273_ == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; 
lean_dec_ref(v___y_272_);
v___x_274_ = lean_box(0);
v___x_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
return v___x_275_;
}
else
{
lean_object* v___x_276_; 
v___x_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_276_, 0, v___y_272_);
return v___x_276_;
}
}
v___jp_277_:
{
uint8_t v___x_279_; 
v___x_279_ = l_Lean_Exception_isInterrupt(v_a_278_);
if (v___x_279_ == 0)
{
uint8_t v___x_280_; 
lean_inc_ref(v_a_278_);
v___x_280_ = l_Lean_Exception_isRuntime(v_a_278_);
v___y_272_ = v_a_278_;
v___y_273_ = v___x_280_;
goto v___jp_271_;
}
else
{
v___y_272_ = v_a_278_;
v___y_273_ = v___x_279_;
goto v___jp_271_;
}
}
v___jp_281_:
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_291_; 
v_a_283_ = lean_ctor_get(v___y_282_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___y_282_);
if (v_isSharedCheck_291_ == 0)
{
v___x_285_ = v___y_282_;
v_isShared_286_ = v_isSharedCheck_291_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___y_282_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_291_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v_a_287_; lean_object* v___x_289_; 
v_a_287_ = lean_ctor_get(v_a_283_, 0);
lean_inc(v_a_287_);
lean_dec(v_a_283_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v_a_287_);
v___x_289_ = v___x_285_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_287_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryDischarger___boxed(lean_object* v_mvarId_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_Meta_LibrarySearch_tryDischarger(v_mvarId_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__0(lean_object* v_x_366_, lean_object* v_x_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_box(0);
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__0___boxed(lean_object* v_x_375_, lean_object* v_x_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Meta_LibrarySearch_solveByElim___lam__0(v_x_375_, v_x_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v_x_376_);
lean_dec(v_x_375_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__1(lean_object* v_x_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
uint8_t v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_389_ = 0;
v___x_390_ = lean_box(v___x_389_);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__1___boxed(lean_object* v_x_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Meta_LibrarySearch_solveByElim___lam__1(v_x_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v_x_392_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(lean_object* v_msgData_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___x_405_; lean_object* v_env_406_; uint8_t v___x_407_; lean_object* v_env_408_; lean_object* v___x_409_; lean_object* v_toCold_410_; lean_object* v_mctx_411_; lean_object* v_lctx_412_; lean_object* v_options_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_405_ = lean_st_ref_get(v___y_403_);
v_env_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc_ref(v_env_406_);
lean_dec(v___x_405_);
v___x_407_ = 0;
v_env_408_ = l_Lean_Environment_setRecordingDeps(v_env_406_, v___x_407_);
v___x_409_ = lean_st_ref_get(v___y_401_);
v_toCold_410_ = lean_ctor_get(v___y_402_, 0);
v_mctx_411_ = lean_ctor_get(v___x_409_, 0);
lean_inc_ref(v_mctx_411_);
lean_dec(v___x_409_);
v_lctx_412_ = lean_ctor_get(v___y_400_, 2);
v_options_413_ = lean_ctor_get(v_toCold_410_, 2);
lean_inc_ref(v_options_413_);
lean_inc_ref(v_lctx_412_);
v___x_414_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_414_, 0, v_env_408_);
lean_ctor_set(v___x_414_, 1, v_mctx_411_);
lean_ctor_set(v___x_414_, 2, v_lctx_412_);
lean_ctor_set(v___x_414_, 3, v_options_413_);
v___x_415_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
lean_ctor_set(v___x_415_, 1, v_msgData_399_);
v___x_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0___boxed(lean_object* v_msgData_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msgData_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(lean_object* v_msg_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v_ref_430_; lean_object* v___x_431_; lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_440_; 
v_ref_430_ = lean_ctor_get(v___y_427_, 2);
v___x_431_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msg_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
v_a_432_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_440_ == 0)
{
v___x_434_ = v___x_431_;
v_isShared_435_ = v_isSharedCheck_440_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_440_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_438_; 
lean_inc(v_ref_430_);
v___x_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_436_, 0, v_ref_430_);
lean_ctor_set(v___x_436_, 1, v_a_432_);
if (v_isShared_435_ == 0)
{
lean_ctor_set_tag(v___x_434_, 1);
lean_ctor_set(v___x_434_, 0, v___x_436_);
v___x_438_ = v___x_434_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg___boxed(lean_object* v_msg_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v_msg_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
return v_res_447_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__0));
v___x_450_ = l_Lean_stringToMessageData(v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__2(lean_object* v_x_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1);
v___x_458_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_457_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__2___boxed(lean_object* v_x_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Meta_LibrarySearch_solveByElim___lam__2(v_x_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v_x_459_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim(lean_object* v_required_473_, uint8_t v_exfalso_474_, lean_object* v_goals_475_, lean_object* v_maxDepth_476_, uint8_t v_grind_477_, uint8_t v_try_x3f_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v___x_484_; uint8_t v_transparency_485_; lean_object* v___f_486_; lean_object* v___f_487_; lean_object* v___f_488_; uint8_t v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; lean_object* v___y_493_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_484_ = l_Lean_Meta_Context_config(v_a_479_);
v_transparency_485_ = lean_ctor_get_uint8(v___x_484_, 9);
lean_dec_ref(v___x_484_);
v___f_486_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__0));
v___f_487_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__1));
v___f_488_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__2));
v___x_489_ = 1;
v___x_490_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_490_, 0, v_maxDepth_476_);
lean_ctor_set(v___x_490_, 1, v___f_486_);
lean_ctor_set(v___x_490_, 2, v___f_487_);
lean_ctor_set(v___x_490_, 3, v___f_488_);
lean_ctor_set_uint8(v___x_490_, sizeof(void*)*4, v___x_489_);
v___x_491_ = 0;
v___x_512_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__3));
v___x_513_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_513_, 0, v___x_490_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
lean_ctor_set_uint8(v___x_513_, sizeof(void*)*2, v_transparency_485_);
lean_ctor_set_uint8(v___x_513_, sizeof(void*)*2 + 1, v___x_489_);
lean_ctor_set_uint8(v___x_513_, sizeof(void*)*2 + 2, v_exfalso_474_);
v___x_514_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_514_, 0, v___x_513_);
lean_ctor_set_uint8(v___x_514_, sizeof(void*)*1, v___x_489_);
lean_ctor_set_uint8(v___x_514_, sizeof(void*)*1 + 1, v___x_489_);
lean_ctor_set_uint8(v___x_514_, sizeof(void*)*1 + 2, v___x_491_);
lean_ctor_set_uint8(v___x_514_, sizeof(void*)*1 + 3, v___x_491_);
if (v_try_x3f_478_ == 0)
{
if (v_grind_477_ == 0)
{
v___y_493_ = v___x_514_;
goto v___jp_492_;
}
else
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__4));
v___x_516_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v___x_514_, v___x_515_);
v___y_493_ = v___x_516_;
goto v___jp_492_;
}
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__5));
v___x_518_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v___x_514_, v___x_517_);
v___y_493_ = v___x_518_;
goto v___jp_492_;
}
v___jp_492_:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_494_ = lean_box(0);
v___x_495_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__3));
v___x_496_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v___x_491_, v___x_491_, v___x_494_, v___x_494_, v___x_495_, v_a_479_, v_a_480_, v_a_481_, v_a_482_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v_fst_498_; lean_object* v_snd_499_; uint8_t v___x_500_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref_known(v___x_496_, 1);
v_fst_498_ = lean_ctor_get(v_a_497_, 0);
lean_inc(v_fst_498_);
v_snd_499_ = lean_ctor_get(v_a_497_, 1);
lean_inc(v_snd_499_);
lean_dec(v_a_497_);
v___x_500_ = l_List_isEmpty___redArg(v_required_473_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(v___y_493_, v_required_473_);
v___x_502_ = l_Lean_Meta_SolveByElim_solveByElim(v___x_501_, v_fst_498_, v_snd_499_, v_goals_475_, v_a_479_, v_a_480_, v_a_481_, v_a_482_);
return v___x_502_;
}
else
{
lean_object* v___x_503_; 
lean_dec(v_required_473_);
v___x_503_ = l_Lean_Meta_SolveByElim_solveByElim(v___y_493_, v_fst_498_, v_snd_499_, v_goals_475_, v_a_479_, v_a_480_, v_a_481_, v_a_482_);
return v___x_503_;
}
}
else
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
lean_dec_ref(v___y_493_);
lean_dec(v_goals_475_);
lean_dec(v_required_473_);
v_a_504_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_496_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_496_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___boxed(lean_object* v_required_519_, lean_object* v_exfalso_520_, lean_object* v_goals_521_, lean_object* v_maxDepth_522_, lean_object* v_grind_523_, lean_object* v_try_x3f_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
uint8_t v_exfalso_boxed_530_; uint8_t v_grind_boxed_531_; uint8_t v_try_x3f_boxed_532_; lean_object* v_res_533_; 
v_exfalso_boxed_530_ = lean_unbox(v_exfalso_520_);
v_grind_boxed_531_ = lean_unbox(v_grind_523_);
v_try_x3f_boxed_532_ = lean_unbox(v_try_x3f_524_);
v_res_533_ = l_Lean_Meta_LibrarySearch_solveByElim(v_required_519_, v_exfalso_boxed_530_, v_goals_521_, v_maxDepth_522_, v_grind_boxed_531_, v_try_x3f_boxed_532_, v_a_525_, v_a_526_, v_a_527_, v_a_528_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0(lean_object* v_00_u03b1_534_, lean_object* v_msg_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v_msg_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___boxed(lean_object* v_00_u03b1_542_, lean_object* v_msg_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0(v_00_u03b1_542_, v_msg_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx___impl(uint8_t v_x_550_){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = lean_box(v_x_550_);
v___x_552_ = lean_obj_tag_nat(v___x_551_);
lean_dec(v___x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx___impl___boxed(lean_object* v_x_553_){
_start:
{
uint8_t v_x_4__boxed_554_; lean_object* v_res_555_; 
v_x_4__boxed_554_ = lean_unbox(v_x_553_);
v_res_555_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx___impl(v_x_4__boxed_554_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg(lean_object* v_k_556_){
_start:
{
lean_inc(v_k_556_);
return v_k_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg___boxed(lean_object* v_k_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg(v_k_557_);
lean_dec(v_k_557_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim(lean_object* v_motive_559_, lean_object* v_ctorIdx_560_, uint8_t v_t_561_, lean_object* v_h_562_, lean_object* v_k_563_){
_start:
{
lean_inc(v_k_563_);
return v_k_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___boxed(lean_object* v_motive_564_, lean_object* v_ctorIdx_565_, lean_object* v_t_566_, lean_object* v_h_567_, lean_object* v_k_568_){
_start:
{
uint8_t v_t_boxed_569_; lean_object* v_res_570_; 
v_t_boxed_569_ = lean_unbox(v_t_566_);
v_res_570_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorElim(v_motive_564_, v_ctorIdx_565_, v_t_boxed_569_, v_h_567_, v_k_568_);
lean_dec(v_k_568_);
lean_dec(v_ctorIdx_565_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg(lean_object* v_none_571_){
_start:
{
lean_inc(v_none_571_);
return v_none_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg___boxed(lean_object* v_none_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg(v_none_572_);
lean_dec(v_none_572_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim(lean_object* v_motive_574_, uint8_t v_t_575_, lean_object* v_h_576_, lean_object* v_none_577_){
_start:
{
lean_inc(v_none_577_);
return v_none_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___boxed(lean_object* v_motive_578_, lean_object* v_t_579_, lean_object* v_h_580_, lean_object* v_none_581_){
_start:
{
uint8_t v_t_boxed_582_; lean_object* v_res_583_; 
v_t_boxed_582_ = lean_unbox(v_t_579_);
v_res_583_ = l_Lean_Meta_LibrarySearch_DeclMod_none_elim(v_motive_578_, v_t_boxed_582_, v_h_580_, v_none_581_);
lean_dec(v_none_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg(lean_object* v_mp_584_){
_start:
{
lean_inc(v_mp_584_);
return v_mp_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg___boxed(lean_object* v_mp_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg(v_mp_585_);
lean_dec(v_mp_585_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim(lean_object* v_motive_587_, uint8_t v_t_588_, lean_object* v_h_589_, lean_object* v_mp_590_){
_start:
{
lean_inc(v_mp_590_);
return v_mp_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___boxed(lean_object* v_motive_591_, lean_object* v_t_592_, lean_object* v_h_593_, lean_object* v_mp_594_){
_start:
{
uint8_t v_t_boxed_595_; lean_object* v_res_596_; 
v_t_boxed_595_ = lean_unbox(v_t_592_);
v_res_596_ = l_Lean_Meta_LibrarySearch_DeclMod_mp_elim(v_motive_591_, v_t_boxed_595_, v_h_593_, v_mp_594_);
lean_dec(v_mp_594_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg(lean_object* v_mpr_597_){
_start:
{
lean_inc(v_mpr_597_);
return v_mpr_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg___boxed(lean_object* v_mpr_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg(v_mpr_598_);
lean_dec(v_mpr_598_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim(lean_object* v_motive_600_, uint8_t v_t_601_, lean_object* v_h_602_, lean_object* v_mpr_603_){
_start:
{
lean_inc(v_mpr_603_);
return v_mpr_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___boxed(lean_object* v_motive_604_, lean_object* v_t_605_, lean_object* v_h_606_, lean_object* v_mpr_607_){
_start:
{
uint8_t v_t_boxed_608_; lean_object* v_res_609_; 
v_t_boxed_608_ = lean_unbox(v_t_605_);
v_res_609_ = l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim(v_motive_604_, v_t_boxed_608_, v_h_606_, v_mpr_607_);
lean_dec(v_mpr_607_);
return v_res_609_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_DeclMod_ofNat(lean_object* v_n_610_){
_start:
{
lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = lean_nat_dec_le(v_n_610_, v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_613_ = lean_unsigned_to_nat(1u);
v___x_614_ = lean_nat_dec_le(v_n_610_, v___x_613_);
if (v___x_614_ == 0)
{
uint8_t v___x_615_; 
v___x_615_ = 2;
return v___x_615_;
}
else
{
uint8_t v___x_616_; 
v___x_616_ = 1;
return v___x_616_;
}
}
else
{
uint8_t v___x_617_; 
v___x_617_ = 0;
return v___x_617_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ofNat___boxed(lean_object* v_n_618_){
_start:
{
uint8_t v_res_619_; lean_object* v_r_620_; 
v_res_619_ = l_Lean_Meta_LibrarySearch_DeclMod_ofNat(v_n_618_);
lean_dec(v_n_618_);
v_r_620_ = lean_box(v_res_619_);
return v_r_620_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod(uint8_t v_x_621_, uint8_t v_y_622_){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_623_ = lean_box(v_x_621_);
v___x_624_ = lean_obj_tag_nat(v___x_623_);
lean_dec(v___x_623_);
v___x_625_ = lean_box(v_y_622_);
v___x_626_ = lean_obj_tag_nat(v___x_625_);
lean_dec(v___x_625_);
v___x_627_ = lean_nat_dec_eq(v___x_624_, v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod___boxed(lean_object* v_x_628_, lean_object* v_y_629_){
_start:
{
uint8_t v_x_23__boxed_630_; uint8_t v_y_24__boxed_631_; uint8_t v_res_632_; lean_object* v_r_633_; 
v_x_23__boxed_630_ = lean_unbox(v_x_628_);
v_y_24__boxed_631_ = lean_unbox(v_y_629_);
v_res_632_ = l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod(v_x_23__boxed_630_, v_y_24__boxed_631_);
v_r_633_ = lean_box(v_res_632_);
return v_r_633_;
}
}
static uint8_t _init_l_Lean_Meta_LibrarySearch_instInhabitedDeclMod_default(void){
_start:
{
uint8_t v___x_634_; 
v___x_634_ = 0;
return v___x_634_;
}
}
static uint8_t _init_l_Lean_Meta_LibrarySearch_instInhabitedDeclMod(void){
_start:
{
uint8_t v___x_635_; 
v___x_635_ = 0;
return v___x_635_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord(uint8_t v_x_636_, uint8_t v_y_637_){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_638_ = lean_box(v_x_636_);
v___x_639_ = lean_obj_tag_nat(v___x_638_);
lean_dec(v___x_638_);
v___x_640_ = lean_box(v_y_637_);
v___x_641_ = lean_obj_tag_nat(v___x_640_);
lean_dec(v___x_640_);
v___x_642_ = lean_nat_dec_lt(v___x_639_, v___x_641_);
if (v___x_642_ == 0)
{
uint8_t v___x_643_; 
v___x_643_ = lean_nat_dec_eq(v___x_639_, v___x_641_);
if (v___x_643_ == 0)
{
uint8_t v___x_644_; 
v___x_644_ = 2;
return v___x_644_;
}
else
{
uint8_t v___x_645_; 
v___x_645_ = 1;
return v___x_645_;
}
}
else
{
uint8_t v___x_646_; 
v___x_646_ = 0;
return v___x_646_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord___boxed(lean_object* v_x_647_, lean_object* v_y_648_){
_start:
{
uint8_t v_x_33__boxed_649_; uint8_t v_y_34__boxed_650_; uint8_t v_res_651_; lean_object* v_r_652_; 
v_x_33__boxed_649_ = lean_unbox(v_x_647_);
v_y_34__boxed_650_ = lean_unbox(v_y_648_);
v_res_651_ = l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord(v_x_33__boxed_649_, v_y_34__boxed_650_);
v_r_652_ = lean_box(v_res_651_);
return v_r_652_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash(uint8_t v_x_655_){
_start:
{
switch(v_x_655_)
{
case 0:
{
uint64_t v___x_656_; 
v___x_656_ = 0ULL;
return v___x_656_;
}
case 1:
{
uint64_t v___x_657_; 
v___x_657_ = 1ULL;
return v___x_657_;
}
default: 
{
uint64_t v___x_658_; 
v___x_658_ = 2ULL;
return v___x_658_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash___boxed(lean_object* v_x_659_){
_start:
{
uint8_t v_x_40__boxed_660_; uint64_t v_res_661_; lean_object* v_r_662_; 
v_x_40__boxed_660_ = lean_unbox(v_x_659_);
v_res_661_ = l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash(v_x_40__boxed_660_);
v_r_662_ = lean_box_uint64(v_res_661_);
return v_r_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0(lean_object* v_k_665_, lean_object* v_b_666_, lean_object* v_c_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v___x_673_; 
lean_inc(v___y_671_);
lean_inc_ref(v___y_670_);
lean_inc(v___y_669_);
lean_inc_ref(v___y_668_);
v___x_673_ = lean_apply_7(v_k_665_, v_b_666_, v_c_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, lean_box(0));
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0___boxed(lean_object* v_k_674_, lean_object* v_b_675_, lean_object* v_c_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0(v_k_674_, v_b_675_, v_c_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(lean_object* v_type_683_, lean_object* v_k_684_, uint8_t v_cleanupAnnotations_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v___f_691_; uint8_t v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___f_691_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_691_, 0, v_k_684_);
v___x_692_ = 0;
v___x_693_ = lean_box(0);
v___x_694_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_692_, v___x_693_, v_type_683_, v___f_691_, v_cleanupAnnotations_685_, v___x_692_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___x_694_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
v_a_703_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_694_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_694_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___boxed(lean_object* v_type_711_, lean_object* v_k_712_, lean_object* v_cleanupAnnotations_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_719_; lean_object* v_res_720_; 
v_cleanupAnnotations_boxed_719_ = lean_unbox(v_cleanupAnnotations_713_);
v_res_720_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_711_, v_k_712_, v_cleanupAnnotations_boxed_719_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0(lean_object* v_00_u03b1_721_, lean_object* v_type_722_, lean_object* v_k_723_, uint8_t v_cleanupAnnotations_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_722_, v_k_723_, v_cleanupAnnotations_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___boxed(lean_object* v_00_u03b1_731_, lean_object* v_type_732_, lean_object* v_k_733_, lean_object* v_cleanupAnnotations_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_740_; lean_object* v_res_741_; 
v_cleanupAnnotations_boxed_740_ = lean_unbox(v_cleanupAnnotations_734_);
v_res_741_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0(v_00_u03b1_731_, v_type_732_, v_k_733_, v_cleanupAnnotations_boxed_740_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0(lean_object* v_name_748_, lean_object* v_x_749_, lean_object* v_type_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
uint8_t v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_756_ = 0;
v___x_757_ = lean_box(v___x_756_);
lean_inc(v_name_748_);
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v_name_748_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_type_750_, v___x_758_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_809_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_809_ == 0)
{
v___x_762_ = v___x_759_;
v_isShared_763_ = v_isSharedCheck_809_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_759_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_809_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v_key_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
v_key_764_ = lean_ctor_get(v_a_760_, 0);
v___x_765_ = lean_unsigned_to_nat(1u);
v___x_766_ = lean_mk_empty_array_with_capacity(v___x_765_);
lean_inc(v_a_760_);
v___x_767_ = lean_array_push(v___x_766_, v_a_760_);
v___x_768_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__2));
v___x_769_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_764_, v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_771_; 
lean_dec(v_a_760_);
lean_dec(v_name_748_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v___x_767_);
v___x_771_ = v___x_762_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_767_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
else
{
lean_object* v___x_773_; uint8_t v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
lean_del_object(v___x_762_);
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = 1;
v___x_775_ = lean_box(v___x_774_);
lean_inc(v_name_748_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v_name_748_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
lean_inc(v_a_760_);
v___x_777_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_a_760_, v___x_773_, v___x_776_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_779_; uint8_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_a_778_);
lean_dec_ref_known(v___x_777_, 1);
v___x_779_ = lean_array_push(v___x_767_, v_a_778_);
v___x_780_ = 2;
v___x_781_ = lean_box(v___x_780_);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v_name_748_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_a_760_, v___x_765_, v___x_782_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_792_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_792_ == 0)
{
v___x_786_ = v___x_783_;
v_isShared_787_ = v_isSharedCheck_792_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_783_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_792_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_788_ = lean_array_push(v___x_779_, v_a_784_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_788_);
v___x_790_ = v___x_786_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_788_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
else
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
lean_dec_ref(v___x_779_);
v_a_793_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_783_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_783_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_793_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
else
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
lean_dec_ref(v___x_767_);
lean_dec(v_a_760_);
lean_dec(v_name_748_);
v_a_801_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_808_ == 0)
{
v___x_803_ = v___x_777_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_777_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_a_801_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec(v_name_748_);
v_a_810_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_759_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_759_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___boxed(lean_object* v_name_818_, lean_object* v_x_819_, lean_object* v_type_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0(v_name_818_, v_x_819_, v_type_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec_ref(v_x_819_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport(lean_object* v_name_829_, lean_object* v_c_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_){
_start:
{
lean_object* v___f_836_; lean_object* v___x_837_; lean_object* v_env_838_; uint8_t v___x_839_; 
lean_inc_n(v_name_829_, 2);
v___f_836_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___boxed), 8, 1);
lean_closure_set(v___f_836_, 0, v_name_829_);
v___x_837_ = lean_st_ref_get(v_a_834_);
v_env_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc_ref(v_env_838_);
lean_dec(v___x_837_);
v___x_839_ = l_Lean_Linter_isDeprecated(v_env_838_, v_name_829_);
if (v___x_839_ == 0)
{
uint8_t v___x_840_; 
v___x_840_ = l_Lean_Name_isMetaprogramming(v_name_829_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; lean_object* v_type_842_; lean_object* v___x_843_; 
v___x_841_ = l_Lean_AsyncConstantInfo_toConstantVal(v_c_830_);
v_type_842_ = lean_ctor_get(v___x_841_, 2);
lean_inc_ref(v_type_842_);
lean_dec_ref(v___x_841_);
v___x_843_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_842_, v___f_836_, v___x_840_, v_a_831_, v_a_832_, v_a_833_, v_a_834_);
return v___x_843_;
}
else
{
lean_object* v___x_844_; lean_object* v___x_845_; 
lean_dec_ref(v___f_836_);
lean_dec_ref(v_c_830_);
v___x_844_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0));
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
return v___x_845_;
}
}
else
{
lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec_ref(v___f_836_);
lean_dec_ref(v_c_830_);
lean_dec(v_name_829_);
v___x_846_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0));
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
return v___x_847_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___boxed(lean_object* v_name_848_, lean_object* v_c_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport(v_name_848_, v_c_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_858108106____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_857_ = lean_box(0);
v___x_858_ = lean_st_mk_ref(v___x_857_);
v___x_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_858108106____hygCtx___hyg_2____boxed(lean_object* v_a_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_858108106____hygCtx___hyg_2_();
return v_res_861_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_constantsPerImportTask(void){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = lean_unsigned_to_nat(6500u);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2955776588____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_889_ = lean_box(0);
v___x_890_ = lean_st_mk_ref(v___x_889_);
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2955776588____hygCtx___hyg_2____boxed(lean_object* v_a_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2955776588____hygCtx___hyg_2_();
return v_res_893_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1(void){
_start:
{
lean_object* v_droppedRef_895_; lean_object* v___x_896_; 
v_droppedRef_895_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt;
v___x_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_896_, 0, v_droppedRef_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_libSearchFindDecls(lean_object* v_ty_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_903_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_ext;
v___x_904_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__0));
v___x_905_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_droppedKeys));
v___x_906_ = lean_unsigned_to_nat(6500u);
v___x_907_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1, &l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1_once, _init_l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1);
v___x_908_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v___x_903_, v___x_904_, v___x_905_, v___x_906_, v___x_907_, v_ty_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_libSearchFindDecls___boxed(lean_object* v_ty_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_Meta_LibrarySearch_libSearchFindDecls(v_ty_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
return v_res_915_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_919_ = lean_box(0);
v___x_920_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_getStarLemmas___closed__1));
v___x_921_ = l_Lean_mkConst(v___x_920_, v___x_919_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_getStarLemmas(lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_ref_929_; lean_object* v___x_930_; 
v_ref_929_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt;
v___x_930_ = lean_st_ref_get(v_ref_929_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2, &l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2_once, _init_l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2);
v___x_932_ = l_Lean_Meta_LibrarySearch_libSearchFindDecls(v___x_931_, v_a_924_, v_a_925_, v_a_926_, v_a_927_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_945_; 
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_945_ == 0)
{
lean_object* v_unused_946_; 
v_unused_946_ = lean_ctor_get(v___x_932_, 0);
lean_dec(v_unused_946_);
v___x_934_ = v___x_932_;
v_isShared_935_ = v_isSharedCheck_945_;
goto v_resetjp_933_;
}
else
{
lean_dec(v___x_932_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_945_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_936_; 
v___x_936_ = lean_st_ref_get(v_ref_929_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v___x_937_; lean_object* v___x_939_; 
v___x_937_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_getStarLemmas___closed__3));
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v___x_937_);
v___x_939_ = v___x_934_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_937_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
else
{
lean_object* v_val_941_; lean_object* v___x_943_; 
v_val_941_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_val_941_);
lean_dec_ref_known(v___x_936_, 1);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v_val_941_);
v___x_943_ = v___x_934_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_val_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
else
{
return v___x_932_;
}
}
else
{
lean_object* v_val_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
v_val_947_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_930_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_val_947_);
lean_dec(v___x_930_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
lean_ctor_set_tag(v___x_949_, 0);
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_val_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_getStarLemmas___boxed(lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v_a_955_, v_a_956_, v_a_957_, v_a_958_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0(uint8_t v___x_961_, lean_object* v___x_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
if (v___x_961_ == 0)
{
lean_object* v___x_968_; 
v___x_968_ = l_Lean_getRemainingHeartbeats___redArg(v___y_965_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_978_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_978_ == 0)
{
v___x_971_ = v___x_968_;
v_isShared_972_ = v_isSharedCheck_978_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_968_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_978_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
uint8_t v___x_973_; lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_973_ = lean_nat_dec_lt(v_a_969_, v___x_962_);
lean_dec(v_a_969_);
v___x_974_ = lean_box(v___x_973_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_974_);
v___x_976_ = v___x_971_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
else
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
v_a_979_ = lean_ctor_get(v___x_968_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_968_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_968_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
else
{
uint8_t v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_987_ = 0;
v___x_988_ = lean_box(v___x_987_);
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0___boxed(lean_object* v___x_990_, lean_object* v___x_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
uint8_t v___x_649__boxed_997_; lean_object* v_res_998_; 
v___x_649__boxed_997_ = lean_unbox(v___x_990_);
v_res_998_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0(v___x_649__boxed_997_, v___x_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___x_991_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(lean_object* v_leavePercent_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Lean_getMaxHeartbeats___redArg(v_a_1000_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1004_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_a_1003_);
lean_dec_ref_known(v___x_1002_, 1);
v___x_1004_ = l_Lean_getRemainingHeartbeats___redArg(v_a_1000_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1019_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1007_ = v___x_1004_;
v_isShared_1008_ = v_isSharedCheck_1019_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_1004_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1019_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; uint8_t v___x_1013_; lean_object* v___x_1014_; lean_object* v___y_1015_; lean_object* v___x_1017_; 
v___x_1009_ = lean_nat_mul(v_a_1005_, v_leavePercent_999_);
lean_dec(v_a_1005_);
v___x_1010_ = lean_unsigned_to_nat(100u);
v___x_1011_ = lean_nat_div(v___x_1009_, v___x_1010_);
lean_dec(v___x_1009_);
v___x_1012_ = lean_unsigned_to_nat(0u);
v___x_1013_ = lean_nat_dec_eq(v_a_1003_, v___x_1012_);
lean_dec(v_a_1003_);
v___x_1014_ = lean_box(v___x_1013_);
v___y_1015_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___y_1015_, 0, v___x_1014_);
lean_closure_set(v___y_1015_, 1, v___x_1011_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v___y_1015_);
v___x_1017_ = v___x_1007_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___y_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
lean_dec(v_a_1003_);
v_a_1020_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_1004_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1004_);
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
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
v_a_1028_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1002_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1002_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___boxed(lean_object* v_leavePercent_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercent_1036_, v_a_1037_);
lean_dec_ref(v_a_1037_);
lean_dec(v_leavePercent_1036_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck(lean_object* v_leavePercent_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercent_1040_, v_a_1043_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___boxed(lean_object* v_leavePercent_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck(v_leavePercent_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_leavePercent_1047_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(lean_object* v_upperBound_1054_, lean_object* v_x_1055_, lean_object* v_f_1056_, lean_object* v_y_1057_, lean_object* v_g_1058_, lean_object* v_a_1059_, lean_object* v_b_1060_){
_start:
{
uint8_t v___x_1061_; 
v___x_1061_ = lean_nat_dec_lt(v_a_1059_, v_upperBound_1054_);
if (v___x_1061_ == 0)
{
lean_dec(v_a_1059_);
lean_dec(v_g_1058_);
lean_dec(v_f_1056_);
return v_b_1060_;
}
else
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1062_ = lean_array_fget_borrowed(v_x_1055_, v_a_1059_);
lean_inc(v_f_1056_);
lean_inc(v___x_1062_);
v___x_1063_ = lean_apply_1(v_f_1056_, v___x_1062_);
v___x_1064_ = lean_array_push(v_b_1060_, v___x_1063_);
v___x_1065_ = lean_array_fget_borrowed(v_y_1057_, v_a_1059_);
lean_inc(v_g_1058_);
lean_inc(v___x_1065_);
v___x_1066_ = lean_apply_1(v_g_1058_, v___x_1065_);
v___x_1067_ = lean_array_push(v___x_1064_, v___x_1066_);
v___x_1068_ = lean_unsigned_to_nat(1u);
v___x_1069_ = lean_nat_add(v_a_1059_, v___x_1068_);
lean_dec(v_a_1059_);
v_a_1059_ = v___x_1069_;
v_b_1060_ = v___x_1067_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg___boxed(lean_object* v_upperBound_1071_, lean_object* v_x_1072_, lean_object* v_f_1073_, lean_object* v_y_1074_, lean_object* v_g_1075_, lean_object* v_a_1076_, lean_object* v_b_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v_upperBound_1071_, v_x_1072_, v_f_1073_, v_y_1074_, v_g_1075_, v_a_1076_, v_b_1077_);
lean_dec_ref(v_y_1074_);
lean_dec_ref(v_x_1072_);
lean_dec(v_upperBound_1071_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(lean_object* v_g_1079_, size_t v_sz_1080_, size_t v_i_1081_, lean_object* v_bs_1082_){
_start:
{
uint8_t v___x_1083_; 
v___x_1083_ = lean_usize_dec_lt(v_i_1081_, v_sz_1080_);
if (v___x_1083_ == 0)
{
lean_dec(v_g_1079_);
return v_bs_1082_;
}
else
{
lean_object* v_v_1084_; lean_object* v___x_1085_; lean_object* v_bs_x27_1086_; lean_object* v___x_1087_; size_t v___x_1088_; size_t v___x_1089_; lean_object* v___x_1090_; 
v_v_1084_ = lean_array_uget(v_bs_1082_, v_i_1081_);
v___x_1085_ = lean_unsigned_to_nat(0u);
v_bs_x27_1086_ = lean_array_uset(v_bs_1082_, v_i_1081_, v___x_1085_);
lean_inc(v_g_1079_);
v___x_1087_ = lean_apply_1(v_g_1079_, v_v_1084_);
v___x_1088_ = ((size_t)1ULL);
v___x_1089_ = lean_usize_add(v_i_1081_, v___x_1088_);
v___x_1090_ = lean_array_uset(v_bs_x27_1086_, v_i_1081_, v___x_1087_);
v_i_1081_ = v___x_1089_;
v_bs_1082_ = v___x_1090_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg___boxed(lean_object* v_g_1092_, lean_object* v_sz_1093_, lean_object* v_i_1094_, lean_object* v_bs_1095_){
_start:
{
size_t v_sz_boxed_1096_; size_t v_i_boxed_1097_; lean_object* v_res_1098_; 
v_sz_boxed_1096_ = lean_unbox_usize(v_sz_1093_);
lean_dec(v_sz_1093_);
v_i_boxed_1097_ = lean_unbox_usize(v_i_1094_);
lean_dec(v_i_1094_);
v_res_1098_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1092_, v_sz_boxed_1096_, v_i_boxed_1097_, v_bs_1095_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___redArg(lean_object* v_f_1099_, lean_object* v_x_1100_, lean_object* v_g_1101_, lean_object* v_y_1102_){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v_res_1106_; lean_object* v___y_1108_; uint8_t v___x_1122_; 
v___x_1103_ = lean_array_get_size(v_x_1100_);
v___x_1104_ = lean_array_get_size(v_y_1102_);
v___x_1105_ = lean_nat_add(v___x_1103_, v___x_1104_);
v_res_1106_ = lean_mk_empty_array_with_capacity(v___x_1105_);
lean_dec(v___x_1105_);
v___x_1122_ = lean_nat_dec_le(v___x_1103_, v___x_1104_);
if (v___x_1122_ == 0)
{
v___y_1108_ = v___x_1104_;
goto v___jp_1107_;
}
else
{
v___y_1108_ = v___x_1103_;
goto v___jp_1107_;
}
v___jp_1107_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1109_ = lean_unsigned_to_nat(0u);
lean_inc(v_g_1101_);
lean_inc(v_f_1099_);
v___x_1110_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v___y_1108_, v_x_1100_, v_f_1099_, v_y_1102_, v_g_1101_, v___x_1109_, v_res_1106_);
v___x_1111_ = lean_nat_dec_lt(v___y_1108_, v___x_1103_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; size_t v_sz_1113_; size_t v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_dec(v_f_1099_);
v___x_1112_ = l_Array_extract___redArg(v_y_1102_, v___y_1108_, v___x_1104_);
v_sz_1113_ = lean_array_size(v___x_1112_);
v___x_1114_ = ((size_t)0ULL);
v___x_1115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1101_, v_sz_1113_, v___x_1114_, v___x_1112_);
v___x_1116_ = l_Array_append___redArg(v___x_1110_, v___x_1115_);
lean_dec_ref(v___x_1115_);
return v___x_1116_;
}
else
{
lean_object* v___x_1117_; size_t v_sz_1118_; size_t v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_dec(v_g_1101_);
v___x_1117_ = l_Array_extract___redArg(v_x_1100_, v___y_1108_, v___x_1103_);
v_sz_1118_ = lean_array_size(v___x_1117_);
v___x_1119_ = ((size_t)0ULL);
v___x_1120_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_f_1099_, v_sz_1118_, v___x_1119_, v___x_1117_);
v___x_1121_ = l_Array_append___redArg(v___x_1110_, v___x_1120_);
lean_dec_ref(v___x_1120_);
return v___x_1121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___redArg___boxed(lean_object* v_f_1123_, lean_object* v_x_1124_, lean_object* v_g_1125_, lean_object* v_y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v_f_1123_, v_x_1124_, v_g_1125_, v_y_1126_);
lean_dec_ref(v_y_1126_);
lean_dec_ref(v_x_1124_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith(lean_object* v_00_u03b1_1128_, lean_object* v_00_u03b2_1129_, lean_object* v_00_u03b3_1130_, lean_object* v_f_1131_, lean_object* v_x_1132_, lean_object* v_g_1133_, lean_object* v_y_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v_f_1131_, v_x_1132_, v_g_1133_, v_y_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___boxed(lean_object* v_00_u03b1_1136_, lean_object* v_00_u03b2_1137_, lean_object* v_00_u03b3_1138_, lean_object* v_f_1139_, lean_object* v_x_1140_, lean_object* v_g_1141_, lean_object* v_y_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_Meta_LibrarySearch_interleaveWith(v_00_u03b1_1136_, v_00_u03b2_1137_, v_00_u03b3_1138_, v_f_1139_, v_x_1140_, v_g_1141_, v_y_1142_);
lean_dec_ref(v_y_1142_);
lean_dec_ref(v_x_1140_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0(lean_object* v_00_u03b2_1144_, lean_object* v_00_u03b3_1145_, lean_object* v_g_1146_, size_t v_sz_1147_, size_t v_i_1148_, lean_object* v_bs_1149_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1146_, v_sz_1147_, v_i_1148_, v_bs_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___boxed(lean_object* v_00_u03b2_1151_, lean_object* v_00_u03b3_1152_, lean_object* v_g_1153_, lean_object* v_sz_1154_, lean_object* v_i_1155_, lean_object* v_bs_1156_){
_start:
{
size_t v_sz_boxed_1157_; size_t v_i_boxed_1158_; lean_object* v_res_1159_; 
v_sz_boxed_1157_ = lean_unbox_usize(v_sz_1154_);
lean_dec(v_sz_1154_);
v_i_boxed_1158_ = lean_unbox_usize(v_i_1155_);
lean_dec(v_i_1155_);
v_res_1159_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0(v_00_u03b2_1151_, v_00_u03b3_1152_, v_g_1153_, v_sz_boxed_1157_, v_i_boxed_1158_, v_bs_1156_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1(lean_object* v_00_u03b3_1160_, lean_object* v_upperBound_1161_, lean_object* v_00_u03b1_1162_, lean_object* v_x_1163_, lean_object* v_f_1164_, lean_object* v_00_u03b2_1165_, lean_object* v_y_1166_, lean_object* v_g_1167_, lean_object* v_inst_1168_, lean_object* v_R_1169_, lean_object* v_a_1170_, lean_object* v_b_1171_, lean_object* v_c_1172_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v_upperBound_1161_, v_x_1163_, v_f_1164_, v_y_1166_, v_g_1167_, v_a_1170_, v_b_1171_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___boxed(lean_object* v_00_u03b3_1174_, lean_object* v_upperBound_1175_, lean_object* v_00_u03b1_1176_, lean_object* v_x_1177_, lean_object* v_f_1178_, lean_object* v_00_u03b2_1179_, lean_object* v_y_1180_, lean_object* v_g_1181_, lean_object* v_inst_1182_, lean_object* v_R_1183_, lean_object* v_a_1184_, lean_object* v_b_1185_, lean_object* v_c_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1(v_00_u03b3_1174_, v_upperBound_1175_, v_00_u03b1_1176_, v_x_1177_, v_f_1178_, v_00_u03b2_1179_, v_y_1180_, v_g_1181_, v_inst_1182_, v_R_1183_, v_a_1184_, v_b_1185_, v_c_1186_);
lean_dec_ref(v_y_1180_);
lean_dec_ref(v_x_1177_);
lean_dec(v_upperBound_1175_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_));
v___x_1196_ = l_Lean_registerInternalExceptionId(v___x_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2____boxed(lean_object* v_a_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_();
return v_res_1198_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1199_ = lean_box(0);
v___x_1200_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_abortSpeculationId;
v___x_1201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
lean_ctor_set(v___x_1201_, 1, v___x_1199_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___redArg(lean_object* v_inst_1202_){
_start:
{
lean_object* v_throw_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v_throw_1203_ = lean_ctor_get(v_inst_1202_, 0);
lean_inc(v_throw_1203_);
lean_dec_ref(v_inst_1202_);
v___x_1204_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0, &l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0_once, _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0);
v___x_1205_ = lean_apply_2(v_throw_1203_, lean_box(0), v___x_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation(lean_object* v_m_1206_, lean_object* v_00_u03b1_1207_, lean_object* v_inst_1208_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_Meta_LibrarySearch_abortSpeculation___redArg(v_inst_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_isAbortSpeculation(lean_object* v_x_1210_){
_start:
{
if (lean_obj_tag(v_x_1210_) == 1)
{
lean_object* v_id_1211_; lean_object* v___x_1212_; uint8_t v___x_1213_; 
v_id_1211_ = lean_ctor_get(v_x_1210_, 0);
v___x_1212_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_abortSpeculationId;
v___x_1213_ = l_Lean_instBEqInternalExceptionId_beq(v_id_1211_, v___x_1212_);
return v___x_1213_;
}
else
{
uint8_t v___x_1214_; 
v___x_1214_ = 0;
return v___x_1214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_isAbortSpeculation___boxed(lean_object* v_x_1215_){
_start:
{
uint8_t v_res_1216_; lean_object* v_r_1217_; 
v_res_1216_ = l_Lean_Meta_LibrarySearch_isAbortSpeculation(v_x_1215_);
lean_dec_ref(v_x_1215_);
v_r_1217_ = lean_box(v_res_1216_);
return v_r_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(lean_object* v_x_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_Meta_saveState___redArg(v___y_1220_, v___y_1222_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v___x_1226_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_a_1225_);
lean_dec_ref_known(v___x_1224_, 1);
lean_inc(v___y_1222_);
lean_inc_ref(v___y_1221_);
lean_inc(v___y_1220_);
lean_inc_ref(v___y_1219_);
v___x_1226_ = lean_apply_5(v_x_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, lean_box(0));
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1235_; 
lean_dec(v_a_1225_);
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1229_ = v___x_1226_;
v_isShared_1230_ = v_isSharedCheck_1235_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1226_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1235_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1231_; lean_object* v___x_1233_; 
v___x_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1231_, 0, v_a_1227_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v___x_1231_);
v___x_1233_ = v___x_1229_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1231_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
else
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1265_; 
v_a_1236_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1238_ = v___x_1226_;
v_isShared_1239_ = v_isSharedCheck_1265_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1226_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1265_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
uint8_t v___y_1241_; uint8_t v___x_1263_; 
v___x_1263_ = l_Lean_Exception_isInterrupt(v_a_1236_);
if (v___x_1263_ == 0)
{
uint8_t v___x_1264_; 
lean_inc(v_a_1236_);
v___x_1264_ = l_Lean_Exception_isRuntime(v_a_1236_);
v___y_1241_ = v___x_1264_;
goto v___jp_1240_;
}
else
{
v___y_1241_ = v___x_1263_;
goto v___jp_1240_;
}
v___jp_1240_:
{
if (v___y_1241_ == 0)
{
lean_object* v___x_1242_; 
lean_del_object(v___x_1238_);
lean_dec(v_a_1236_);
v___x_1242_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1225_, v___y_1220_, v___y_1222_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1250_; 
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1250_ == 0)
{
lean_object* v_unused_1251_; 
v_unused_1251_ = lean_ctor_get(v___x_1242_, 0);
lean_dec(v_unused_1251_);
v___x_1244_ = v___x_1242_;
v_isShared_1245_ = v_isSharedCheck_1250_;
goto v_resetjp_1243_;
}
else
{
lean_dec(v___x_1242_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1250_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1246_; lean_object* v___x_1248_; 
v___x_1246_ = lean_box(0);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1246_);
v___x_1248_ = v___x_1244_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1246_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
v_a_1252_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1242_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1242_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
else
{
lean_object* v___x_1261_; 
lean_dec(v_a_1225_);
if (v_isShared_1239_ == 0)
{
v___x_1261_ = v___x_1238_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1236_);
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
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec_ref(v_x_1218_);
v_a_1266_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1224_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1224_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg___boxed(lean_object* v_x_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v_x_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0(lean_object* v_00_u03b1_1281_, lean_object* v_x_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v_x_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___boxed(lean_object* v_00_u03b1_1289_, lean_object* v_x_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0(v_00_u03b1_1289_, v_x_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(lean_object* v_e_1297_, lean_object* v___y_1298_){
_start:
{
uint8_t v___x_1300_; 
v___x_1300_ = l_Lean_Expr_hasMVar(v_e_1297_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; 
v___x_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1301_, 0, v_e_1297_);
return v___x_1301_;
}
else
{
lean_object* v___x_1302_; lean_object* v_mctx_1303_; lean_object* v___x_1304_; lean_object* v_fst_1305_; lean_object* v_snd_1306_; lean_object* v___x_1307_; lean_object* v_cache_1308_; lean_object* v_zetaDeltaFVarIds_1309_; lean_object* v_postponed_1310_; lean_object* v_diag_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1320_; 
v___x_1302_ = lean_st_ref_get(v___y_1298_);
v_mctx_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc_ref(v_mctx_1303_);
lean_dec(v___x_1302_);
v___x_1304_ = l_Lean_instantiateMVarsCore(v_mctx_1303_, v_e_1297_);
v_fst_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_fst_1305_);
v_snd_1306_ = lean_ctor_get(v___x_1304_, 1);
lean_inc(v_snd_1306_);
lean_dec_ref(v___x_1304_);
v___x_1307_ = lean_st_ref_take(v___y_1298_);
v_cache_1308_ = lean_ctor_get(v___x_1307_, 1);
v_zetaDeltaFVarIds_1309_ = lean_ctor_get(v___x_1307_, 2);
v_postponed_1310_ = lean_ctor_get(v___x_1307_, 3);
v_diag_1311_ = lean_ctor_get(v___x_1307_, 4);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1320_ == 0)
{
lean_object* v_unused_1321_; 
v_unused_1321_ = lean_ctor_get(v___x_1307_, 0);
lean_dec(v_unused_1321_);
v___x_1313_ = v___x_1307_;
v_isShared_1314_ = v_isSharedCheck_1320_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_diag_1311_);
lean_inc(v_postponed_1310_);
lean_inc(v_zetaDeltaFVarIds_1309_);
lean_inc(v_cache_1308_);
lean_dec(v___x_1307_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1320_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v_snd_1306_);
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_snd_1306_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_cache_1308_);
lean_ctor_set(v_reuseFailAlloc_1319_, 2, v_zetaDeltaFVarIds_1309_);
lean_ctor_set(v_reuseFailAlloc_1319_, 3, v_postponed_1310_);
lean_ctor_set(v_reuseFailAlloc_1319_, 4, v_diag_1311_);
v___x_1316_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = lean_st_ref_put(v___y_1298_, v___x_1316_);
v___x_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1318_, 0, v_fst_1305_);
return v___x_1318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg___boxed(lean_object* v_e_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_e_1322_, v___y_1323_);
lean_dec(v___y_1323_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1(lean_object* v_e_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_e_1326_, v___y_1328_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___boxed(lean_object* v_e_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1(v_e_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0(lean_object* v___x_1340_, lean_object* v_x_1341_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1340_);
lean_ctor_set(v___x_1342_, 1, v_x_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(lean_object* v___x_1343_, size_t v_sz_1344_, size_t v_i_1345_, lean_object* v_bs_1346_){
_start:
{
uint8_t v___x_1347_; 
v___x_1347_ = lean_usize_dec_lt(v_i_1345_, v_sz_1344_);
if (v___x_1347_ == 0)
{
lean_dec_ref(v___x_1343_);
return v_bs_1346_;
}
else
{
lean_object* v_v_1348_; lean_object* v___x_1349_; lean_object* v_bs_x27_1350_; lean_object* v___x_1351_; size_t v___x_1352_; size_t v___x_1353_; lean_object* v___x_1354_; 
v_v_1348_ = lean_array_uget(v_bs_1346_, v_i_1345_);
v___x_1349_ = lean_unsigned_to_nat(0u);
v_bs_x27_1350_ = lean_array_uset(v_bs_1346_, v_i_1345_, v___x_1349_);
lean_inc_ref(v___x_1343_);
v___x_1351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1343_);
lean_ctor_set(v___x_1351_, 1, v_v_1348_);
v___x_1352_ = ((size_t)1ULL);
v___x_1353_ = lean_usize_add(v_i_1345_, v___x_1352_);
v___x_1354_ = lean_array_uset(v_bs_x27_1350_, v_i_1345_, v___x_1351_);
v_i_1345_ = v___x_1353_;
v_bs_1346_ = v___x_1354_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2___boxed(lean_object* v___x_1356_, lean_object* v_sz_1357_, lean_object* v_i_1358_, lean_object* v_bs_1359_){
_start:
{
size_t v_sz_boxed_1360_; size_t v_i_boxed_1361_; lean_object* v_res_1362_; 
v_sz_boxed_1360_ = lean_unbox_usize(v_sz_1357_);
lean_dec(v_sz_1357_);
v_i_boxed_1361_ = lean_unbox_usize(v_i_1358_);
lean_dec(v_i_1358_);
v_res_1362_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(v___x_1356_, v_sz_boxed_1360_, v_i_boxed_1361_, v_bs_1359_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm(lean_object* v_searchFn_1363_, lean_object* v_goal_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v___x_1370_; 
lean_inc(v_goal_1364_);
v___x_1370_ = l_Lean_MVarId_getType(v_goal_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v_a_1371_; lean_object* v___x_1372_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc(v_a_1371_);
lean_dec_ref_known(v___x_1370_, 1);
lean_inc_ref(v_searchFn_1363_);
lean_inc(v_a_1368_);
lean_inc_ref(v_a_1367_);
lean_inc(v_a_1366_);
lean_inc_ref(v_a_1365_);
v___x_1372_ = lean_apply_6(v_searchFn_1363_, v_a_1371_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, lean_box(0));
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v___x_1374_; lean_object* v_mctx_1375_; lean_object* v___x_1376_; lean_object* v___f_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1373_);
lean_dec_ref_known(v___x_1372_, 1);
v___x_1374_ = lean_st_ref_get(v_a_1366_);
v_mctx_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc_ref_n(v_mctx_1375_, 2);
lean_dec(v___x_1374_);
lean_inc(v_goal_1364_);
v___x_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1376_, 0, v_goal_1364_);
lean_ctor_set(v___x_1376_, 1, v_mctx_1375_);
lean_inc_ref(v___x_1376_);
v___f_1377_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0), 2, 1);
lean_closure_set(v___f_1377_, 0, v___x_1376_);
v___x_1378_ = lean_alloc_closure((void*)(l_Lean_MVarId_applySymm___boxed), 6, 1);
lean_closure_set(v___x_1378_, 0, v_goal_1364_);
v___x_1379_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v___x_1378_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1439_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1439_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1439_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
if (lean_obj_tag(v_a_1380_) == 1)
{
lean_object* v_val_1384_; lean_object* v___x_1385_; 
lean_del_object(v___x_1382_);
lean_dec_ref_known(v___x_1376_, 2);
v_val_1384_ = lean_ctor_get(v_a_1380_, 0);
lean_inc_n(v_val_1384_, 2);
lean_dec_ref_known(v_a_1380_, 1);
v___x_1385_ = l_Lean_MVarId_getType(v_val_1384_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1387_; lean_object* v_a_1388_; lean_object* v___x_1389_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1386_);
lean_dec_ref_known(v___x_1385_, 1);
v___x_1387_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_a_1386_, v_a_1366_);
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_a_1388_);
lean_dec_ref(v___x_1387_);
lean_inc(v_a_1368_);
lean_inc_ref(v_a_1367_);
lean_inc(v_a_1366_);
lean_inc_ref(v_a_1365_);
v___x_1389_ = lean_apply_6(v_searchFn_1363_, v_a_1388_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, lean_box(0));
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1416_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1392_ = v___x_1389_;
v_isShared_1393_ = v_isSharedCheck_1416_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1389_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1416_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1394_; lean_object* v_mctx_1395_; lean_object* v___x_1396_; lean_object* v___f_1397_; lean_object* v___x_1398_; lean_object* v_cache_1399_; lean_object* v_zetaDeltaFVarIds_1400_; lean_object* v_postponed_1401_; lean_object* v_diag_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1414_; 
v___x_1394_ = lean_st_ref_get(v_a_1366_);
v_mctx_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc_ref(v_mctx_1395_);
lean_dec(v___x_1394_);
v___x_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1396_, 0, v_val_1384_);
lean_ctor_set(v___x_1396_, 1, v_mctx_1395_);
v___f_1397_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0), 2, 1);
lean_closure_set(v___f_1397_, 0, v___x_1396_);
v___x_1398_ = lean_st_ref_take(v_a_1366_);
v_cache_1399_ = lean_ctor_get(v___x_1398_, 1);
v_zetaDeltaFVarIds_1400_ = lean_ctor_get(v___x_1398_, 2);
v_postponed_1401_ = lean_ctor_get(v___x_1398_, 3);
v_diag_1402_ = lean_ctor_get(v___x_1398_, 4);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1414_ == 0)
{
lean_object* v_unused_1415_; 
v_unused_1415_ = lean_ctor_get(v___x_1398_, 0);
lean_dec(v_unused_1415_);
v___x_1404_ = v___x_1398_;
v_isShared_1405_ = v_isSharedCheck_1414_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_diag_1402_);
lean_inc(v_postponed_1401_);
lean_inc(v_zetaDeltaFVarIds_1400_);
lean_inc(v_cache_1399_);
lean_dec(v___x_1398_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1414_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v_mctx_1375_);
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_mctx_1375_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_cache_1399_);
lean_ctor_set(v_reuseFailAlloc_1413_, 2, v_zetaDeltaFVarIds_1400_);
lean_ctor_set(v_reuseFailAlloc_1413_, 3, v_postponed_1401_);
lean_ctor_set(v_reuseFailAlloc_1413_, 4, v_diag_1402_);
v___x_1407_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1411_; 
v___x_1408_ = lean_st_ref_put(v_a_1366_, v___x_1407_);
v___x_1409_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v___f_1377_, v_a_1373_, v___f_1397_, v_a_1390_);
lean_dec(v_a_1390_);
lean_dec(v_a_1373_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v___x_1409_);
v___x_1411_ = v___x_1392_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_dec(v_val_1384_);
lean_dec_ref(v___f_1377_);
lean_dec_ref(v_mctx_1375_);
lean_dec(v_a_1373_);
v_a_1417_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1389_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1389_);
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
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec(v_val_1384_);
lean_dec_ref(v___f_1377_);
lean_dec_ref(v_mctx_1375_);
lean_dec(v_a_1373_);
lean_dec_ref(v_searchFn_1363_);
v_a_1425_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1385_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1385_);
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
else
{
size_t v_sz_1433_; size_t v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1437_; 
lean_dec(v_a_1380_);
lean_dec_ref(v___f_1377_);
lean_dec_ref(v_mctx_1375_);
lean_dec_ref(v_searchFn_1363_);
v_sz_1433_ = lean_array_size(v_a_1373_);
v___x_1434_ = ((size_t)0ULL);
v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(v___x_1376_, v_sz_1433_, v___x_1434_, v_a_1373_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1435_);
v___x_1437_ = v___x_1382_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec_ref(v___f_1377_);
lean_dec_ref_known(v___x_1376_, 2);
lean_dec_ref(v_mctx_1375_);
lean_dec(v_a_1373_);
lean_dec_ref(v_searchFn_1363_);
v_a_1440_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1379_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1379_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_dec(v_goal_1364_);
lean_dec_ref(v_searchFn_1363_);
v_a_1448_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1372_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1372_);
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
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_dec(v_goal_1364_);
lean_dec_ref(v_searchFn_1363_);
v_a_1456_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1370_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1370_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm___boxed(lean_object* v_searchFn_1464_, lean_object* v_goal_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v_searchFn_1464_, v_goal_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
lean_dec(v_a_1469_);
lean_dec_ref(v_a_1468_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0(lean_object* v_e_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1482_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__1));
v___x_1483_ = lean_unsigned_to_nat(1u);
v___x_1484_ = lean_mk_empty_array_with_capacity(v___x_1483_);
v___x_1485_ = lean_array_push(v___x_1484_, v_e_1476_);
v___x_1486_ = l_Lean_Meta_mkAppM(v___x_1482_, v___x_1485_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___boxed(lean_object* v_e_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0(v_e_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1(lean_object* v_e_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1504_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__1));
v___x_1505_ = lean_unsigned_to_nat(1u);
v___x_1506_ = lean_mk_empty_array_with_capacity(v___x_1505_);
v___x_1507_ = lean_array_push(v___x_1506_, v_e_1498_);
v___x_1508_ = l_Lean_Meta_mkAppM(v___x_1504_, v___x_1507_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___boxed(lean_object* v_e_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1(v_e_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(lean_object* v_lem_1518_, uint8_t v_mod_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_){
_start:
{
lean_object* v___f_1525_; lean_object* v___f_1526_; lean_object* v___x_1527_; 
v___f_1525_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__0));
v___f_1526_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__1));
v___x_1527_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_lem_1518_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
if (lean_obj_tag(v___x_1527_) == 0)
{
switch(v_mod_1519_)
{
case 0:
{
return v___x_1527_;
}
case 1:
{
lean_object* v_a_1528_; lean_object* v___x_1529_; 
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_a_1528_);
lean_dec_ref_known(v___x_1527_, 1);
v___x_1529_ = l_Lean_Meta_mapForallTelescope(v___f_1525_, v_a_1528_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
return v___x_1529_;
}
default: 
{
lean_object* v_a_1530_; lean_object* v___x_1531_; 
v_a_1530_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1527_, 1);
v___x_1531_ = l_Lean_Meta_mapForallTelescope(v___f_1526_, v_a_1530_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
return v___x_1531_;
}
}
}
else
{
return v___x_1527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___boxed(lean_object* v_lem_1532_, lean_object* v_mod_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_){
_start:
{
uint8_t v_mod_boxed_1539_; lean_object* v_res_1540_; 
v_mod_boxed_1539_ = lean_unbox(v_mod_1533_);
v_res_1540_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_lem_1532_, v_mod_boxed_1539_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
lean_dec(v_a_1537_);
lean_dec_ref(v_a_1536_);
lean_dec(v_a_1535_);
lean_dec_ref(v_a_1534_);
return v_res_1540_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar(lean_object* v_e_1541_){
_start:
{
switch(lean_obj_tag(v_e_1541_))
{
case 0:
{
uint8_t v___x_1542_; 
v___x_1542_ = 1;
return v___x_1542_;
}
case 1:
{
uint8_t v___x_1543_; 
v___x_1543_ = 1;
return v___x_1543_;
}
case 2:
{
uint8_t v___x_1544_; 
v___x_1544_ = 1;
return v___x_1544_;
}
default: 
{
uint8_t v___x_1545_; 
v___x_1545_ = 0;
return v___x_1545_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar___boxed(lean_object* v_e_1546_){
_start:
{
uint8_t v_res_1547_; lean_object* v_r_1548_; 
v_res_1547_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar(v_e_1546_);
lean_dec_ref(v_e_1546_);
v_r_1548_ = lean_box(v_res_1547_);
return v_r_1548_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1549_ = lean_unsigned_to_nat(32u);
v___x_1550_ = lean_mk_empty_array_with_capacity(v___x_1549_);
v___x_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
return v___x_1551_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1552_ = ((size_t)5ULL);
v___x_1553_ = lean_unsigned_to_nat(0u);
v___x_1554_ = lean_unsigned_to_nat(32u);
v___x_1555_ = lean_mk_empty_array_with_capacity(v___x_1554_);
v___x_1556_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0);
v___x_1557_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
lean_ctor_set(v___x_1557_, 1, v___x_1555_);
lean_ctor_set(v___x_1557_, 2, v___x_1553_);
lean_ctor_set(v___x_1557_, 3, v___x_1553_);
lean_ctor_set_usize(v___x_1557_, 4, v___x_1552_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(lean_object* v___y_1558_){
_start:
{
lean_object* v___x_1560_; lean_object* v_traceState_1561_; lean_object* v_traces_1562_; lean_object* v___x_1563_; lean_object* v_traceState_1564_; lean_object* v_env_1565_; lean_object* v_nextMacroScope_1566_; lean_object* v_ngen_1567_; lean_object* v_auxDeclNGen_1568_; lean_object* v_cache_1569_; lean_object* v_recordedDeps_1570_; lean_object* v_messages_1571_; lean_object* v_infoState_1572_; lean_object* v_snapshotTasks_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1592_; 
v___x_1560_ = lean_st_ref_get(v___y_1558_);
v_traceState_1561_ = lean_ctor_get(v___x_1560_, 4);
lean_inc_ref(v_traceState_1561_);
lean_dec(v___x_1560_);
v_traces_1562_ = lean_ctor_get(v_traceState_1561_, 0);
lean_inc_ref(v_traces_1562_);
lean_dec_ref(v_traceState_1561_);
v___x_1563_ = lean_st_ref_take(v___y_1558_);
v_traceState_1564_ = lean_ctor_get(v___x_1563_, 4);
v_env_1565_ = lean_ctor_get(v___x_1563_, 0);
v_nextMacroScope_1566_ = lean_ctor_get(v___x_1563_, 1);
v_ngen_1567_ = lean_ctor_get(v___x_1563_, 2);
v_auxDeclNGen_1568_ = lean_ctor_get(v___x_1563_, 3);
v_cache_1569_ = lean_ctor_get(v___x_1563_, 5);
v_recordedDeps_1570_ = lean_ctor_get(v___x_1563_, 6);
v_messages_1571_ = lean_ctor_get(v___x_1563_, 7);
v_infoState_1572_ = lean_ctor_get(v___x_1563_, 8);
v_snapshotTasks_1573_ = lean_ctor_get(v___x_1563_, 9);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1575_ = v___x_1563_;
v_isShared_1576_ = v_isSharedCheck_1592_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_snapshotTasks_1573_);
lean_inc(v_infoState_1572_);
lean_inc(v_messages_1571_);
lean_inc(v_recordedDeps_1570_);
lean_inc(v_cache_1569_);
lean_inc(v_traceState_1564_);
lean_inc(v_auxDeclNGen_1568_);
lean_inc(v_ngen_1567_);
lean_inc(v_nextMacroScope_1566_);
lean_inc(v_env_1565_);
lean_dec(v___x_1563_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1592_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
uint64_t v_tid_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1590_; 
v_tid_1577_ = lean_ctor_get_uint64(v_traceState_1564_, sizeof(void*)*1);
v_isSharedCheck_1590_ = !lean_is_exclusive(v_traceState_1564_);
if (v_isSharedCheck_1590_ == 0)
{
lean_object* v_unused_1591_; 
v_unused_1591_ = lean_ctor_get(v_traceState_1564_, 0);
lean_dec(v_unused_1591_);
v___x_1579_ = v_traceState_1564_;
v_isShared_1580_ = v_isSharedCheck_1590_;
goto v_resetjp_1578_;
}
else
{
lean_dec(v_traceState_1564_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1590_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1581_; lean_object* v___x_1583_; 
v___x_1581_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 0, v___x_1581_);
v___x_1583_ = v___x_1579_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1581_);
lean_ctor_set_uint64(v_reuseFailAlloc_1589_, sizeof(void*)*1, v_tid_1577_);
v___x_1583_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_object* v___x_1585_; 
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 4, v___x_1583_);
v___x_1585_ = v___x_1575_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_env_1565_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_nextMacroScope_1566_);
lean_ctor_set(v_reuseFailAlloc_1588_, 2, v_ngen_1567_);
lean_ctor_set(v_reuseFailAlloc_1588_, 3, v_auxDeclNGen_1568_);
lean_ctor_set(v_reuseFailAlloc_1588_, 4, v___x_1583_);
lean_ctor_set(v_reuseFailAlloc_1588_, 5, v_cache_1569_);
lean_ctor_set(v_reuseFailAlloc_1588_, 6, v_recordedDeps_1570_);
lean_ctor_set(v_reuseFailAlloc_1588_, 7, v_messages_1571_);
lean_ctor_set(v_reuseFailAlloc_1588_, 8, v_infoState_1572_);
lean_ctor_set(v_reuseFailAlloc_1588_, 9, v_snapshotTasks_1573_);
v___x_1585_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = lean_st_ref_put(v___y_1558_, v___x_1585_);
v___x_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1587_, 0, v_traces_1562_);
return v___x_1587_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___boxed(lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v___y_1593_);
lean_dec(v___y_1593_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0(lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v___y_1599_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___boxed(lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0(v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
return v_res_1607_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(lean_object* v_opts_1608_, lean_object* v_opt_1609_){
_start:
{
lean_object* v_name_1610_; lean_object* v_defValue_1611_; lean_object* v_map_1612_; lean_object* v___x_1613_; 
v_name_1610_ = lean_ctor_get(v_opt_1609_, 0);
v_defValue_1611_ = lean_ctor_get(v_opt_1609_, 1);
v_map_1612_ = lean_ctor_get(v_opts_1608_, 0);
v___x_1613_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1612_, v_name_1610_);
if (lean_obj_tag(v___x_1613_) == 0)
{
uint8_t v___x_1614_; 
v___x_1614_ = lean_unbox(v_defValue_1611_);
return v___x_1614_;
}
else
{
lean_object* v_val_1615_; 
v_val_1615_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_val_1615_);
lean_dec_ref_known(v___x_1613_, 1);
if (lean_obj_tag(v_val_1615_) == 1)
{
uint8_t v_v_1616_; 
v_v_1616_ = lean_ctor_get_uint8(v_val_1615_, 0);
lean_dec_ref_known(v_val_1615_, 0);
return v_v_1616_;
}
else
{
uint8_t v___x_1617_; 
lean_dec(v_val_1615_);
v___x_1617_ = lean_unbox(v_defValue_1611_);
return v___x_1617_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___boxed(lean_object* v_opts_1618_, lean_object* v_opt_1619_){
_start:
{
uint8_t v_res_1620_; lean_object* v_r_1621_; 
v_res_1620_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1618_, v_opt_1619_);
lean_dec_ref(v_opt_1619_);
lean_dec_ref(v_opts_1618_);
v_r_1621_ = lean_box(v_res_1620_);
return v_r_1621_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__0));
v___x_1624_ = l_Lean_stringToMessageData(v___x_1623_);
return v___x_1624_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__2));
v___x_1627_ = l_Lean_stringToMessageData(v___x_1626_);
return v___x_1627_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__5));
v___x_1632_ = l_Lean_MessageData_ofFormat(v___x_1631_);
return v___x_1632_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__8));
v___x_1637_ = l_Lean_MessageData_ofFormat(v___x_1636_);
return v___x_1637_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12(void){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__11));
v___x_1642_ = l_Lean_MessageData_ofFormat(v___x_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0(lean_object* v_fst_1643_, uint8_t v_snd_1644_, lean_object* v_x_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___y_1655_; 
v___x_1651_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1);
v___x_1652_ = l_Lean_MessageData_ofName(v_fst_1643_);
v___x_1653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1651_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
switch(v_snd_1644_)
{
case 0:
{
lean_object* v___x_1660_; 
v___x_1660_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6);
v___y_1655_ = v___x_1660_;
goto v___jp_1654_;
}
case 1:
{
lean_object* v___x_1661_; 
v___x_1661_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9);
v___y_1655_ = v___x_1661_;
goto v___jp_1654_;
}
default: 
{
lean_object* v___x_1662_; 
v___x_1662_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12);
v___y_1655_ = v___x_1662_;
goto v___jp_1654_;
}
}
v___jp_1654_:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
lean_inc_ref(v___y_1655_);
v___x_1656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1653_);
lean_ctor_set(v___x_1656_, 1, v___y_1655_);
v___x_1657_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3);
v___x_1658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1656_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
v___x_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
return v___x_1659_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___boxed(lean_object* v_fst_1663_, lean_object* v_snd_1664_, lean_object* v_x_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
uint8_t v_snd_11168__boxed_1671_; lean_object* v_res_1672_; 
v_snd_11168__boxed_1671_ = lean_unbox(v_snd_1664_);
v_res_1672_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0(v_fst_1663_, v_snd_11168__boxed_1671_, v_x_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec_ref(v_x_1665_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(lean_object* v_opts_1673_, lean_object* v_opt_1674_){
_start:
{
lean_object* v_name_1675_; lean_object* v_defValue_1676_; lean_object* v_map_1677_; lean_object* v___x_1678_; 
v_name_1675_ = lean_ctor_get(v_opt_1674_, 0);
v_defValue_1676_ = lean_ctor_get(v_opt_1674_, 1);
v_map_1677_ = lean_ctor_get(v_opts_1673_, 0);
v___x_1678_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1677_, v_name_1675_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_inc(v_defValue_1676_);
return v_defValue_1676_;
}
else
{
lean_object* v_val_1679_; 
v_val_1679_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_val_1679_);
lean_dec_ref_known(v___x_1678_, 1);
if (lean_obj_tag(v_val_1679_) == 3)
{
lean_object* v_v_1680_; 
v_v_1680_ = lean_ctor_get(v_val_1679_, 0);
lean_inc(v_v_1680_);
lean_dec_ref_known(v_val_1679_, 1);
return v_v_1680_;
}
else
{
lean_dec(v_val_1679_);
lean_inc(v_defValue_1676_);
return v_defValue_1676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5___boxed(lean_object* v_opts_1681_, lean_object* v_opt_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1681_, v_opt_1682_);
lean_dec_ref(v_opt_1682_);
lean_dec_ref(v_opts_1681_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(lean_object* v_x_1684_){
_start:
{
if (lean_obj_tag(v_x_1684_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
v_a_1686_ = lean_ctor_get(v_x_1684_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_x_1684_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v_x_1684_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v_x_1684_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
lean_ctor_set_tag(v___x_1688_, 1);
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
v_a_1694_ = lean_ctor_get(v_x_1684_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_x_1684_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v_x_1684_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v_x_1684_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
lean_ctor_set_tag(v___x_1696_, 0);
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg___boxed(lean_object* v_x_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_x_1702_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(size_t v_sz_1705_, size_t v_i_1706_, lean_object* v_bs_1707_){
_start:
{
uint8_t v___x_1708_; 
v___x_1708_ = lean_usize_dec_lt(v_i_1706_, v_sz_1705_);
if (v___x_1708_ == 0)
{
return v_bs_1707_;
}
else
{
lean_object* v_v_1709_; lean_object* v_msg_1710_; lean_object* v___x_1711_; lean_object* v_bs_x27_1712_; size_t v___x_1713_; size_t v___x_1714_; lean_object* v___x_1715_; 
v_v_1709_ = lean_array_uget_borrowed(v_bs_1707_, v_i_1706_);
v_msg_1710_ = lean_ctor_get(v_v_1709_, 1);
lean_inc_ref(v_msg_1710_);
v___x_1711_ = lean_unsigned_to_nat(0u);
v_bs_x27_1712_ = lean_array_uset(v_bs_1707_, v_i_1706_, v___x_1711_);
v___x_1713_ = ((size_t)1ULL);
v___x_1714_ = lean_usize_add(v_i_1706_, v___x_1713_);
v___x_1715_ = lean_array_uset(v_bs_x27_1712_, v_i_1706_, v_msg_1710_);
v_i_1706_ = v___x_1714_;
v_bs_1707_ = v___x_1715_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1717_, lean_object* v_i_1718_, lean_object* v_bs_1719_){
_start:
{
size_t v_sz_boxed_1720_; size_t v_i_boxed_1721_; lean_object* v_res_1722_; 
v_sz_boxed_1720_ = lean_unbox_usize(v_sz_1717_);
lean_dec(v_sz_1717_);
v_i_boxed_1721_ = lean_unbox_usize(v_i_1718_);
lean_dec(v_i_1718_);
v_res_1722_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(v_sz_boxed_1720_, v_i_boxed_1721_, v_bs_1719_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(lean_object* v_oldTraces_1723_, lean_object* v_data_1724_, lean_object* v_ref_1725_, lean_object* v_msg_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v_toCold_1732_; lean_object* v_currRecDepth_1733_; lean_object* v_ref_1734_; uint16_t v_optionFlags_1735_; uint8_t v_suppressElabErrors_1736_; uint8_t v_isRecordingDeps_1737_; lean_object* v_ref_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v_traceState_1741_; lean_object* v_traces_1742_; lean_object* v___x_1743_; size_t v_sz_1744_; size_t v___x_1745_; lean_object* v___x_1746_; lean_object* v_msg_1747_; lean_object* v___x_1748_; lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1787_; 
v_toCold_1732_ = lean_ctor_get(v___y_1729_, 0);
v_currRecDepth_1733_ = lean_ctor_get(v___y_1729_, 1);
v_ref_1734_ = lean_ctor_get(v___y_1729_, 2);
v_optionFlags_1735_ = lean_ctor_get_uint16(v___y_1729_, sizeof(void*)*3);
v_suppressElabErrors_1736_ = lean_ctor_get_uint8(v___y_1729_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1737_ = lean_ctor_get_uint8(v___y_1729_, sizeof(void*)*3 + 3);
v_ref_1738_ = l_Lean_replaceRef(v_ref_1725_, v_ref_1734_);
lean_inc(v_currRecDepth_1733_);
lean_inc_ref(v_toCold_1732_);
v___x_1739_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1739_, 0, v_toCold_1732_);
lean_ctor_set(v___x_1739_, 1, v_currRecDepth_1733_);
lean_ctor_set(v___x_1739_, 2, v_ref_1738_);
lean_ctor_set_uint16(v___x_1739_, sizeof(void*)*3, v_optionFlags_1735_);
lean_ctor_set_uint8(v___x_1739_, sizeof(void*)*3 + 2, v_suppressElabErrors_1736_);
lean_ctor_set_uint8(v___x_1739_, sizeof(void*)*3 + 3, v_isRecordingDeps_1737_);
v___x_1740_ = lean_st_ref_get(v___y_1730_);
v_traceState_1741_ = lean_ctor_get(v___x_1740_, 4);
lean_inc_ref(v_traceState_1741_);
lean_dec(v___x_1740_);
v_traces_1742_ = lean_ctor_get(v_traceState_1741_, 0);
lean_inc_ref(v_traces_1742_);
lean_dec_ref(v_traceState_1741_);
v___x_1743_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1742_);
lean_dec_ref(v_traces_1742_);
v_sz_1744_ = lean_array_size(v___x_1743_);
v___x_1745_ = ((size_t)0ULL);
v___x_1746_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(v_sz_1744_, v___x_1745_, v___x_1743_);
v_msg_1747_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1747_, 0, v_data_1724_);
lean_ctor_set(v_msg_1747_, 1, v_msg_1726_);
lean_ctor_set(v_msg_1747_, 2, v___x_1746_);
v___x_1748_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msg_1747_, v___y_1727_, v___y_1728_, v___x_1739_, v___y_1730_);
lean_dec_ref_known(v___x_1739_, 3);
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1751_ = v___x_1748_;
v_isShared_1752_ = v_isSharedCheck_1787_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1748_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1787_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; lean_object* v_traceState_1754_; lean_object* v_env_1755_; lean_object* v_nextMacroScope_1756_; lean_object* v_ngen_1757_; lean_object* v_auxDeclNGen_1758_; lean_object* v_cache_1759_; lean_object* v_recordedDeps_1760_; lean_object* v_messages_1761_; lean_object* v_infoState_1762_; lean_object* v_snapshotTasks_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1786_; 
v___x_1753_ = lean_st_ref_take(v___y_1730_);
v_traceState_1754_ = lean_ctor_get(v___x_1753_, 4);
v_env_1755_ = lean_ctor_get(v___x_1753_, 0);
v_nextMacroScope_1756_ = lean_ctor_get(v___x_1753_, 1);
v_ngen_1757_ = lean_ctor_get(v___x_1753_, 2);
v_auxDeclNGen_1758_ = lean_ctor_get(v___x_1753_, 3);
v_cache_1759_ = lean_ctor_get(v___x_1753_, 5);
v_recordedDeps_1760_ = lean_ctor_get(v___x_1753_, 6);
v_messages_1761_ = lean_ctor_get(v___x_1753_, 7);
v_infoState_1762_ = lean_ctor_get(v___x_1753_, 8);
v_snapshotTasks_1763_ = lean_ctor_get(v___x_1753_, 9);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1765_ = v___x_1753_;
v_isShared_1766_ = v_isSharedCheck_1786_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_snapshotTasks_1763_);
lean_inc(v_infoState_1762_);
lean_inc(v_messages_1761_);
lean_inc(v_recordedDeps_1760_);
lean_inc(v_cache_1759_);
lean_inc(v_traceState_1754_);
lean_inc(v_auxDeclNGen_1758_);
lean_inc(v_ngen_1757_);
lean_inc(v_nextMacroScope_1756_);
lean_inc(v_env_1755_);
lean_dec(v___x_1753_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1786_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
uint64_t v_tid_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1784_; 
v_tid_1767_ = lean_ctor_get_uint64(v_traceState_1754_, sizeof(void*)*1);
v_isSharedCheck_1784_ = !lean_is_exclusive(v_traceState_1754_);
if (v_isSharedCheck_1784_ == 0)
{
lean_object* v_unused_1785_; 
v_unused_1785_ = lean_ctor_get(v_traceState_1754_, 0);
lean_dec(v_unused_1785_);
v___x_1769_ = v_traceState_1754_;
v_isShared_1770_ = v_isSharedCheck_1784_;
goto v_resetjp_1768_;
}
else
{
lean_dec(v_traceState_1754_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1784_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1775_; 
v___x_1771_ = lean_box(0);
v___x_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1772_, 0, v_ref_1725_);
lean_ctor_set(v___x_1772_, 1, v_a_1749_);
v___x_1773_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1723_, v___x_1772_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v___x_1773_);
v___x_1775_ = v___x_1769_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1773_);
lean_ctor_set_uint64(v_reuseFailAlloc_1783_, sizeof(void*)*1, v_tid_1767_);
v___x_1775_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1777_; 
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 4, v___x_1775_);
v___x_1777_ = v___x_1765_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_env_1755_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_nextMacroScope_1756_);
lean_ctor_set(v_reuseFailAlloc_1782_, 2, v_ngen_1757_);
lean_ctor_set(v_reuseFailAlloc_1782_, 3, v_auxDeclNGen_1758_);
lean_ctor_set(v_reuseFailAlloc_1782_, 4, v___x_1775_);
lean_ctor_set(v_reuseFailAlloc_1782_, 5, v_cache_1759_);
lean_ctor_set(v_reuseFailAlloc_1782_, 6, v_recordedDeps_1760_);
lean_ctor_set(v_reuseFailAlloc_1782_, 7, v_messages_1761_);
lean_ctor_set(v_reuseFailAlloc_1782_, 8, v_infoState_1762_);
lean_ctor_set(v_reuseFailAlloc_1782_, 9, v_snapshotTasks_1763_);
v___x_1777_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1778_; lean_object* v___x_1780_; 
v___x_1778_ = lean_st_ref_put(v___y_1730_, v___x_1777_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v___x_1771_);
v___x_1780_ = v___x_1751_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1771_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2___boxed(lean_object* v_oldTraces_1788_, lean_object* v_data_1789_, lean_object* v_ref_1790_, lean_object* v_msg_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_1788_, v_data_1789_, v_ref_1790_, v_msg_1791_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
return v_res_1797_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(lean_object* v_e_1798_){
_start:
{
if (lean_obj_tag(v_e_1798_) == 0)
{
uint8_t v___x_1799_; 
v___x_1799_ = 2;
return v___x_1799_;
}
else
{
uint8_t v___x_1800_; 
v___x_1800_ = 0;
return v___x_1800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___boxed(lean_object* v_e_1801_){
_start:
{
uint8_t v_res_1802_; lean_object* v_r_1803_; 
v_res_1802_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(v_e_1801_);
lean_dec_ref(v_e_1801_);
v_r_1803_ = lean_box(v_res_1802_);
return v_r_1803_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1804_; double v___x_1805_; 
v___x_1804_ = lean_unsigned_to_nat(0u);
v___x_1805_ = lean_float_of_nat(v___x_1804_);
return v___x_1805_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__1));
v___x_1808_ = l_Lean_stringToMessageData(v___x_1807_);
return v___x_1808_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1809_; double v___x_1810_; 
v___x_1809_ = lean_unsigned_to_nat(1000u);
v___x_1810_ = lean_float_of_nat(v___x_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(lean_object* v_cls_1811_, uint8_t v_collapsed_1812_, lean_object* v_tag_1813_, lean_object* v_opts_1814_, uint8_t v_clsEnabled_1815_, lean_object* v_oldTraces_1816_, lean_object* v_msg_1817_, lean_object* v_resStartStop_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_fst_1824_; lean_object* v_snd_1825_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v_data_1829_; lean_object* v_fst_1840_; lean_object* v_snd_1841_; lean_object* v___x_1842_; uint8_t v___x_1843_; lean_object* v___y_1845_; lean_object* v_a_1846_; uint8_t v___y_1861_; double v___y_1893_; 
v_fst_1824_ = lean_ctor_get(v_resStartStop_1818_, 0);
lean_inc(v_fst_1824_);
v_snd_1825_ = lean_ctor_get(v_resStartStop_1818_, 1);
lean_inc(v_snd_1825_);
lean_dec_ref(v_resStartStop_1818_);
v_fst_1840_ = lean_ctor_get(v_snd_1825_, 0);
lean_inc(v_fst_1840_);
v_snd_1841_ = lean_ctor_get(v_snd_1825_, 1);
lean_inc(v_snd_1841_);
lean_dec(v_snd_1825_);
v___x_1842_ = l_Lean_trace_profiler;
v___x_1843_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1814_, v___x_1842_);
if (v___x_1843_ == 0)
{
v___y_1861_ = v___x_1843_;
goto v___jp_1860_;
}
else
{
lean_object* v___x_1898_; uint8_t v___x_1899_; 
v___x_1898_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1899_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1814_, v___x_1898_);
if (v___x_1899_ == 0)
{
lean_object* v___x_1900_; lean_object* v___x_1901_; double v___x_1902_; double v___x_1903_; double v___x_1904_; 
v___x_1900_ = l_Lean_trace_profiler_threshold;
v___x_1901_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1814_, v___x_1900_);
v___x_1902_ = lean_float_of_nat(v___x_1901_);
v___x_1903_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3);
v___x_1904_ = lean_float_div(v___x_1902_, v___x_1903_);
v___y_1893_ = v___x_1904_;
goto v___jp_1892_;
}
else
{
lean_object* v___x_1905_; lean_object* v___x_1906_; double v___x_1907_; 
v___x_1905_ = l_Lean_trace_profiler_threshold;
v___x_1906_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1814_, v___x_1905_);
v___x_1907_ = lean_float_of_nat(v___x_1906_);
v___y_1893_ = v___x_1907_;
goto v___jp_1892_;
}
}
v___jp_1826_:
{
lean_object* v___x_1830_; 
lean_inc(v___y_1827_);
v___x_1830_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_1816_, v_data_1829_, v___y_1827_, v___y_1828_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v___x_1831_; 
lean_dec_ref_known(v___x_1830_, 1);
v___x_1831_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_1824_);
return v___x_1831_;
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_dec(v_fst_1824_);
v_a_1832_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1830_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1830_);
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
v___jp_1844_:
{
uint8_t v_result_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; double v___x_1850_; lean_object* v_data_1851_; 
v_result_1847_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(v_fst_1824_);
v___x_1848_ = lean_box(v_result_1847_);
v___x_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
v___x_1850_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0);
lean_inc_ref(v_tag_1813_);
lean_inc_ref(v___x_1849_);
lean_inc(v_cls_1811_);
v_data_1851_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1851_, 0, v_cls_1811_);
lean_ctor_set(v_data_1851_, 1, v___x_1849_);
lean_ctor_set(v_data_1851_, 2, v_tag_1813_);
lean_ctor_set_float(v_data_1851_, sizeof(void*)*3, v___x_1850_);
lean_ctor_set_float(v_data_1851_, sizeof(void*)*3 + 8, v___x_1850_);
lean_ctor_set_uint8(v_data_1851_, sizeof(void*)*3 + 16, v_collapsed_1812_);
if (v___x_1843_ == 0)
{
lean_dec_ref_known(v___x_1849_, 1);
lean_dec(v_snd_1841_);
lean_dec(v_fst_1840_);
lean_dec_ref(v_tag_1813_);
lean_dec(v_cls_1811_);
v___y_1827_ = v___y_1845_;
v___y_1828_ = v_a_1846_;
v_data_1829_ = v_data_1851_;
goto v___jp_1826_;
}
else
{
lean_object* v_data_1852_; double v___x_1853_; double v___x_1854_; 
lean_dec_ref_known(v_data_1851_, 3);
v_data_1852_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1852_, 0, v_cls_1811_);
lean_ctor_set(v_data_1852_, 1, v___x_1849_);
lean_ctor_set(v_data_1852_, 2, v_tag_1813_);
v___x_1853_ = lean_unbox_float(v_fst_1840_);
lean_dec(v_fst_1840_);
lean_ctor_set_float(v_data_1852_, sizeof(void*)*3, v___x_1853_);
v___x_1854_ = lean_unbox_float(v_snd_1841_);
lean_dec(v_snd_1841_);
lean_ctor_set_float(v_data_1852_, sizeof(void*)*3 + 8, v___x_1854_);
lean_ctor_set_uint8(v_data_1852_, sizeof(void*)*3 + 16, v_collapsed_1812_);
v___y_1827_ = v___y_1845_;
v___y_1828_ = v_a_1846_;
v_data_1829_ = v_data_1852_;
goto v___jp_1826_;
}
}
v___jp_1855_:
{
lean_object* v_ref_1856_; lean_object* v___x_1857_; 
v_ref_1856_ = lean_ctor_get(v___y_1821_, 2);
lean_inc(v___y_1822_);
lean_inc_ref(v___y_1821_);
lean_inc(v___y_1820_);
lean_inc_ref(v___y_1819_);
lean_inc(v_fst_1824_);
v___x_1857_ = lean_apply_6(v_msg_1817_, v_fst_1824_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, lean_box(0));
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
lean_inc(v_a_1858_);
lean_dec_ref_known(v___x_1857_, 1);
v___y_1845_ = v_ref_1856_;
v_a_1846_ = v_a_1858_;
goto v___jp_1844_;
}
else
{
lean_object* v___x_1859_; 
lean_dec_ref_known(v___x_1857_, 1);
v___x_1859_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2);
v___y_1845_ = v_ref_1856_;
v_a_1846_ = v___x_1859_;
goto v___jp_1844_;
}
}
v___jp_1860_:
{
if (v_clsEnabled_1815_ == 0)
{
if (v___y_1861_ == 0)
{
lean_object* v___x_1862_; lean_object* v_traceState_1863_; lean_object* v_env_1864_; lean_object* v_nextMacroScope_1865_; lean_object* v_ngen_1866_; lean_object* v_auxDeclNGen_1867_; lean_object* v_cache_1868_; lean_object* v_recordedDeps_1869_; lean_object* v_messages_1870_; lean_object* v_infoState_1871_; lean_object* v_snapshotTasks_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1891_; 
lean_dec(v_snd_1841_);
lean_dec(v_fst_1840_);
lean_dec_ref(v_msg_1817_);
lean_dec_ref(v_tag_1813_);
lean_dec(v_cls_1811_);
v___x_1862_ = lean_st_ref_take(v___y_1822_);
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
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1874_ = v___x_1862_;
v_isShared_1875_ = v_isSharedCheck_1891_;
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
v_isShared_1875_ = v_isSharedCheck_1891_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
uint64_t v_tid_1876_; lean_object* v_traces_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1890_; 
v_tid_1876_ = lean_ctor_get_uint64(v_traceState_1863_, sizeof(void*)*1);
v_traces_1877_ = lean_ctor_get(v_traceState_1863_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v_traceState_1863_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1879_ = v_traceState_1863_;
v_isShared_1880_ = v_isSharedCheck_1890_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_traces_1877_);
lean_dec(v_traceState_1863_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1890_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1881_; lean_object* v___x_1883_; 
v___x_1881_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1816_, v_traces_1877_);
lean_dec_ref(v_traces_1877_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v___x_1881_);
v___x_1883_ = v___x_1879_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1881_);
lean_ctor_set_uint64(v_reuseFailAlloc_1889_, sizeof(void*)*1, v_tid_1876_);
v___x_1883_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1885_; 
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 4, v___x_1883_);
v___x_1885_ = v___x_1874_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_env_1864_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_nextMacroScope_1865_);
lean_ctor_set(v_reuseFailAlloc_1888_, 2, v_ngen_1866_);
lean_ctor_set(v_reuseFailAlloc_1888_, 3, v_auxDeclNGen_1867_);
lean_ctor_set(v_reuseFailAlloc_1888_, 4, v___x_1883_);
lean_ctor_set(v_reuseFailAlloc_1888_, 5, v_cache_1868_);
lean_ctor_set(v_reuseFailAlloc_1888_, 6, v_recordedDeps_1869_);
lean_ctor_set(v_reuseFailAlloc_1888_, 7, v_messages_1870_);
lean_ctor_set(v_reuseFailAlloc_1888_, 8, v_infoState_1871_);
lean_ctor_set(v_reuseFailAlloc_1888_, 9, v_snapshotTasks_1872_);
v___x_1885_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = lean_st_ref_put(v___y_1822_, v___x_1885_);
v___x_1887_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_1824_);
return v___x_1887_;
}
}
}
}
}
else
{
goto v___jp_1855_;
}
}
else
{
goto v___jp_1855_;
}
}
v___jp_1892_:
{
double v___x_1894_; double v___x_1895_; double v___x_1896_; uint8_t v___x_1897_; 
v___x_1894_ = lean_unbox_float(v_snd_1841_);
v___x_1895_ = lean_unbox_float(v_fst_1840_);
v___x_1896_ = lean_float_sub(v___x_1894_, v___x_1895_);
v___x_1897_ = lean_float_decLt(v___y_1893_, v___x_1896_);
v___y_1861_ = v___x_1897_;
goto v___jp_1860_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___boxed(lean_object* v_cls_1908_, lean_object* v_collapsed_1909_, lean_object* v_tag_1910_, lean_object* v_opts_1911_, lean_object* v_clsEnabled_1912_, lean_object* v_oldTraces_1913_, lean_object* v_msg_1914_, lean_object* v_resStartStop_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
uint8_t v_collapsed_boxed_1921_; uint8_t v_clsEnabled_boxed_1922_; lean_object* v_res_1923_; 
v_collapsed_boxed_1921_ = lean_unbox(v_collapsed_1909_);
v_clsEnabled_boxed_1922_ = lean_unbox(v_clsEnabled_1912_);
v_res_1923_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v_cls_1908_, v_collapsed_boxed_1921_, v_tag_1910_, v_opts_1911_, v_clsEnabled_boxed_1922_, v_oldTraces_1913_, v_msg_1914_, v_resStartStop_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec_ref(v_opts_1911_);
return v_res_1923_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2(void){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1927_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_1928_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__1));
v___x_1929_ = l_Lean_Name_append(v___x_1928_, v___x_1927_);
return v___x_1929_;
}
}
static double _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3(void){
_start:
{
lean_object* v___x_1930_; double v___x_1931_; 
v___x_1930_ = lean_unsigned_to_nat(1000000000u);
v___x_1931_ = lean_float_of_nat(v___x_1930_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(lean_object* v_cfg_1932_, lean_object* v_act_1933_, lean_object* v_allowFailure_1934_, lean_object* v_cand_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_){
_start:
{
lean_object* v_fst_1941_; lean_object* v_snd_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_2229_; 
v_fst_1941_ = lean_ctor_get(v_cand_1935_, 0);
v_snd_1942_ = lean_ctor_get(v_cand_1935_, 1);
v_isSharedCheck_2229_ = !lean_is_exclusive(v_cand_1935_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_1944_ = v_cand_1935_;
v_isShared_1945_ = v_isSharedCheck_2229_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_snd_1942_);
lean_inc(v_fst_1941_);
lean_dec(v_cand_1935_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_2229_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v_toCold_1946_; lean_object* v_options_1947_; uint8_t v_hasTrace_1948_; 
v_toCold_1946_ = lean_ctor_get(v_a_1938_, 0);
v_options_1947_ = lean_ctor_get(v_toCold_1946_, 2);
v_hasTrace_1948_ = lean_ctor_get_uint8(v_options_1947_, sizeof(void*)*1);
if (v_hasTrace_1948_ == 0)
{
lean_object* v_fst_1949_; lean_object* v_snd_1950_; lean_object* v_fst_1951_; lean_object* v_snd_1952_; lean_object* v___x_1953_; lean_object* v_cache_1954_; lean_object* v_zetaDeltaFVarIds_1955_; lean_object* v_postponed_1956_; lean_object* v_diag_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_2005_; 
lean_del_object(v___x_1944_);
v_fst_1949_ = lean_ctor_get(v_fst_1941_, 0);
lean_inc(v_fst_1949_);
v_snd_1950_ = lean_ctor_get(v_fst_1941_, 1);
lean_inc(v_snd_1950_);
lean_dec(v_fst_1941_);
v_fst_1951_ = lean_ctor_get(v_snd_1942_, 0);
lean_inc(v_fst_1951_);
v_snd_1952_ = lean_ctor_get(v_snd_1942_, 1);
lean_inc(v_snd_1952_);
lean_dec(v_snd_1942_);
v___x_1953_ = lean_st_ref_take(v_a_1937_);
v_cache_1954_ = lean_ctor_get(v___x_1953_, 1);
v_zetaDeltaFVarIds_1955_ = lean_ctor_get(v___x_1953_, 2);
v_postponed_1956_ = lean_ctor_get(v___x_1953_, 3);
v_diag_1957_ = lean_ctor_get(v___x_1953_, 4);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_2005_ == 0)
{
lean_object* v_unused_2006_; 
v_unused_2006_ = lean_ctor_get(v___x_1953_, 0);
lean_dec(v_unused_2006_);
v___x_1959_ = v___x_1953_;
v_isShared_1960_ = v_isSharedCheck_2005_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_diag_1957_);
lean_inc(v_postponed_1956_);
lean_inc(v_zetaDeltaFVarIds_1955_);
lean_inc(v_cache_1954_);
lean_dec(v___x_1953_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_2005_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v_snd_1950_);
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_snd_1950_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_cache_1954_);
lean_ctor_set(v_reuseFailAlloc_2004_, 2, v_zetaDeltaFVarIds_1955_);
lean_ctor_set(v_reuseFailAlloc_2004_, 3, v_postponed_1956_);
lean_ctor_set(v_reuseFailAlloc_2004_, 4, v_diag_1957_);
v___x_1962_ = v_reuseFailAlloc_2004_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
lean_object* v___x_1963_; uint8_t v___x_1964_; lean_object* v___x_1965_; 
v___x_1963_ = lean_st_ref_put(v_a_1937_, v___x_1962_);
v___x_1964_ = lean_unbox(v_snd_1952_);
lean_dec(v_snd_1952_);
v___x_1965_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_1951_, v___x_1964_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1966_);
lean_dec_ref_known(v___x_1965_, 1);
v___x_1967_ = lean_box(0);
lean_inc(v_fst_1949_);
v___x_1968_ = l_Lean_MVarId_apply(v_fst_1949_, v_a_1966_, v_cfg_1932_, v___x_1967_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1970_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc_n(v_a_1969_, 2);
lean_dec_ref_known(v___x_1968_, 1);
lean_inc(v_a_1939_);
lean_inc_ref(v_a_1938_);
lean_inc(v_a_1937_);
lean_inc_ref(v_a_1936_);
v___x_1970_ = lean_apply_6(v_act_1933_, v_a_1969_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, lean_box(0));
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_dec(v_a_1969_);
lean_dec(v_fst_1949_);
lean_dec_ref(v_allowFailure_1934_);
return v___x_1970_;
}
else
{
lean_object* v_a_1971_; uint8_t v___y_1973_; uint8_t v___x_1994_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_1971_);
v___x_1994_ = l_Lean_Exception_isInterrupt(v_a_1971_);
if (v___x_1994_ == 0)
{
uint8_t v___x_1995_; 
v___x_1995_ = l_Lean_Exception_isRuntime(v_a_1971_);
v___y_1973_ = v___x_1995_;
goto v___jp_1972_;
}
else
{
lean_dec(v_a_1971_);
v___y_1973_ = v___x_1994_;
goto v___jp_1972_;
}
v___jp_1972_:
{
if (v___y_1973_ == 0)
{
lean_object* v___x_1974_; 
lean_dec_ref_known(v___x_1970_, 1);
lean_inc(v_a_1939_);
lean_inc_ref(v_a_1938_);
lean_inc(v_a_1937_);
lean_inc_ref(v_a_1936_);
v___x_1974_ = lean_apply_6(v_allowFailure_1934_, v_fst_1949_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, lean_box(0));
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1985_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1977_ = v___x_1974_;
v_isShared_1978_ = v_isSharedCheck_1985_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1974_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1985_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
uint8_t v___x_1979_; 
v___x_1979_ = lean_unbox(v_a_1975_);
lean_dec(v_a_1975_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
lean_del_object(v___x_1977_);
lean_dec(v_a_1969_);
v___x_1980_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1);
v___x_1981_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_1980_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
return v___x_1981_;
}
else
{
lean_object* v___x_1983_; 
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v_a_1969_);
v___x_1983_ = v___x_1977_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1969_);
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
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
lean_dec(v_a_1969_);
v_a_1986_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1974_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1974_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
else
{
lean_dec(v_a_1969_);
lean_dec(v_fst_1949_);
lean_dec_ref(v_allowFailure_1934_);
return v___x_1970_;
}
}
}
}
else
{
lean_dec(v_fst_1949_);
lean_dec_ref(v_allowFailure_1934_);
lean_dec_ref(v_act_1933_);
return v___x_1968_;
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec(v_fst_1949_);
lean_dec_ref(v_allowFailure_1934_);
lean_dec_ref(v_act_1933_);
lean_dec_ref(v_cfg_1932_);
v_a_1996_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1965_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1965_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
}
}
else
{
lean_object* v_fst_2007_; lean_object* v_snd_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2228_; 
v_fst_2007_ = lean_ctor_get(v_fst_1941_, 0);
v_snd_2008_ = lean_ctor_get(v_fst_1941_, 1);
v_isSharedCheck_2228_ = !lean_is_exclusive(v_fst_1941_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2010_ = v_fst_1941_;
v_isShared_2011_ = v_isSharedCheck_2228_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_snd_2008_);
lean_inc(v_fst_2007_);
lean_dec(v_fst_1941_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2228_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v_fst_2012_; lean_object* v_snd_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2227_; 
v_fst_2012_ = lean_ctor_get(v_snd_1942_, 0);
v_snd_2013_ = lean_ctor_get(v_snd_1942_, 1);
v_isSharedCheck_2227_ = !lean_is_exclusive(v_snd_1942_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2015_ = v_snd_1942_;
v_isShared_2016_ = v_isSharedCheck_2227_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_snd_2013_);
lean_inc(v_fst_2012_);
lean_dec(v_snd_1942_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2227_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v_inheritedTraceOptions_2017_; lean_object* v___f_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; uint8_t v___x_2022_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v_a_2026_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v_a_2045_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v_a_2050_; lean_object* v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; uint8_t v___y_2063_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v_a_2073_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v_a_2087_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v_a_2092_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2104_; uint8_t v___y_2105_; 
v_inheritedTraceOptions_2017_ = lean_ctor_get(v_toCold_1946_, 11);
lean_inc(v_snd_2013_);
lean_inc(v_fst_2012_);
v___f_2018_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2018_, 0, v_fst_2012_);
lean_closure_set(v___f_2018_, 1, v_snd_2013_);
v___x_2019_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_2020_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4));
v___x_2021_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2);
v___x_2022_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2017_, v_options_1947_, v___x_2021_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2171_; uint8_t v___x_2172_; 
v___x_2171_ = l_Lean_trace_profiler;
v___x_2172_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_1947_, v___x_2171_);
if (v___x_2172_ == 0)
{
lean_object* v___x_2173_; lean_object* v_cache_2174_; lean_object* v_zetaDeltaFVarIds_2175_; lean_object* v_postponed_2176_; lean_object* v_diag_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2225_; 
lean_dec_ref(v___f_2018_);
lean_del_object(v___x_2015_);
lean_del_object(v___x_2010_);
lean_del_object(v___x_1944_);
v___x_2173_ = lean_st_ref_take(v_a_1937_);
v_cache_2174_ = lean_ctor_get(v___x_2173_, 1);
v_zetaDeltaFVarIds_2175_ = lean_ctor_get(v___x_2173_, 2);
v_postponed_2176_ = lean_ctor_get(v___x_2173_, 3);
v_diag_2177_ = lean_ctor_get(v___x_2173_, 4);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2225_ == 0)
{
lean_object* v_unused_2226_; 
v_unused_2226_ = lean_ctor_get(v___x_2173_, 0);
lean_dec(v_unused_2226_);
v___x_2179_ = v___x_2173_;
v_isShared_2180_ = v_isSharedCheck_2225_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_diag_2177_);
lean_inc(v_postponed_2176_);
lean_inc(v_zetaDeltaFVarIds_2175_);
lean_inc(v_cache_2174_);
lean_dec(v___x_2173_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2225_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 0, v_snd_2008_);
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_snd_2008_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_cache_2174_);
lean_ctor_set(v_reuseFailAlloc_2224_, 2, v_zetaDeltaFVarIds_2175_);
lean_ctor_set(v_reuseFailAlloc_2224_, 3, v_postponed_2176_);
lean_ctor_set(v_reuseFailAlloc_2224_, 4, v_diag_2177_);
v___x_2182_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
lean_object* v___x_2183_; uint8_t v___x_2184_; lean_object* v___x_2185_; 
v___x_2183_ = lean_st_ref_put(v_a_1937_, v___x_2182_);
v___x_2184_ = lean_unbox(v_snd_2013_);
lean_dec(v_snd_2013_);
v___x_2185_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2012_, v___x_2184_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
lean_dec_ref_known(v___x_2185_, 1);
v___x_2187_ = lean_box(0);
lean_inc(v_fst_2007_);
v___x_2188_ = l_Lean_MVarId_apply(v_fst_2007_, v_a_2186_, v_cfg_1932_, v___x_2187_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; lean_object* v___x_2190_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc_n(v_a_2189_, 2);
lean_dec_ref_known(v___x_2188_, 1);
lean_inc(v_a_1939_);
lean_inc_ref(v_a_1938_);
lean_inc(v_a_1937_);
lean_inc_ref(v_a_1936_);
v___x_2190_ = lean_apply_6(v_act_1933_, v_a_2189_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, lean_box(0));
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_dec(v_a_2189_);
lean_dec(v_fst_2007_);
lean_dec_ref(v_allowFailure_1934_);
return v___x_2190_;
}
else
{
lean_object* v_a_2191_; uint8_t v___y_2193_; uint8_t v___x_2214_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2191_);
v___x_2214_ = l_Lean_Exception_isInterrupt(v_a_2191_);
if (v___x_2214_ == 0)
{
uint8_t v___x_2215_; 
v___x_2215_ = l_Lean_Exception_isRuntime(v_a_2191_);
v___y_2193_ = v___x_2215_;
goto v___jp_2192_;
}
else
{
lean_dec(v_a_2191_);
v___y_2193_ = v___x_2214_;
goto v___jp_2192_;
}
v___jp_2192_:
{
if (v___y_2193_ == 0)
{
lean_object* v___x_2194_; 
lean_dec_ref_known(v___x_2190_, 1);
lean_inc(v_a_1939_);
lean_inc_ref(v_a_1938_);
lean_inc(v_a_1937_);
lean_inc_ref(v_a_1936_);
v___x_2194_ = lean_apply_6(v_allowFailure_1934_, v_fst_2007_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, lean_box(0));
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2205_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2197_ = v___x_2194_;
v_isShared_2198_ = v_isSharedCheck_2205_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2194_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2205_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
uint8_t v___x_2199_; 
v___x_2199_ = lean_unbox(v_a_2195_);
lean_dec(v_a_2195_);
if (v___x_2199_ == 0)
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
lean_del_object(v___x_2197_);
lean_dec(v_a_2189_);
v___x_2200_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1);
v___x_2201_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2200_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
return v___x_2201_;
}
else
{
lean_object* v___x_2203_; 
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 0, v_a_2189_);
v___x_2203_ = v___x_2197_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2189_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_dec(v_a_2189_);
v_a_2206_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2194_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2194_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
else
{
lean_dec(v_a_2189_);
lean_dec(v_fst_2007_);
lean_dec_ref(v_allowFailure_1934_);
return v___x_2190_;
}
}
}
}
else
{
lean_dec(v_fst_2007_);
lean_dec_ref(v_allowFailure_1934_);
lean_dec_ref(v_act_1933_);
return v___x_2188_;
}
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec(v_fst_2007_);
lean_dec_ref(v_allowFailure_1934_);
lean_dec_ref(v_act_1933_);
lean_dec_ref(v_cfg_1932_);
v_a_2216_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2185_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2185_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
}
}
else
{
goto v___jp_2112_;
}
}
else
{
goto v___jp_2112_;
}
v___jp_2023_:
{
lean_object* v___x_2027_; double v___x_2028_; double v___x_2029_; double v___x_2030_; double v___x_2031_; double v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2036_; 
v___x_2027_ = lean_io_mono_nanos_now();
v___x_2028_ = lean_float_of_nat(v___y_2025_);
v___x_2029_ = lean_float_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3);
v___x_2030_ = lean_float_div(v___x_2028_, v___x_2029_);
v___x_2031_ = lean_float_of_nat(v___x_2027_);
v___x_2032_ = lean_float_div(v___x_2031_, v___x_2029_);
v___x_2033_ = lean_box_float(v___x_2030_);
v___x_2034_ = lean_box_float(v___x_2032_);
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 1, v___x_2034_);
lean_ctor_set(v___x_2015_, 0, v___x_2033_);
v___x_2036_ = v___x_2015_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2033_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v___x_2034_);
v___x_2036_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
lean_object* v___x_2038_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 1, v___x_2036_);
lean_ctor_set(v___x_2010_, 0, v_a_2026_);
v___x_2038_ = v___x_2010_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2026_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2039_; 
v___x_2039_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v___x_2019_, v_hasTrace_1948_, v___x_2020_, v_options_1947_, v___x_2022_, v___y_2024_, v___f_2018_, v___x_2038_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
return v___x_2039_;
}
}
}
v___jp_2042_:
{
lean_object* v___x_2046_; 
v___x_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2046_, 0, v_a_2045_);
v___y_2024_ = v___y_2043_;
v___y_2025_ = v___y_2044_;
v_a_2026_ = v___x_2046_;
goto v___jp_2023_;
}
v___jp_2047_:
{
lean_object* v___x_2051_; 
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v_a_2050_);
v___y_2024_ = v___y_2048_;
v___y_2025_ = v___y_2049_;
v_a_2026_ = v___x_2051_;
goto v___jp_2023_;
}
v___jp_2052_:
{
if (lean_obj_tag(v___y_2055_) == 0)
{
lean_object* v_a_2056_; 
v_a_2056_ = lean_ctor_get(v___y_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref_known(v___y_2055_, 1);
v___y_2043_ = v___y_2053_;
v___y_2044_ = v___y_2054_;
v_a_2045_ = v_a_2056_;
goto v___jp_2042_;
}
else
{
lean_object* v_a_2057_; 
v_a_2057_ = lean_ctor_get(v___y_2055_, 0);
lean_inc(v_a_2057_);
lean_dec_ref_known(v___y_2055_, 1);
v___y_2048_ = v___y_2053_;
v___y_2049_ = v___y_2054_;
v_a_2050_ = v_a_2057_;
goto v___jp_2047_;
}
}
v___jp_2058_:
{
if (v___y_2063_ == 0)
{
lean_object* v___x_2064_; 
lean_dec_ref(v___y_2059_);
lean_inc(v_a_1939_);
lean_inc_ref(v_a_1938_);
lean_inc(v_a_1937_);
lean_inc_ref(v_a_1936_);
v___x_2064_ = lean_apply_6(v_allowFailure_1934_, v_fst_2007_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, lean_box(0));
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; uint8_t v___x_2066_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2065_);
lean_dec_ref_known(v___x_2064_, 1);
v___x_2066_ = lean_unbox(v_a_2065_);
lean_dec(v_a_2065_);
if (v___x_2066_ == 0)
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
lean_dec(v___y_2061_);
v___x_2067_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1);
v___x_2068_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2067_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
v___y_2053_ = v___y_2060_;
v___y_2054_ = v___y_2062_;
v___y_2055_ = v___x_2068_;
goto v___jp_2052_;
}
else
{
v___y_2043_ = v___y_2060_;
v___y_2044_ = v___y_2062_;
v_a_2045_ = v___y_2061_;
goto v___jp_2042_;
}
}
else
{
lean_object* v_a_2069_; 
lean_dec(v___y_2061_);
v_a_2069_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2069_);
lean_dec_ref_known(v___x_2064_, 1);
v___y_2048_ = v___y_2060_;
v___y_2049_ = v___y_2062_;
v_a_2050_ = v_a_2069_;
goto v___jp_2047_;
}
}
else
{
lean_dec(v___y_2061_);
lean_dec(v_fst_2007_);
lean_dec_ref(v_allowFailure_1934_);
v___y_2048_ = v___y_2060_;
v___y_2049_ = v___y_2062_;
v_a_2050_ = v___y_2059_;
goto v___jp_2047_;
}
}
v___jp_2070_:
{
lean_object* v___x_2074_; double v___x_2075_; double v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2074_ = lean_io_get_num_heartbeats();
v___x_2075_ = lean_float_of_nat(v___y_2071_);
v___x_2076_ = lean_float_of_nat(v___x_2074_);
v___x_2077_ = lean_box_float(v___x_2075_);
v___x_2078_ = lean_box_float(v___x_2076_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 1, v___x_2078_);
lean_ctor_set(v___x_1944_, 0, v___x_2077_);
v___x_2080_ = v___x_1944_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2077_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v___x_2078_);
v___x_2080_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2081_, 0, v_a_2073_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
v___x_2082_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v___x_2019_, v_hasTrace_1948_, v___x_2020_, v_options_1947_, v___x_2022_, v___y_2072_, v___f_2018_, v___x_2081_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
return v___x_2082_;
}
}
v___jp_2084_:
{
lean_object* v___x_2088_; 
v___x_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2088_, 0, v_a_2087_);
v___y_2071_ = v___y_2085_;
v___y_2072_ = v___y_2086_;
v_a_2073_ = v___x_2088_;
goto v___jp_2070_;
}
v___jp_2089_:
{
lean_object* v___x_2093_; 
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v_a_2092_);
v___y_2071_ = v___y_2090_;
v___y_2072_ = v___y_2091_;
v_a_2073_ = v___x_2093_;
goto v___jp_2070_;
}
v___jp_2094_:
{
if (lean_obj_tag(v___y_2097_) == 0)
{
lean_object* v_a_2098_; 
v_a_2098_ = lean_ctor_get(v___y_2097_, 0);
lean_inc(v_a_2098_);
lean_dec_ref_known(v___y_2097_, 1);
v___y_2085_ = v___y_2095_;
v___y_2086_ = v___y_2096_;
v_a_2087_ = v_a_2098_;
goto v___jp_2084_;
}
else
{
lean_object* v_a_2099_; 
v_a_2099_ = lean_ctor_get(v___y_2097_, 0);
lean_inc(v_a_2099_);
lean_dec_ref_known(v___y_2097_, 1);
v___y_2090_ = v___y_2095_;
v___y_2091_ = v___y_2096_;
v_a_2092_ = v_a_2099_;
goto v___jp_2089_;
}
}
v___jp_2100_:
{
if (v___y_2105_ == 0)
{
lean_object* v___x_2106_; 
lean_dec_ref(v___y_2104_);
lean_inc(v_a_1939_);
lean_inc_ref(v_a_1938_);
lean_inc(v_a_1937_);
lean_inc_ref(v_a_1936_);
v___x_2106_ = lean_apply_6(v_allowFailure_1934_, v_fst_2007_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, lean_box(0));
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; uint8_t v___x_2108_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2107_);
lean_dec_ref_known(v___x_2106_, 1);
v___x_2108_ = lean_unbox(v_a_2107_);
lean_dec(v_a_2107_);
if (v___x_2108_ == 0)
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
lean_dec(v___y_2103_);
v___x_2109_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1);
v___x_2110_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2109_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
v___y_2095_ = v___y_2101_;
v___y_2096_ = v___y_2102_;
v___y_2097_ = v___x_2110_;
goto v___jp_2094_;
}
else
{
v___y_2085_ = v___y_2101_;
v___y_2086_ = v___y_2102_;
v_a_2087_ = v___y_2103_;
goto v___jp_2084_;
}
}
else
{
lean_object* v_a_2111_; 
lean_dec(v___y_2103_);
v_a_2111_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2111_);
lean_dec_ref_known(v___x_2106_, 1);
v___y_2090_ = v___y_2101_;
v___y_2091_ = v___y_2102_;
v_a_2092_ = v_a_2111_;
goto v___jp_2089_;
}
}
else
{
lean_dec(v___y_2103_);
lean_dec(v_fst_2007_);
lean_dec_ref(v_allowFailure_1934_);
v___y_2090_ = v___y_2101_;
v___y_2091_ = v___y_2102_;
v_a_2092_ = v___y_2104_;
goto v___jp_2089_;
}
}
v___jp_2112_:
{
lean_object* v___x_2113_; lean_object* v_a_2114_; lean_object* v___x_2115_; uint8_t v___x_2116_; 
v___x_2113_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v_a_1939_);
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2114_);
lean_dec_ref(v___x_2113_);
v___x_2115_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2116_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_1947_, v___x_2115_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v_cache_2119_; lean_object* v_zetaDeltaFVarIds_2120_; lean_object* v_postponed_2121_; lean_object* v_diag_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2142_; 
lean_del_object(v___x_1944_);
v___x_2117_ = lean_io_mono_nanos_now();
v___x_2118_ = lean_st_ref_take(v_a_1937_);
v_cache_2119_ = lean_ctor_get(v___x_2118_, 1);
v_zetaDeltaFVarIds_2120_ = lean_ctor_get(v___x_2118_, 2);
v_postponed_2121_ = lean_ctor_get(v___x_2118_, 3);
v_diag_2122_ = lean_ctor_get(v___x_2118_, 4);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2142_ == 0)
{
lean_object* v_unused_2143_; 
v_unused_2143_ = lean_ctor_get(v___x_2118_, 0);
lean_dec(v_unused_2143_);
v___x_2124_ = v___x_2118_;
v_isShared_2125_ = v_isSharedCheck_2142_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_diag_2122_);
lean_inc(v_postponed_2121_);
lean_inc(v_zetaDeltaFVarIds_2120_);
lean_inc(v_cache_2119_);
lean_dec(v___x_2118_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2142_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 0, v_snd_2008_);
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_snd_2008_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_cache_2119_);
lean_ctor_set(v_reuseFailAlloc_2141_, 2, v_zetaDeltaFVarIds_2120_);
lean_ctor_set(v_reuseFailAlloc_2141_, 3, v_postponed_2121_);
lean_ctor_set(v_reuseFailAlloc_2141_, 4, v_diag_2122_);
v___x_2127_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
lean_object* v___x_2128_; uint8_t v___x_2129_; lean_object* v___x_2130_; 
v___x_2128_ = lean_st_ref_put(v_a_1937_, v___x_2127_);
v___x_2129_ = lean_unbox(v_snd_2013_);
lean_dec(v_snd_2013_);
v___x_2130_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2012_, v___x_2129_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v___x_2132_ = lean_box(0);
lean_inc(v_fst_2007_);
v___x_2133_ = l_Lean_MVarId_apply(v_fst_2007_, v_a_2131_, v_cfg_1932_, v___x_2132_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2135_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc_n(v_a_2134_, 2);
lean_dec_ref_known(v___x_2133_, 1);
lean_inc(v_a_1939_);
lean_inc_ref(v_a_1938_);
lean_inc(v_a_1937_);
lean_inc_ref(v_a_1936_);
v___x_2135_ = lean_apply_6(v_act_1933_, v_a_2134_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, lean_box(0));
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; 
lean_dec(v_a_2134_);
lean_dec(v_fst_2007_);
lean_dec_ref(v_allowFailure_1934_);
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2135_, 1);
v___y_2043_ = v_a_2114_;
v___y_2044_ = v___x_2117_;
v_a_2045_ = v_a_2136_;
goto v___jp_2042_;
}
else
{
lean_object* v_a_2137_; uint8_t v___x_2138_; 
v_a_2137_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2135_, 1);
v___x_2138_ = l_Lean_Exception_isInterrupt(v_a_2137_);
if (v___x_2138_ == 0)
{
uint8_t v___x_2139_; 
lean_inc(v_a_2137_);
v___x_2139_ = l_Lean_Exception_isRuntime(v_a_2137_);
v___y_2059_ = v_a_2137_;
v___y_2060_ = v_a_2114_;
v___y_2061_ = v_a_2134_;
v___y_2062_ = v___x_2117_;
v___y_2063_ = v___x_2139_;
goto v___jp_2058_;
}
else
{
v___y_2059_ = v_a_2137_;
v___y_2060_ = v_a_2114_;
v___y_2061_ = v_a_2134_;
v___y_2062_ = v___x_2117_;
v___y_2063_ = v___x_2138_;
goto v___jp_2058_;
}
}
}
else
{
lean_dec(v_fst_2007_);
lean_dec_ref(v_allowFailure_1934_);
lean_dec_ref(v_act_1933_);
v___y_2053_ = v_a_2114_;
v___y_2054_ = v___x_2117_;
v___y_2055_ = v___x_2133_;
goto v___jp_2052_;
}
}
else
{
lean_object* v_a_2140_; 
lean_dec(v_fst_2007_);
lean_dec_ref(v_allowFailure_1934_);
lean_dec_ref(v_act_1933_);
lean_dec_ref(v_cfg_1932_);
v_a_2140_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2130_, 1);
v___y_2048_ = v_a_2114_;
v___y_2049_ = v___x_2117_;
v_a_2050_ = v_a_2140_;
goto v___jp_2047_;
}
}
}
}
else
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v_cache_2146_; lean_object* v_zetaDeltaFVarIds_2147_; lean_object* v_postponed_2148_; lean_object* v_diag_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2169_; 
lean_del_object(v___x_2015_);
lean_del_object(v___x_2010_);
v___x_2144_ = lean_io_get_num_heartbeats();
v___x_2145_ = lean_st_ref_take(v_a_1937_);
v_cache_2146_ = lean_ctor_get(v___x_2145_, 1);
v_zetaDeltaFVarIds_2147_ = lean_ctor_get(v___x_2145_, 2);
v_postponed_2148_ = lean_ctor_get(v___x_2145_, 3);
v_diag_2149_ = lean_ctor_get(v___x_2145_, 4);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2169_ == 0)
{
lean_object* v_unused_2170_; 
v_unused_2170_ = lean_ctor_get(v___x_2145_, 0);
lean_dec(v_unused_2170_);
v___x_2151_ = v___x_2145_;
v_isShared_2152_ = v_isSharedCheck_2169_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_diag_2149_);
lean_inc(v_postponed_2148_);
lean_inc(v_zetaDeltaFVarIds_2147_);
lean_inc(v_cache_2146_);
lean_dec(v___x_2145_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2169_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 0, v_snd_2008_);
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_snd_2008_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v_cache_2146_);
lean_ctor_set(v_reuseFailAlloc_2168_, 2, v_zetaDeltaFVarIds_2147_);
lean_ctor_set(v_reuseFailAlloc_2168_, 3, v_postponed_2148_);
lean_ctor_set(v_reuseFailAlloc_2168_, 4, v_diag_2149_);
v___x_2154_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2155_; uint8_t v___x_2156_; lean_object* v___x_2157_; 
v___x_2155_ = lean_st_ref_put(v_a_1937_, v___x_2154_);
v___x_2156_ = lean_unbox(v_snd_2013_);
lean_dec(v_snd_2013_);
v___x_2157_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2012_, v___x_2156_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2158_);
lean_dec_ref_known(v___x_2157_, 1);
v___x_2159_ = lean_box(0);
lean_inc(v_fst_2007_);
v___x_2160_ = l_Lean_MVarId_apply(v_fst_2007_, v_a_2158_, v_cfg_1932_, v___x_2159_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2162_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc_n(v_a_2161_, 2);
lean_dec_ref_known(v___x_2160_, 1);
lean_inc(v_a_1939_);
lean_inc_ref(v_a_1938_);
lean_inc(v_a_1937_);
lean_inc_ref(v_a_1936_);
v___x_2162_ = lean_apply_6(v_act_1933_, v_a_2161_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, lean_box(0));
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; 
lean_dec(v_a_2161_);
lean_dec(v_fst_2007_);
lean_dec_ref(v_allowFailure_1934_);
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2163_);
lean_dec_ref_known(v___x_2162_, 1);
v___y_2085_ = v___x_2144_;
v___y_2086_ = v_a_2114_;
v_a_2087_ = v_a_2163_;
goto v___jp_2084_;
}
else
{
lean_object* v_a_2164_; uint8_t v___x_2165_; 
v_a_2164_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2164_);
lean_dec_ref_known(v___x_2162_, 1);
v___x_2165_ = l_Lean_Exception_isInterrupt(v_a_2164_);
if (v___x_2165_ == 0)
{
uint8_t v___x_2166_; 
lean_inc(v_a_2164_);
v___x_2166_ = l_Lean_Exception_isRuntime(v_a_2164_);
v___y_2101_ = v___x_2144_;
v___y_2102_ = v_a_2114_;
v___y_2103_ = v_a_2161_;
v___y_2104_ = v_a_2164_;
v___y_2105_ = v___x_2166_;
goto v___jp_2100_;
}
else
{
v___y_2101_ = v___x_2144_;
v___y_2102_ = v_a_2114_;
v___y_2103_ = v_a_2161_;
v___y_2104_ = v_a_2164_;
v___y_2105_ = v___x_2165_;
goto v___jp_2100_;
}
}
}
else
{
lean_dec(v_fst_2007_);
lean_dec_ref(v_allowFailure_1934_);
lean_dec_ref(v_act_1933_);
v___y_2095_ = v___x_2144_;
v___y_2096_ = v_a_2114_;
v___y_2097_ = v___x_2160_;
goto v___jp_2094_;
}
}
else
{
lean_object* v_a_2167_; 
lean_dec(v_fst_2007_);
lean_dec_ref(v_allowFailure_1934_);
lean_dec_ref(v_act_1933_);
lean_dec_ref(v_cfg_1932_);
v_a_2167_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2167_);
lean_dec_ref_known(v___x_2157_, 1);
v___y_2090_ = v___x_2144_;
v___y_2091_ = v_a_2114_;
v_a_2092_ = v_a_2167_;
goto v___jp_2089_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___boxed(lean_object* v_cfg_2230_, lean_object* v_act_2231_, lean_object* v_allowFailure_2232_, lean_object* v_cand_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(v_cfg_2230_, v_act_2231_, v_allowFailure_2232_, v_cand_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
lean_dec(v_a_2237_);
lean_dec_ref(v_a_2236_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(lean_object* v_00_u03b1_2240_, lean_object* v_x_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v___x_2247_; 
v___x_2247_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_x_2241_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2248_, lean_object* v_x_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(v_00_u03b1_2248_, v_x_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(lean_object* v_act_2258_, lean_object* v_a_2259_, uint8_t v_collectAll_2260_, lean_object* v_as_2261_, size_t v_sz_2262_, size_t v_i_2263_, lean_object* v_b_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v_a_2271_; uint8_t v___x_2275_; 
v___x_2275_ = lean_usize_dec_lt(v_i_2263_, v_sz_2262_);
if (v___x_2275_ == 0)
{
lean_object* v___x_2276_; 
lean_dec_ref(v_a_2259_);
lean_dec_ref(v_act_2258_);
v___x_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2276_, 0, v_b_2264_);
return v___x_2276_;
}
else
{
lean_object* v_snd_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2350_; 
v_snd_2277_ = lean_ctor_get(v_b_2264_, 1);
v_isSharedCheck_2350_ = !lean_is_exclusive(v_b_2264_);
if (v_isSharedCheck_2350_ == 0)
{
lean_object* v_unused_2351_; 
v_unused_2351_ = lean_ctor_get(v_b_2264_, 0);
lean_dec(v_unused_2351_);
v___x_2279_ = v_b_2264_;
v_isShared_2280_ = v_isSharedCheck_2350_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_snd_2277_);
lean_dec(v_b_2264_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2350_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2281_; lean_object* v_a_2282_; lean_object* v___x_2283_; 
v___x_2281_ = lean_box(0);
v_a_2282_ = lean_array_uget_borrowed(v_as_2261_, v_i_2263_);
lean_inc_ref(v_act_2258_);
lean_inc(v___y_2268_);
lean_inc_ref(v___y_2267_);
lean_inc(v___y_2266_);
lean_inc_ref(v___y_2265_);
lean_inc(v_a_2282_);
v___x_2283_ = lean_apply_6(v_act_2258_, v_a_2282_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, lean_box(0));
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2313_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2286_ = v___x_2283_;
v_isShared_2287_ = v_isSharedCheck_2313_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2283_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2313_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
uint8_t v___y_2306_; uint8_t v___x_2312_; 
v___x_2312_ = l_List_isEmpty___redArg(v_a_2284_);
if (v___x_2312_ == 0)
{
v___y_2306_ = v___x_2312_;
goto v___jp_2305_;
}
else
{
if (v_collectAll_2260_ == 0)
{
v___y_2306_ = v___x_2312_;
goto v___jp_2305_;
}
else
{
lean_del_object(v___x_2286_);
goto v___jp_2288_;
}
}
v___jp_2288_:
{
lean_object* v___x_2289_; lean_object* v_mctx_2290_; lean_object* v___x_2291_; 
v___x_2289_ = lean_st_ref_get(v___y_2266_);
v_mctx_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc_ref(v_mctx_2290_);
lean_dec(v___x_2289_);
lean_inc_ref(v_a_2259_);
v___x_2291_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2259_, v___y_2266_, v___y_2268_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v___x_2293_; 
lean_dec_ref_known(v___x_2291_, 1);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 1, v_mctx_2290_);
lean_ctor_set(v___x_2279_, 0, v_a_2284_);
v___x_2293_ = v___x_2279_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2284_);
lean_ctor_set(v_reuseFailAlloc_2296_, 1, v_mctx_2290_);
v___x_2293_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = lean_array_push(v_snd_2277_, v___x_2293_);
v___x_2295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2281_);
lean_ctor_set(v___x_2295_, 1, v___x_2294_);
v_a_2271_ = v___x_2295_;
goto v___jp_2270_;
}
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
lean_dec_ref(v_mctx_2290_);
lean_dec(v_a_2284_);
lean_del_object(v___x_2279_);
lean_dec(v_snd_2277_);
lean_dec_ref(v_a_2259_);
lean_dec_ref(v_act_2258_);
v_a_2297_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2291_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2291_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2302_; 
if (v_isShared_2300_ == 0)
{
v___x_2302_ = v___x_2299_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2297_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
v___jp_2305_:
{
if (v___y_2306_ == 0)
{
lean_del_object(v___x_2286_);
goto v___jp_2288_;
}
else
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2310_; 
lean_dec(v_a_2284_);
lean_del_object(v___x_2279_);
lean_dec_ref(v_a_2259_);
lean_dec_ref(v_act_2258_);
v___x_2307_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___closed__0));
v___x_2308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
lean_ctor_set(v___x_2308_, 1, v_snd_2277_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v___x_2308_);
v___x_2310_ = v___x_2286_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2308_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2349_; 
v_a_2314_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2316_ = v___x_2283_;
v_isShared_2317_ = v_isSharedCheck_2349_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2283_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2349_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
uint8_t v___y_2319_; uint8_t v___x_2347_; 
v___x_2347_ = l_Lean_Exception_isInterrupt(v_a_2314_);
if (v___x_2347_ == 0)
{
uint8_t v___x_2348_; 
lean_inc(v_a_2314_);
v___x_2348_ = l_Lean_Exception_isRuntime(v_a_2314_);
v___y_2319_ = v___x_2348_;
goto v___jp_2318_;
}
else
{
v___y_2319_ = v___x_2347_;
goto v___jp_2318_;
}
v___jp_2318_:
{
if (v___y_2319_ == 0)
{
lean_object* v___x_2320_; 
lean_del_object(v___x_2316_);
lean_inc_ref(v_a_2259_);
v___x_2320_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2259_, v___y_2266_, v___y_2268_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2334_; 
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2334_ == 0)
{
lean_object* v_unused_2335_; 
v_unused_2335_ = lean_ctor_get(v___x_2320_, 0);
lean_dec(v_unused_2335_);
v___x_2322_ = v___x_2320_;
v_isShared_2323_ = v_isSharedCheck_2334_;
goto v_resetjp_2321_;
}
else
{
lean_dec(v___x_2320_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2334_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
uint8_t v___x_2324_; 
v___x_2324_ = l_Lean_Meta_LibrarySearch_isAbortSpeculation(v_a_2314_);
lean_dec(v_a_2314_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2326_; 
lean_del_object(v___x_2322_);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v___x_2281_);
v___x_2326_ = v___x_2279_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2281_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_snd_2277_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
v_a_2271_ = v___x_2326_;
goto v___jp_2270_;
}
}
else
{
lean_object* v___x_2329_; 
lean_dec_ref(v_a_2259_);
lean_dec_ref(v_act_2258_);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v___x_2281_);
v___x_2329_ = v___x_2279_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2281_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_snd_2277_);
v___x_2329_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
lean_object* v___x_2331_; 
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 0, v___x_2329_);
v___x_2331_ = v___x_2322_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
}
else
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
lean_dec(v_a_2314_);
lean_del_object(v___x_2279_);
lean_dec(v_snd_2277_);
lean_dec_ref(v_a_2259_);
lean_dec_ref(v_act_2258_);
v_a_2336_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___x_2320_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2320_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2336_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
else
{
lean_object* v___x_2345_; 
lean_del_object(v___x_2279_);
lean_dec(v_snd_2277_);
lean_dec_ref(v_a_2259_);
lean_dec_ref(v_act_2258_);
if (v_isShared_2317_ == 0)
{
v___x_2345_ = v___x_2316_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2314_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
}
}
v___jp_2270_:
{
size_t v___x_2272_; size_t v___x_2273_; 
v___x_2272_ = ((size_t)1ULL);
v___x_2273_ = lean_usize_add(v_i_2263_, v___x_2272_);
v_i_2263_ = v___x_2273_;
v_b_2264_ = v_a_2271_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___boxed(lean_object* v_act_2352_, lean_object* v_a_2353_, lean_object* v_collectAll_2354_, lean_object* v_as_2355_, lean_object* v_sz_2356_, lean_object* v_i_2357_, lean_object* v_b_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
uint8_t v_collectAll_boxed_2364_; size_t v_sz_boxed_2365_; size_t v_i_boxed_2366_; lean_object* v_res_2367_; 
v_collectAll_boxed_2364_ = lean_unbox(v_collectAll_2354_);
v_sz_boxed_2365_ = lean_unbox_usize(v_sz_2356_);
lean_dec(v_sz_2356_);
v_i_boxed_2366_ = lean_unbox_usize(v_i_2357_);
lean_dec(v_i_2357_);
v_res_2367_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(v_act_2352_, v_a_2353_, v_collectAll_boxed_2364_, v_as_2355_, v_sz_boxed_2365_, v_i_boxed_2366_, v_b_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec_ref(v_as_2355_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryOnEach(lean_object* v_act_2373_, lean_object* v_candidates_2374_, uint8_t v_collectAll_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_){
_start:
{
lean_object* v___x_2381_; 
v___x_2381_ = l_Lean_Meta_saveState___redArg(v_a_2377_, v_a_2379_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v_a_2382_; lean_object* v___x_2383_; size_t v_sz_2384_; size_t v___x_2385_; lean_object* v___x_2386_; 
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_a_2382_);
lean_dec_ref_known(v___x_2381_, 1);
v___x_2383_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryOnEach___closed__1));
v_sz_2384_ = lean_array_size(v_candidates_2374_);
v___x_2385_ = ((size_t)0ULL);
v___x_2386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(v_act_2373_, v_a_2382_, v_collectAll_2375_, v_candidates_2374_, v_sz_2384_, v___x_2385_, v___x_2383_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2401_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2389_ = v___x_2386_;
v_isShared_2390_ = v_isSharedCheck_2401_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2386_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2401_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v_fst_2391_; 
v_fst_2391_ = lean_ctor_get(v_a_2387_, 0);
if (lean_obj_tag(v_fst_2391_) == 0)
{
lean_object* v_snd_2392_; lean_object* v___x_2393_; lean_object* v___x_2395_; 
v_snd_2392_ = lean_ctor_get(v_a_2387_, 1);
lean_inc(v_snd_2392_);
lean_dec(v_a_2387_);
v___x_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2393_, 0, v_snd_2392_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v___x_2393_);
v___x_2395_ = v___x_2389_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2393_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
else
{
lean_object* v_val_2397_; lean_object* v___x_2399_; 
lean_inc_ref(v_fst_2391_);
lean_dec(v_a_2387_);
v_val_2397_ = lean_ctor_get(v_fst_2391_, 0);
lean_inc(v_val_2397_);
lean_dec_ref_known(v_fst_2391_, 1);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v_val_2397_);
v___x_2399_ = v___x_2389_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_val_2397_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2409_; 
v_a_2402_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2404_ = v___x_2386_;
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2386_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
if (v_isShared_2405_ == 0)
{
v___x_2407_ = v___x_2404_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
lean_dec_ref(v_act_2373_);
v_a_2410_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2381_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2381_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryOnEach___boxed(lean_object* v_act_2418_, lean_object* v_candidates_2419_, lean_object* v_collectAll_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_){
_start:
{
uint8_t v_collectAll_boxed_2426_; lean_object* v_res_2427_; 
v_collectAll_boxed_2426_ = lean_unbox(v_collectAll_2420_);
v_res_2427_ = l_Lean_Meta_LibrarySearch_tryOnEach(v_act_2418_, v_candidates_2419_, v_collectAll_boxed_2426_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_);
lean_dec(v_a_2424_);
lean_dec_ref(v_a_2423_);
lean_dec(v_a_2422_);
lean_dec_ref(v_a_2421_);
lean_dec_ref(v_candidates_2419_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg(){
_start:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2429_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0, &l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0_once, _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0);
v___x_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2429_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg___boxed(lean_object* v___y_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(lean_object* v_00_u03b1_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v___x_2439_; 
v___x_2439_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___boxed(lean_object* v_00_u03b1_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(v_00_u03b1_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(lean_object* v_category_2447_, lean_object* v_opts_2448_, lean_object* v_act_2449_, lean_object* v_decl_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
lean_inc(v___y_2454_);
lean_inc_ref(v___y_2453_);
lean_inc(v___y_2452_);
lean_inc_ref(v___y_2451_);
v___x_2456_ = lean_apply_4(v_act_2449_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
v___x_2457_ = l_Lean_profileitIOUnsafe___redArg(v_category_2447_, v_opts_2448_, v___x_2456_, v_decl_2450_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg___boxed(lean_object* v_category_2458_, lean_object* v_opts_2459_, lean_object* v_act_2460_, lean_object* v_decl_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v_category_2458_, v_opts_2459_, v_act_2460_, v_decl_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec_ref(v_opts_2459_);
lean_dec_ref(v_category_2458_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(lean_object* v_00_u03b1_2468_, lean_object* v_category_2469_, lean_object* v_opts_2470_, lean_object* v_act_2471_, lean_object* v_decl_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v_category_2469_, v_opts_2470_, v_act_2471_, v_decl_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___boxed(lean_object* v_00_u03b1_2479_, lean_object* v_category_2480_, lean_object* v_opts_2481_, lean_object* v_act_2482_, lean_object* v_decl_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(v_00_u03b1_2479_, v_category_2480_, v_opts_2481_, v_act_2482_, v_decl_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec_ref(v_opts_2481_);
lean_dec_ref(v_category_2480_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0(lean_object* v_a_2490_, lean_object* v___x_2491_, lean_object* v_tactic_2492_, lean_object* v_allowFailure_2493_, lean_object* v_cand_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v___x_2500_; 
lean_inc(v___y_2498_);
lean_inc_ref(v___y_2497_);
lean_inc(v___y_2496_);
lean_inc_ref(v___y_2495_);
v___x_2500_ = lean_apply_5(v_a_2490_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, lean_box(0));
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v_a_2501_; uint8_t v___x_2502_; 
v_a_2501_ = lean_ctor_get(v___x_2500_, 0);
lean_inc(v_a_2501_);
lean_dec_ref_known(v___x_2500_, 1);
v___x_2502_ = lean_unbox(v_a_2501_);
lean_dec(v_a_2501_);
if (v___x_2502_ == 0)
{
lean_object* v___x_2503_; 
v___x_2503_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(v___x_2491_, v_tactic_2492_, v_allowFailure_2493_, v_cand_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
return v___x_2503_;
}
else
{
lean_object* v___x_2504_; lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_dec_ref(v_cand_2494_);
lean_dec_ref(v_allowFailure_2493_);
lean_dec_ref(v_tactic_2492_);
lean_dec_ref(v___x_2491_);
v___x_2504_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2504_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2504_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
lean_dec_ref(v_cand_2494_);
lean_dec_ref(v_allowFailure_2493_);
lean_dec_ref(v_tactic_2492_);
lean_dec_ref(v___x_2491_);
v_a_2513_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2500_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2500_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed(lean_object* v_a_2521_, lean_object* v___x_2522_, lean_object* v_tactic_2523_, lean_object* v_allowFailure_2524_, lean_object* v_cand_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0(v_a_2521_, v___x_2522_, v_tactic_2523_, v_allowFailure_2524_, v_cand_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
return v_res_2531_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(lean_object* v_as_2532_, size_t v_i_2533_, size_t v_stop_2534_){
_start:
{
uint8_t v___x_2535_; 
v___x_2535_ = lean_usize_dec_eq(v_i_2533_, v_stop_2534_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; lean_object* v_fst_2537_; uint8_t v___x_2538_; 
v___x_2536_ = lean_array_uget_borrowed(v_as_2532_, v_i_2533_);
v_fst_2537_ = lean_ctor_get(v___x_2536_, 0);
v___x_2538_ = l_List_isEmpty___redArg(v_fst_2537_);
if (v___x_2538_ == 0)
{
size_t v___x_2539_; size_t v___x_2540_; 
v___x_2539_ = ((size_t)1ULL);
v___x_2540_ = lean_usize_add(v_i_2533_, v___x_2539_);
v_i_2533_ = v___x_2540_;
goto _start;
}
else
{
return v___x_2538_;
}
}
else
{
uint8_t v___x_2542_; 
v___x_2542_ = 0;
return v___x_2542_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2___boxed(lean_object* v_as_2543_, lean_object* v_i_2544_, lean_object* v_stop_2545_){
_start:
{
size_t v_i_boxed_2546_; size_t v_stop_boxed_2547_; uint8_t v_res_2548_; lean_object* v_r_2549_; 
v_i_boxed_2546_ = lean_unbox_usize(v_i_2544_);
lean_dec(v_i_2544_);
v_stop_boxed_2547_ = lean_unbox_usize(v_stop_2545_);
lean_dec(v_stop_2545_);
v_res_2548_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_as_2543_, v_i_boxed_2546_, v_stop_boxed_2547_);
lean_dec_ref(v_as_2543_);
v_r_2549_ = lean_box(v_res_2548_);
return v_r_2549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(lean_object* v_goal_2550_, lean_object* v___x_2551_, size_t v_sz_2552_, size_t v_i_2553_, lean_object* v_bs_2554_){
_start:
{
uint8_t v___x_2555_; 
v___x_2555_ = lean_usize_dec_lt(v_i_2553_, v_sz_2552_);
if (v___x_2555_ == 0)
{
lean_dec_ref(v___x_2551_);
lean_dec(v_goal_2550_);
return v_bs_2554_;
}
else
{
lean_object* v_v_2556_; lean_object* v___x_2557_; lean_object* v_bs_x27_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; size_t v___x_2561_; size_t v___x_2562_; lean_object* v___x_2563_; 
v_v_2556_ = lean_array_uget(v_bs_2554_, v_i_2553_);
v___x_2557_ = lean_unsigned_to_nat(0u);
v_bs_x27_2558_ = lean_array_uset(v_bs_2554_, v_i_2553_, v___x_2557_);
lean_inc_ref(v___x_2551_);
lean_inc(v_goal_2550_);
v___x_2559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2559_, 0, v_goal_2550_);
lean_ctor_set(v___x_2559_, 1, v___x_2551_);
v___x_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
lean_ctor_set(v___x_2560_, 1, v_v_2556_);
v___x_2561_ = ((size_t)1ULL);
v___x_2562_ = lean_usize_add(v_i_2553_, v___x_2561_);
v___x_2563_ = lean_array_uset(v_bs_x27_2558_, v_i_2553_, v___x_2560_);
v_i_2553_ = v___x_2562_;
v_bs_2554_ = v___x_2563_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1___boxed(lean_object* v_goal_2565_, lean_object* v___x_2566_, lean_object* v_sz_2567_, lean_object* v_i_2568_, lean_object* v_bs_2569_){
_start:
{
size_t v_sz_boxed_2570_; size_t v_i_boxed_2571_; lean_object* v_res_2572_; 
v_sz_boxed_2570_ = lean_unbox_usize(v_sz_2567_);
lean_dec(v_sz_2567_);
v_i_boxed_2571_ = lean_unbox_usize(v_i_2568_);
lean_dec(v_i_2568_);
v_res_2572_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2565_, v___x_2566_, v_sz_boxed_2570_, v_i_boxed_2571_, v_bs_2569_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(lean_object* v_leavePercentHeartbeats_2574_, lean_object* v___x_2575_, lean_object* v_tactic_2576_, lean_object* v_allowFailure_2577_, lean_object* v_goal_2578_, uint8_t v_collectAll_2579_, uint8_t v_includeStar_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v___x_2589_; 
v___x_2589_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2574_, v___y_2583_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_object* v_a_2590_; lean_object* v___f_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2590_);
lean_dec_ref_known(v___x_2589_, 1);
v___f_2591_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2591_, 0, v_a_2590_);
lean_closure_set(v___f_2591_, 1, v___x_2575_);
lean_closure_set(v___f_2591_, 2, v_tactic_2576_);
lean_closure_set(v___f_2591_, 3, v_allowFailure_2577_);
v___x_2592_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0));
lean_inc(v_goal_2578_);
v___x_2593_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2592_, v_goal_2578_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2595_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___x_2593_, 1);
lean_inc_ref(v___f_2591_);
v___x_2595_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2591_, v_a_2594_, v_collectAll_2579_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
lean_dec(v_a_2594_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
if (lean_obj_tag(v_a_2596_) == 0)
{
lean_dec_ref_known(v___x_2595_, 1);
lean_dec_ref(v___f_2591_);
lean_dec(v_goal_2578_);
goto v___jp_2586_;
}
else
{
lean_object* v_val_2597_; lean_object* v___x_2646_; lean_object* v___x_2647_; uint8_t v___x_2648_; 
v_val_2597_ = lean_ctor_get(v_a_2596_, 0);
v___x_2646_ = lean_unsigned_to_nat(0u);
v___x_2647_ = lean_array_get_size(v_val_2597_);
v___x_2648_ = lean_nat_dec_lt(v___x_2646_, v___x_2647_);
if (v___x_2648_ == 0)
{
goto v___jp_2642_;
}
else
{
if (v___x_2648_ == 0)
{
goto v___jp_2642_;
}
else
{
size_t v___x_2649_; size_t v___x_2650_; uint8_t v___x_2651_; 
v___x_2649_ = ((size_t)0ULL);
v___x_2650_ = lean_usize_of_nat(v___x_2647_);
v___x_2651_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_val_2597_, v___x_2649_, v___x_2650_);
if (v___x_2651_ == 0)
{
goto v___jp_2642_;
}
else
{
lean_dec_ref(v___f_2591_);
lean_dec(v_goal_2578_);
return v___x_2595_;
}
}
}
v___jp_2598_:
{
if (v_includeStar_2580_ == 0)
{
lean_dec_ref(v___f_2591_);
lean_dec(v_goal_2578_);
return v___x_2595_;
}
else
{
lean_object* v___x_2599_; 
lean_inc_ref(v_a_2596_);
lean_dec_ref_known(v___x_2595_, 1);
v___x_2599_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2633_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2602_ = v___x_2599_;
v_isShared_2603_ = v_isSharedCheck_2633_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2599_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2633_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; uint8_t v___x_2606_; 
v___x_2604_ = lean_array_get_size(v_a_2600_);
v___x_2605_ = lean_unsigned_to_nat(0u);
v___x_2606_ = lean_nat_dec_eq(v___x_2604_, v___x_2605_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2607_; lean_object* v_mctx_2608_; size_t v_sz_2609_; size_t v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
lean_inc(v_val_2597_);
lean_del_object(v___x_2602_);
lean_dec_ref_known(v_a_2596_, 1);
v___x_2607_ = lean_st_ref_get(v___y_2582_);
v_mctx_2608_ = lean_ctor_get(v___x_2607_, 0);
lean_inc_ref(v_mctx_2608_);
lean_dec(v___x_2607_);
v_sz_2609_ = lean_array_size(v_a_2600_);
v___x_2610_ = ((size_t)0ULL);
v___x_2611_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2578_, v_mctx_2608_, v_sz_2609_, v___x_2610_, v_a_2600_);
v___x_2612_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2591_, v___x_2611_, v_collectAll_2579_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
lean_dec_ref(v___x_2611_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2629_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2615_ = v___x_2612_;
v_isShared_2616_ = v_isSharedCheck_2629_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2612_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2629_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
if (lean_obj_tag(v_a_2613_) == 0)
{
lean_del_object(v___x_2615_);
lean_dec(v_val_2597_);
goto v___jp_2586_;
}
else
{
lean_object* v_val_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2628_; 
v_val_2617_ = lean_ctor_get(v_a_2613_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v_a_2613_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2619_ = v_a_2613_;
v_isShared_2620_ = v_isSharedCheck_2628_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_val_2617_);
lean_dec(v_a_2613_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2628_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2621_; lean_object* v___x_2623_; 
v___x_2621_ = l_Array_append___redArg(v_val_2597_, v_val_2617_);
lean_dec(v_val_2617_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 0, v___x_2621_);
v___x_2623_ = v___x_2619_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2621_);
v___x_2623_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
lean_object* v___x_2625_; 
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v___x_2623_);
v___x_2625_ = v___x_2615_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2623_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2597_);
return v___x_2612_;
}
}
else
{
lean_object* v___x_2631_; 
lean_dec(v_a_2600_);
lean_dec_ref(v___f_2591_);
lean_dec(v_goal_2578_);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 0, v_a_2596_);
v___x_2631_ = v___x_2602_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2596_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
else
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
lean_dec_ref_known(v_a_2596_, 1);
lean_dec_ref(v___f_2591_);
lean_dec(v_goal_2578_);
v_a_2634_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2636_ = v___x_2599_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2599_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2634_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
}
v___jp_2642_:
{
if (v_collectAll_2579_ == 0)
{
lean_object* v___x_2643_; lean_object* v___x_2644_; uint8_t v___x_2645_; 
v___x_2643_ = lean_array_get_size(v_val_2597_);
v___x_2644_ = lean_unsigned_to_nat(0u);
v___x_2645_ = lean_nat_dec_eq(v___x_2643_, v___x_2644_);
if (v___x_2645_ == 0)
{
lean_dec_ref(v___f_2591_);
lean_dec(v_goal_2578_);
return v___x_2595_;
}
else
{
goto v___jp_2598_;
}
}
else
{
goto v___jp_2598_;
}
}
}
}
else
{
lean_dec_ref(v___f_2591_);
lean_dec(v_goal_2578_);
return v___x_2595_;
}
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
lean_dec_ref(v___f_2591_);
lean_dec(v_goal_2578_);
v_a_2652_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2593_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2593_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
else
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
lean_dec(v_goal_2578_);
lean_dec_ref(v_allowFailure_2577_);
lean_dec_ref(v_tactic_2576_);
lean_dec_ref(v___x_2575_);
v_a_2660_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v___x_2589_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2589_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2660_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
v___jp_2586_:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2587_ = lean_box(0);
v___x_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
return v___x_2588_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed(lean_object* v_leavePercentHeartbeats_2668_, lean_object* v___x_2669_, lean_object* v_tactic_2670_, lean_object* v_allowFailure_2671_, lean_object* v_goal_2672_, lean_object* v_collectAll_2673_, lean_object* v_includeStar_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
uint8_t v_collectAll_boxed_2680_; uint8_t v_includeStar_boxed_2681_; lean_object* v_res_2682_; 
v_collectAll_boxed_2680_ = lean_unbox(v_collectAll_2673_);
v_includeStar_boxed_2681_ = lean_unbox(v_includeStar_2674_);
v_res_2682_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(v_leavePercentHeartbeats_2668_, v___x_2669_, v_tactic_2670_, v_allowFailure_2671_, v_goal_2672_, v_collectAll_boxed_2680_, v_includeStar_boxed_2681_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v_leavePercentHeartbeats_2668_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2(lean_object* v_goal_2683_, lean_object* v_x_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = l_Lean_MVarId_getType(v_goal_2683_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2699_; 
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2693_ = v___x_2690_;
v_isShared_2694_ = v_isSharedCheck_2699_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2690_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2699_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2695_; lean_object* v___x_2697_; 
v___x_2695_ = l_Lean_MessageData_ofExpr(v_a_2691_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 0, v___x_2695_);
v___x_2697_ = v___x_2693_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2695_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
else
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
v_a_2700_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2690_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2690_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___boxed(lean_object* v_goal_2708_, lean_object* v_x_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2(v_goal_2708_, v_x_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec_ref(v_x_2709_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__6(lean_object* v_leavePercentHeartbeats_2716_, lean_object* v___x_2717_, lean_object* v_tactic_2718_, lean_object* v_allowFailure_2719_, lean_object* v_goal_2720_, uint8_t v_collectAll_2721_, uint8_t v_includeStar_2722_, uint8_t v___x_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v___x_2732_; 
v___x_2732_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2716_, v___y_2726_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; lean_object* v___f_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v___x_2732_, 1);
v___f_2734_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2734_, 0, v_a_2733_);
lean_closure_set(v___f_2734_, 1, v___x_2717_);
lean_closure_set(v___f_2734_, 2, v_tactic_2718_);
lean_closure_set(v___f_2734_, 3, v_allowFailure_2719_);
v___x_2735_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0));
lean_inc(v_goal_2720_);
v___x_2736_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2735_, v_goal_2720_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; lean_object* v___x_2738_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2737_);
lean_dec_ref_known(v___x_2736_, 1);
lean_inc_ref(v___f_2734_);
v___x_2738_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2734_, v_a_2737_, v_collectAll_2721_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
lean_dec(v_a_2737_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
if (lean_obj_tag(v_a_2739_) == 0)
{
lean_dec_ref_known(v___x_2738_, 1);
lean_dec_ref(v___f_2734_);
lean_dec(v_goal_2720_);
goto v___jp_2729_;
}
else
{
lean_object* v_val_2740_; lean_object* v___x_2790_; lean_object* v___x_2791_; uint8_t v___x_2792_; 
v_val_2740_ = lean_ctor_get(v_a_2739_, 0);
v___x_2790_ = lean_unsigned_to_nat(0u);
v___x_2791_ = lean_array_get_size(v_val_2740_);
v___x_2792_ = lean_nat_dec_lt(v___x_2790_, v___x_2791_);
if (v___x_2792_ == 0)
{
goto v___jp_2786_;
}
else
{
if (v___x_2792_ == 0)
{
goto v___jp_2786_;
}
else
{
size_t v___x_2793_; size_t v___x_2794_; uint8_t v___x_2795_; 
v___x_2793_ = ((size_t)0ULL);
v___x_2794_ = lean_usize_of_nat(v___x_2791_);
v___x_2795_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_val_2740_, v___x_2793_, v___x_2794_);
if (v___x_2795_ == 0)
{
goto v___jp_2786_;
}
else
{
if (v___x_2723_ == 0)
{
goto v___jp_2785_;
}
else
{
lean_dec_ref(v___f_2734_);
lean_dec(v_goal_2720_);
return v___x_2738_;
}
}
}
}
v___jp_2741_:
{
lean_object* v___x_2742_; 
v___x_2742_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2776_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2745_ = v___x_2742_;
v_isShared_2746_ = v_isSharedCheck_2776_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2742_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2776_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; uint8_t v___x_2749_; 
v___x_2747_ = lean_array_get_size(v_a_2743_);
v___x_2748_ = lean_unsigned_to_nat(0u);
v___x_2749_ = lean_nat_dec_eq(v___x_2747_, v___x_2748_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; lean_object* v_mctx_2751_; size_t v_sz_2752_; size_t v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
lean_inc(v_val_2740_);
lean_del_object(v___x_2745_);
lean_dec_ref_known(v_a_2739_, 1);
v___x_2750_ = lean_st_ref_get(v___y_2725_);
v_mctx_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc_ref(v_mctx_2751_);
lean_dec(v___x_2750_);
v_sz_2752_ = lean_array_size(v_a_2743_);
v___x_2753_ = ((size_t)0ULL);
v___x_2754_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2720_, v_mctx_2751_, v_sz_2752_, v___x_2753_, v_a_2743_);
v___x_2755_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2734_, v___x_2754_, v_collectAll_2721_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
lean_dec_ref(v___x_2754_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2772_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2758_ = v___x_2755_;
v_isShared_2759_ = v_isSharedCheck_2772_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2755_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2772_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
if (lean_obj_tag(v_a_2756_) == 0)
{
lean_del_object(v___x_2758_);
lean_dec(v_val_2740_);
goto v___jp_2729_;
}
else
{
lean_object* v_val_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2771_; 
v_val_2760_ = lean_ctor_get(v_a_2756_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v_a_2756_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2762_ = v_a_2756_;
v_isShared_2763_ = v_isSharedCheck_2771_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_val_2760_);
lean_dec(v_a_2756_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2771_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2764_; lean_object* v___x_2766_; 
v___x_2764_ = l_Array_append___redArg(v_val_2740_, v_val_2760_);
lean_dec(v_val_2760_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 0, v___x_2764_);
v___x_2766_ = v___x_2762_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v___x_2764_);
v___x_2766_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
lean_object* v___x_2768_; 
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v___x_2766_);
v___x_2768_ = v___x_2758_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2766_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2740_);
return v___x_2755_;
}
}
else
{
lean_object* v___x_2774_; 
lean_dec(v_a_2743_);
lean_dec_ref(v___f_2734_);
lean_dec(v_goal_2720_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v_a_2739_);
v___x_2774_ = v___x_2745_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2739_);
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
else
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
lean_dec_ref_known(v_a_2739_, 1);
lean_dec_ref(v___f_2734_);
lean_dec(v_goal_2720_);
v_a_2777_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2742_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2742_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
v___jp_2785_:
{
if (v_includeStar_2722_ == 0)
{
if (v___x_2723_ == 0)
{
lean_inc_ref(v_a_2739_);
lean_dec_ref_known(v___x_2738_, 1);
goto v___jp_2741_;
}
else
{
lean_dec_ref(v___f_2734_);
lean_dec(v_goal_2720_);
return v___x_2738_;
}
}
else
{
lean_inc_ref(v_a_2739_);
lean_dec_ref_known(v___x_2738_, 1);
goto v___jp_2741_;
}
}
v___jp_2786_:
{
if (v_collectAll_2721_ == 0)
{
if (v___x_2723_ == 0)
{
goto v___jp_2785_;
}
else
{
lean_object* v___x_2787_; lean_object* v___x_2788_; uint8_t v___x_2789_; 
v___x_2787_ = lean_array_get_size(v_val_2740_);
v___x_2788_ = lean_unsigned_to_nat(0u);
v___x_2789_ = lean_nat_dec_eq(v___x_2787_, v___x_2788_);
if (v___x_2789_ == 0)
{
lean_dec_ref(v___f_2734_);
lean_dec(v_goal_2720_);
return v___x_2738_;
}
else
{
goto v___jp_2785_;
}
}
}
else
{
goto v___jp_2785_;
}
}
}
}
else
{
lean_dec_ref(v___f_2734_);
lean_dec(v_goal_2720_);
return v___x_2738_;
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec_ref(v___f_2734_);
lean_dec(v_goal_2720_);
v_a_2796_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2736_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2736_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
lean_dec(v_goal_2720_);
lean_dec_ref(v_allowFailure_2719_);
lean_dec_ref(v_tactic_2718_);
lean_dec_ref(v___x_2717_);
v_a_2804_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2732_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2732_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
v___jp_2729_:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2730_ = lean_box(0);
v___x_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2730_);
return v___x_2731_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__6___boxed(lean_object* v_leavePercentHeartbeats_2812_, lean_object* v___x_2813_, lean_object* v_tactic_2814_, lean_object* v_allowFailure_2815_, lean_object* v_goal_2816_, lean_object* v_collectAll_2817_, lean_object* v_includeStar_2818_, lean_object* v___x_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
uint8_t v_collectAll_boxed_2825_; uint8_t v_includeStar_boxed_2826_; uint8_t v___x_13998__boxed_2827_; lean_object* v_res_2828_; 
v_collectAll_boxed_2825_ = lean_unbox(v_collectAll_2817_);
v_includeStar_boxed_2826_ = lean_unbox(v_includeStar_2818_);
v___x_13998__boxed_2827_ = lean_unbox(v___x_2819_);
v_res_2828_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__6(v_leavePercentHeartbeats_2812_, v___x_2813_, v_tactic_2814_, v_allowFailure_2815_, v_goal_2816_, v_collectAll_boxed_2825_, v_includeStar_boxed_2826_, v___x_13998__boxed_2827_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v_leavePercentHeartbeats_2812_);
return v_res_2828_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(lean_object* v_e_2829_){
_start:
{
if (lean_obj_tag(v_e_2829_) == 0)
{
uint8_t v___x_2830_; 
v___x_2830_ = 2;
return v___x_2830_;
}
else
{
lean_object* v_a_2831_; 
v_a_2831_ = lean_ctor_get(v_e_2829_, 0);
if (lean_obj_tag(v_a_2831_) == 0)
{
uint8_t v___x_2832_; 
v___x_2832_ = 1;
return v___x_2832_;
}
else
{
uint8_t v___x_2833_; 
v___x_2833_ = 0;
return v___x_2833_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4___boxed(lean_object* v_e_2834_){
_start:
{
uint8_t v_res_2835_; lean_object* v_r_2836_; 
v_res_2835_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(v_e_2834_);
lean_dec_ref(v_e_2834_);
v_r_2836_ = lean_box(v_res_2835_);
return v_r_2836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(lean_object* v_cls_2837_, uint8_t v_collapsed_2838_, lean_object* v_tag_2839_, lean_object* v_opts_2840_, uint8_t v_clsEnabled_2841_, lean_object* v_oldTraces_2842_, lean_object* v_msg_2843_, lean_object* v_resStartStop_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v_fst_2850_; lean_object* v_snd_2851_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v_data_2855_; lean_object* v_fst_2866_; lean_object* v_snd_2867_; lean_object* v___x_2868_; uint8_t v___x_2869_; lean_object* v___y_2871_; lean_object* v_a_2872_; uint8_t v___y_2887_; double v___y_2919_; 
v_fst_2850_ = lean_ctor_get(v_resStartStop_2844_, 0);
lean_inc(v_fst_2850_);
v_snd_2851_ = lean_ctor_get(v_resStartStop_2844_, 1);
lean_inc(v_snd_2851_);
lean_dec_ref(v_resStartStop_2844_);
v_fst_2866_ = lean_ctor_get(v_snd_2851_, 0);
lean_inc(v_fst_2866_);
v_snd_2867_ = lean_ctor_get(v_snd_2851_, 1);
lean_inc(v_snd_2867_);
lean_dec(v_snd_2851_);
v___x_2868_ = l_Lean_trace_profiler;
v___x_2869_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_2840_, v___x_2868_);
if (v___x_2869_ == 0)
{
v___y_2887_ = v___x_2869_;
goto v___jp_2886_;
}
else
{
lean_object* v___x_2924_; uint8_t v___x_2925_; 
v___x_2924_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2925_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_2840_, v___x_2924_);
if (v___x_2925_ == 0)
{
lean_object* v___x_2926_; lean_object* v___x_2927_; double v___x_2928_; double v___x_2929_; double v___x_2930_; 
v___x_2926_ = l_Lean_trace_profiler_threshold;
v___x_2927_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_2840_, v___x_2926_);
v___x_2928_ = lean_float_of_nat(v___x_2927_);
v___x_2929_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3);
v___x_2930_ = lean_float_div(v___x_2928_, v___x_2929_);
v___y_2919_ = v___x_2930_;
goto v___jp_2918_;
}
else
{
lean_object* v___x_2931_; lean_object* v___x_2932_; double v___x_2933_; 
v___x_2931_ = l_Lean_trace_profiler_threshold;
v___x_2932_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_2840_, v___x_2931_);
v___x_2933_ = lean_float_of_nat(v___x_2932_);
v___y_2919_ = v___x_2933_;
goto v___jp_2918_;
}
}
v___jp_2852_:
{
lean_object* v___x_2856_; 
lean_inc(v___y_2854_);
v___x_2856_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_2842_, v_data_2855_, v___y_2854_, v___y_2853_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v___x_2857_; 
lean_dec_ref_known(v___x_2856_, 1);
v___x_2857_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_2850_);
return v___x_2857_;
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_dec(v_fst_2850_);
v_a_2858_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2856_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2856_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
v___jp_2870_:
{
uint8_t v_result_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; double v___x_2876_; lean_object* v_data_2877_; 
v_result_2873_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(v_fst_2850_);
v___x_2874_ = lean_box(v_result_2873_);
v___x_2875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2874_);
v___x_2876_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0);
lean_inc_ref(v_tag_2839_);
lean_inc_ref(v___x_2875_);
lean_inc(v_cls_2837_);
v_data_2877_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2877_, 0, v_cls_2837_);
lean_ctor_set(v_data_2877_, 1, v___x_2875_);
lean_ctor_set(v_data_2877_, 2, v_tag_2839_);
lean_ctor_set_float(v_data_2877_, sizeof(void*)*3, v___x_2876_);
lean_ctor_set_float(v_data_2877_, sizeof(void*)*3 + 8, v___x_2876_);
lean_ctor_set_uint8(v_data_2877_, sizeof(void*)*3 + 16, v_collapsed_2838_);
if (v___x_2869_ == 0)
{
lean_dec_ref_known(v___x_2875_, 1);
lean_dec(v_snd_2867_);
lean_dec(v_fst_2866_);
lean_dec_ref(v_tag_2839_);
lean_dec(v_cls_2837_);
v___y_2853_ = v_a_2872_;
v___y_2854_ = v___y_2871_;
v_data_2855_ = v_data_2877_;
goto v___jp_2852_;
}
else
{
lean_object* v_data_2878_; double v___x_2879_; double v___x_2880_; 
lean_dec_ref_known(v_data_2877_, 3);
v_data_2878_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2878_, 0, v_cls_2837_);
lean_ctor_set(v_data_2878_, 1, v___x_2875_);
lean_ctor_set(v_data_2878_, 2, v_tag_2839_);
v___x_2879_ = lean_unbox_float(v_fst_2866_);
lean_dec(v_fst_2866_);
lean_ctor_set_float(v_data_2878_, sizeof(void*)*3, v___x_2879_);
v___x_2880_ = lean_unbox_float(v_snd_2867_);
lean_dec(v_snd_2867_);
lean_ctor_set_float(v_data_2878_, sizeof(void*)*3 + 8, v___x_2880_);
lean_ctor_set_uint8(v_data_2878_, sizeof(void*)*3 + 16, v_collapsed_2838_);
v___y_2853_ = v_a_2872_;
v___y_2854_ = v___y_2871_;
v_data_2855_ = v_data_2878_;
goto v___jp_2852_;
}
}
v___jp_2881_:
{
lean_object* v_ref_2882_; lean_object* v___x_2883_; 
v_ref_2882_ = lean_ctor_get(v___y_2847_, 2);
lean_inc(v___y_2848_);
lean_inc_ref(v___y_2847_);
lean_inc(v___y_2846_);
lean_inc_ref(v___y_2845_);
lean_inc(v_fst_2850_);
v___x_2883_ = lean_apply_6(v_msg_2843_, v_fst_2850_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, lean_box(0));
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2884_);
lean_dec_ref_known(v___x_2883_, 1);
v___y_2871_ = v_ref_2882_;
v_a_2872_ = v_a_2884_;
goto v___jp_2870_;
}
else
{
lean_object* v___x_2885_; 
lean_dec_ref_known(v___x_2883_, 1);
v___x_2885_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2);
v___y_2871_ = v_ref_2882_;
v_a_2872_ = v___x_2885_;
goto v___jp_2870_;
}
}
v___jp_2886_:
{
if (v_clsEnabled_2841_ == 0)
{
if (v___y_2887_ == 0)
{
lean_object* v___x_2888_; lean_object* v_traceState_2889_; lean_object* v_env_2890_; lean_object* v_nextMacroScope_2891_; lean_object* v_ngen_2892_; lean_object* v_auxDeclNGen_2893_; lean_object* v_cache_2894_; lean_object* v_recordedDeps_2895_; lean_object* v_messages_2896_; lean_object* v_infoState_2897_; lean_object* v_snapshotTasks_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2917_; 
lean_dec(v_snd_2867_);
lean_dec(v_fst_2866_);
lean_dec_ref(v_msg_2843_);
lean_dec_ref(v_tag_2839_);
lean_dec(v_cls_2837_);
v___x_2888_ = lean_st_ref_take(v___y_2848_);
v_traceState_2889_ = lean_ctor_get(v___x_2888_, 4);
v_env_2890_ = lean_ctor_get(v___x_2888_, 0);
v_nextMacroScope_2891_ = lean_ctor_get(v___x_2888_, 1);
v_ngen_2892_ = lean_ctor_get(v___x_2888_, 2);
v_auxDeclNGen_2893_ = lean_ctor_get(v___x_2888_, 3);
v_cache_2894_ = lean_ctor_get(v___x_2888_, 5);
v_recordedDeps_2895_ = lean_ctor_get(v___x_2888_, 6);
v_messages_2896_ = lean_ctor_get(v___x_2888_, 7);
v_infoState_2897_ = lean_ctor_get(v___x_2888_, 8);
v_snapshotTasks_2898_ = lean_ctor_get(v___x_2888_, 9);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2900_ = v___x_2888_;
v_isShared_2901_ = v_isSharedCheck_2917_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_snapshotTasks_2898_);
lean_inc(v_infoState_2897_);
lean_inc(v_messages_2896_);
lean_inc(v_recordedDeps_2895_);
lean_inc(v_cache_2894_);
lean_inc(v_traceState_2889_);
lean_inc(v_auxDeclNGen_2893_);
lean_inc(v_ngen_2892_);
lean_inc(v_nextMacroScope_2891_);
lean_inc(v_env_2890_);
lean_dec(v___x_2888_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2917_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
uint64_t v_tid_2902_; lean_object* v_traces_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2916_; 
v_tid_2902_ = lean_ctor_get_uint64(v_traceState_2889_, sizeof(void*)*1);
v_traces_2903_ = lean_ctor_get(v_traceState_2889_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v_traceState_2889_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2905_ = v_traceState_2889_;
v_isShared_2906_ = v_isSharedCheck_2916_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_traces_2903_);
lean_dec(v_traceState_2889_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2916_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2907_; lean_object* v___x_2909_; 
v___x_2907_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2842_, v_traces_2903_);
lean_dec_ref(v_traces_2903_);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 0, v___x_2907_);
v___x_2909_ = v___x_2905_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2907_);
lean_ctor_set_uint64(v_reuseFailAlloc_2915_, sizeof(void*)*1, v_tid_2902_);
v___x_2909_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
lean_object* v___x_2911_; 
if (v_isShared_2901_ == 0)
{
lean_ctor_set(v___x_2900_, 4, v___x_2909_);
v___x_2911_ = v___x_2900_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_env_2890_);
lean_ctor_set(v_reuseFailAlloc_2914_, 1, v_nextMacroScope_2891_);
lean_ctor_set(v_reuseFailAlloc_2914_, 2, v_ngen_2892_);
lean_ctor_set(v_reuseFailAlloc_2914_, 3, v_auxDeclNGen_2893_);
lean_ctor_set(v_reuseFailAlloc_2914_, 4, v___x_2909_);
lean_ctor_set(v_reuseFailAlloc_2914_, 5, v_cache_2894_);
lean_ctor_set(v_reuseFailAlloc_2914_, 6, v_recordedDeps_2895_);
lean_ctor_set(v_reuseFailAlloc_2914_, 7, v_messages_2896_);
lean_ctor_set(v_reuseFailAlloc_2914_, 8, v_infoState_2897_);
lean_ctor_set(v_reuseFailAlloc_2914_, 9, v_snapshotTasks_2898_);
v___x_2911_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2912_ = lean_st_ref_put(v___y_2848_, v___x_2911_);
v___x_2913_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_2850_);
return v___x_2913_;
}
}
}
}
}
else
{
goto v___jp_2881_;
}
}
else
{
goto v___jp_2881_;
}
}
v___jp_2918_:
{
double v___x_2920_; double v___x_2921_; double v___x_2922_; uint8_t v___x_2923_; 
v___x_2920_ = lean_unbox_float(v_snd_2867_);
v___x_2921_ = lean_unbox_float(v_fst_2866_);
v___x_2922_ = lean_float_sub(v___x_2920_, v___x_2921_);
v___x_2923_ = lean_float_decLt(v___y_2919_, v___x_2922_);
v___y_2887_ = v___x_2923_;
goto v___jp_2886_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4___boxed(lean_object* v_cls_2934_, lean_object* v_collapsed_2935_, lean_object* v_tag_2936_, lean_object* v_opts_2937_, lean_object* v_clsEnabled_2938_, lean_object* v_oldTraces_2939_, lean_object* v_msg_2940_, lean_object* v_resStartStop_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
uint8_t v_collapsed_boxed_2947_; uint8_t v_clsEnabled_boxed_2948_; lean_object* v_res_2949_; 
v_collapsed_boxed_2947_ = lean_unbox(v_collapsed_2935_);
v_clsEnabled_boxed_2948_ = lean_unbox(v_clsEnabled_2938_);
v_res_2949_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v_cls_2934_, v_collapsed_boxed_2947_, v_tag_2936_, v_opts_2937_, v_clsEnabled_boxed_2948_, v_oldTraces_2939_, v_msg_2940_, v_resStartStop_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec_ref(v_opts_2937_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(lean_object* v_goal_2953_, lean_object* v_tactic_2954_, lean_object* v_allowFailure_2955_, lean_object* v_leavePercentHeartbeats_2956_, uint8_t v_includeStar_2957_, uint8_t v_collectAll_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_){
_start:
{
lean_object* v_toCold_2964_; lean_object* v_options_2965_; lean_object* v_inheritedTraceOptions_2966_; uint8_t v_hasTrace_2967_; lean_object* v___x_2968_; 
v_toCold_2964_ = lean_ctor_get(v_a_2961_, 0);
v_options_2965_ = lean_ctor_get(v_toCold_2964_, 2);
v_inheritedTraceOptions_2966_ = lean_ctor_get(v_toCold_2964_, 11);
v_hasTrace_2967_ = lean_ctor_get_uint8(v_options_2965_, sizeof(void*)*1);
v___x_2968_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
if (v_hasTrace_2967_ == 0)
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___f_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2969_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2961_);
v___x_2970_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___closed__0));
v___x_2971_ = lean_box(v_collectAll_2958_);
v___x_2972_ = lean_box(v_includeStar_2957_);
v___f_2973_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed), 12, 7);
lean_closure_set(v___f_2973_, 0, v_leavePercentHeartbeats_2956_);
lean_closure_set(v___f_2973_, 1, v___x_2970_);
lean_closure_set(v___f_2973_, 2, v_tactic_2954_);
lean_closure_set(v___f_2973_, 3, v_allowFailure_2955_);
lean_closure_set(v___f_2973_, 4, v_goal_2953_);
lean_closure_set(v___f_2973_, 5, v___x_2971_);
lean_closure_set(v___f_2973_, 6, v___x_2972_);
v___x_2974_ = lean_box(0);
v___x_2975_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_2968_, v___x_2969_, v___f_2973_, v___x_2974_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_);
lean_dec_ref(v___x_2969_);
return v___x_2975_;
}
else
{
lean_object* v___f_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; uint8_t v___x_2980_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v_a_2984_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v_a_2999_; 
lean_inc(v_goal_2953_);
v___f_2976_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2976_, 0, v_goal_2953_);
v___x_2977_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_2978_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4));
v___x_2979_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2);
v___x_2980_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2966_, v_options_2965_, v___x_2979_);
if (v___x_2980_ == 0)
{
lean_object* v___x_3064_; uint8_t v___x_3065_; 
v___x_3064_ = l_Lean_trace_profiler;
v___x_3065_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_2965_, v___x_3064_);
if (v___x_3065_ == 0)
{
lean_object* v___x_3066_; uint8_t v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___f_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
lean_dec_ref(v___f_2976_);
v___x_3066_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2961_);
v___x_3067_ = 0;
v___x_3068_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3068_, 0, v___x_3067_);
lean_ctor_set_uint8(v___x_3068_, 1, v_hasTrace_2967_);
lean_ctor_set_uint8(v___x_3068_, 2, v_hasTrace_2967_);
lean_ctor_set_uint8(v___x_3068_, 3, v_hasTrace_2967_);
v___x_3069_ = lean_box(v_collectAll_2958_);
v___x_3070_ = lean_box(v_includeStar_2957_);
v___f_3071_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed), 12, 7);
lean_closure_set(v___f_3071_, 0, v_leavePercentHeartbeats_2956_);
lean_closure_set(v___f_3071_, 1, v___x_3068_);
lean_closure_set(v___f_3071_, 2, v_tactic_2954_);
lean_closure_set(v___f_3071_, 3, v_allowFailure_2955_);
lean_closure_set(v___f_3071_, 4, v_goal_2953_);
lean_closure_set(v___f_3071_, 5, v___x_3069_);
lean_closure_set(v___f_3071_, 6, v___x_3070_);
v___x_3072_ = lean_box(0);
v___x_3073_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_2968_, v___x_3066_, v___f_3071_, v___x_3072_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_);
lean_dec_ref(v___x_3066_);
return v___x_3073_;
}
else
{
goto v___jp_3008_;
}
}
else
{
goto v___jp_3008_;
}
v___jp_2981_:
{
lean_object* v___x_2985_; double v___x_2986_; double v___x_2987_; double v___x_2988_; double v___x_2989_; double v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2985_ = lean_io_mono_nanos_now();
v___x_2986_ = lean_float_of_nat(v___y_2982_);
v___x_2987_ = lean_float_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3);
v___x_2988_ = lean_float_div(v___x_2986_, v___x_2987_);
v___x_2989_ = lean_float_of_nat(v___x_2985_);
v___x_2990_ = lean_float_div(v___x_2989_, v___x_2987_);
v___x_2991_ = lean_box_float(v___x_2988_);
v___x_2992_ = lean_box_float(v___x_2990_);
v___x_2993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2991_);
lean_ctor_set(v___x_2993_, 1, v___x_2992_);
v___x_2994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2994_, 0, v_a_2984_);
lean_ctor_set(v___x_2994_, 1, v___x_2993_);
v___x_2995_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v___x_2977_, v_hasTrace_2967_, v___x_2978_, v_options_2965_, v___x_2980_, v___y_2983_, v___f_2976_, v___x_2994_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_);
return v___x_2995_;
}
v___jp_2996_:
{
lean_object* v___x_3000_; double v___x_3001_; double v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3000_ = lean_io_get_num_heartbeats();
v___x_3001_ = lean_float_of_nat(v___y_2998_);
v___x_3002_ = lean_float_of_nat(v___x_3000_);
v___x_3003_ = lean_box_float(v___x_3001_);
v___x_3004_ = lean_box_float(v___x_3002_);
v___x_3005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3003_);
lean_ctor_set(v___x_3005_, 1, v___x_3004_);
v___x_3006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3006_, 0, v_a_2999_);
lean_ctor_set(v___x_3006_, 1, v___x_3005_);
v___x_3007_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v___x_2977_, v_hasTrace_2967_, v___x_2978_, v_options_2965_, v___x_2980_, v___y_2997_, v___f_2976_, v___x_3006_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_);
return v___x_3007_;
}
v___jp_3008_:
{
lean_object* v___x_3009_; lean_object* v_a_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; 
v___x_3009_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v_a_2962_);
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3010_);
lean_dec_ref(v___x_3009_);
v___x_3011_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3012_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_2965_, v___x_3011_);
if (v___x_3012_ == 0)
{
lean_object* v___x_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___f_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3013_ = lean_io_mono_nanos_now();
v___x_3014_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2961_);
v___x_3015_ = 0;
v___x_3016_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3016_, 0, v___x_3015_);
lean_ctor_set_uint8(v___x_3016_, 1, v_hasTrace_2967_);
lean_ctor_set_uint8(v___x_3016_, 2, v_hasTrace_2967_);
lean_ctor_set_uint8(v___x_3016_, 3, v_hasTrace_2967_);
v___x_3017_ = lean_box(v_collectAll_2958_);
v___x_3018_ = lean_box(v_includeStar_2957_);
v___f_3019_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed), 12, 7);
lean_closure_set(v___f_3019_, 0, v_leavePercentHeartbeats_2956_);
lean_closure_set(v___f_3019_, 1, v___x_3016_);
lean_closure_set(v___f_3019_, 2, v_tactic_2954_);
lean_closure_set(v___f_3019_, 3, v_allowFailure_2955_);
lean_closure_set(v___f_3019_, 4, v_goal_2953_);
lean_closure_set(v___f_3019_, 5, v___x_3017_);
lean_closure_set(v___f_3019_, 6, v___x_3018_);
v___x_3020_ = lean_box(0);
v___x_3021_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_2968_, v___x_3014_, v___f_3019_, v___x_3020_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_);
lean_dec_ref(v___x_3014_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_3021_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_3021_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
if (v_isShared_3025_ == 0)
{
lean_ctor_set_tag(v___x_3024_, 1);
v___x_3027_ = v___x_3024_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3022_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
v___y_2982_ = v___x_3013_;
v___y_2983_ = v_a_3010_;
v_a_2984_ = v___x_3027_;
goto v___jp_2981_;
}
}
}
else
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
v_a_3030_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3032_ = v___x_3021_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_3021_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3035_; 
if (v_isShared_3033_ == 0)
{
lean_ctor_set_tag(v___x_3032_, 0);
v___x_3035_ = v___x_3032_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3030_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
v___y_2982_ = v___x_3013_;
v___y_2983_ = v_a_3010_;
v_a_2984_ = v___x_3035_;
goto v___jp_2981_;
}
}
}
}
else
{
lean_object* v___x_3038_; lean_object* v___x_3039_; uint8_t v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___f_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3038_ = lean_io_get_num_heartbeats();
v___x_3039_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2961_);
v___x_3040_ = 0;
v___x_3041_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3041_, 0, v___x_3040_);
lean_ctor_set_uint8(v___x_3041_, 1, v___x_3012_);
lean_ctor_set_uint8(v___x_3041_, 2, v___x_3012_);
lean_ctor_set_uint8(v___x_3041_, 3, v___x_3012_);
v___x_3042_ = lean_box(v_collectAll_2958_);
v___x_3043_ = lean_box(v_includeStar_2957_);
v___x_3044_ = lean_box(v___x_3012_);
v___f_3045_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__6___boxed), 13, 8);
lean_closure_set(v___f_3045_, 0, v_leavePercentHeartbeats_2956_);
lean_closure_set(v___f_3045_, 1, v___x_3041_);
lean_closure_set(v___f_3045_, 2, v_tactic_2954_);
lean_closure_set(v___f_3045_, 3, v_allowFailure_2955_);
lean_closure_set(v___f_3045_, 4, v_goal_2953_);
lean_closure_set(v___f_3045_, 5, v___x_3042_);
lean_closure_set(v___f_3045_, 6, v___x_3043_);
lean_closure_set(v___f_3045_, 7, v___x_3044_);
v___x_3046_ = lean_box(0);
v___x_3047_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_2968_, v___x_3039_, v___f_3045_, v___x_3046_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_);
lean_dec_ref(v___x_3039_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___x_3047_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3047_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
lean_ctor_set_tag(v___x_3050_, 1);
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3048_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
v___y_2997_ = v_a_3010_;
v___y_2998_ = v___x_3038_;
v_a_2999_ = v___x_3053_;
goto v___jp_2996_;
}
}
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
v_a_3056_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_3047_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3047_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
lean_ctor_set_tag(v___x_3058_, 0);
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
v___y_2997_ = v_a_3010_;
v___y_2998_ = v___x_3038_;
v_a_2999_ = v___x_3061_;
goto v___jp_2996_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___boxed(lean_object* v_goal_3074_, lean_object* v_tactic_3075_, lean_object* v_allowFailure_3076_, lean_object* v_leavePercentHeartbeats_3077_, lean_object* v_includeStar_3078_, lean_object* v_collectAll_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_){
_start:
{
uint8_t v_includeStar_boxed_3085_; uint8_t v_collectAll_boxed_3086_; lean_object* v_res_3087_; 
v_includeStar_boxed_3085_ = lean_unbox(v_includeStar_3078_);
v_collectAll_boxed_3086_ = lean_unbox(v_collectAll_3079_);
v_res_3087_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(v_goal_3074_, v_tactic_3075_, v_allowFailure_3076_, v_leavePercentHeartbeats_3077_, v_includeStar_boxed_3085_, v_collectAll_boxed_3086_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_);
lean_dec(v_a_3083_);
lean_dec_ref(v_a_3082_);
lean_dec(v_a_3081_);
lean_dec_ref(v_a_3080_);
return v_res_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearch(lean_object* v_goal_3088_, lean_object* v_tactic_3089_, lean_object* v_allowFailure_3090_, lean_object* v_leavePercentHeartbeats_3091_, uint8_t v_includeStar_3092_, uint8_t v_collectAll_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_){
_start:
{
lean_object* v___x_3099_; 
v___x_3099_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(v_goal_3088_, v_tactic_3089_, v_allowFailure_3090_, v_leavePercentHeartbeats_3091_, v_includeStar_3092_, v_collectAll_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearch___boxed(lean_object* v_goal_3100_, lean_object* v_tactic_3101_, lean_object* v_allowFailure_3102_, lean_object* v_leavePercentHeartbeats_3103_, lean_object* v_includeStar_3104_, lean_object* v_collectAll_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_){
_start:
{
uint8_t v_includeStar_boxed_3111_; uint8_t v_collectAll_boxed_3112_; lean_object* v_res_3113_; 
v_includeStar_boxed_3111_ = lean_unbox(v_includeStar_3104_);
v_collectAll_boxed_3112_ = lean_unbox(v_collectAll_3105_);
v_res_3113_ = l_Lean_Meta_LibrarySearch_librarySearch(v_goal_3100_, v_tactic_3101_, v_allowFailure_3102_, v_leavePercentHeartbeats_3103_, v_includeStar_boxed_3111_, v_collectAll_boxed_3112_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3109_);
lean_dec(v_a_3109_);
lean_dec_ref(v_a_3108_);
lean_dec(v_a_3107_);
lean_dec_ref(v_a_3106_);
return v_res_3113_;
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
