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
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
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
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
size_t lean_usize_of_nat(lean_object*);
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
static const lean_ctor_object l_Lean_Meta_LibrarySearch_grindDischarger___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*14 + 40, .m_other = 14, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(10000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1048576) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 1, 1, 0, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 1, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
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
lean_object* v_a_150_; lean_object* v___y_158_; lean_object* v___x_168_; 
lean_inc(v_mvarId_143_);
v___x_168_ = l_Lean_MVarId_getType(v_mvarId_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v_a_169_; lean_object* v___x_170_; 
v_a_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc_n(v_a_169_, 2);
lean_dec_ref_known(v___x_168_, 1);
v___x_170_ = l_Lean_Meta_getLevel(v_a_169_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v_a_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_a_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_a_171_);
lean_dec_ref_known(v___x_170_, 1);
v___x_172_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__2));
v___x_173_ = lean_box(0);
v___x_174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_174_, 0, v_a_171_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
v___x_175_ = l_Lean_Expr_const___override(v___x_172_, v___x_174_);
v___x_176_ = l_Lean_Expr_app___override(v___x_175_, v_a_169_);
v___x_177_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__3));
v___x_178_ = lean_box(0);
v___x_179_ = l_Lean_MVarId_apply(v_mvarId_143_, v___x_176_, v___x_177_, v___x_178_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_180_);
lean_dec_ref_known(v___x_179_, 1);
if (lean_obj_tag(v_a_180_) == 1)
{
lean_object* v_tail_181_; 
v_tail_181_ = lean_ctor_get(v_a_180_, 1);
if (lean_obj_tag(v_tail_181_) == 0)
{
lean_object* v_head_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
lean_inc(v_tail_181_);
v_head_182_ = lean_ctor_get(v_a_180_, 0);
lean_inc(v_head_182_);
lean_dec_ref_known(v_a_180_, 2);
v___x_183_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__4));
v___x_184_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_183_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_206_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_206_ == 0)
{
v___x_187_ = v___x_184_;
v_isShared_188_ = v_isSharedCheck_206_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_206_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_Meta_Grind_main(v_head_182_, v_a_185_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_204_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_204_ == 0)
{
v___x_192_ = v___x_189_;
v_isShared_193_ = v_isSharedCheck_204_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_189_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_204_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
uint8_t v___x_194_; 
v___x_194_ = l_Lean_Meta_Grind_Result_hasFailed(v_a_190_);
lean_dec(v_a_190_);
if (v___x_194_ == 0)
{
lean_object* v___x_196_; 
if (v_isShared_188_ == 0)
{
lean_ctor_set_tag(v___x_187_, 1);
lean_ctor_set(v___x_187_, 0, v_tail_181_);
v___x_196_ = v___x_187_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_tail_181_);
v___x_196_ = v_reuseFailAlloc_200_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_198_; 
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 0, v___x_196_);
v___x_198_ = v___x_192_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
else
{
lean_object* v___x_202_; 
lean_del_object(v___x_187_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 0, v___x_178_);
v___x_202_ = v___x_192_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_178_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
else
{
lean_object* v_a_205_; 
lean_del_object(v___x_187_);
v_a_205_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_a_205_);
lean_dec_ref_known(v___x_189_, 1);
v_a_150_ = v_a_205_;
goto v___jp_149_;
}
}
}
else
{
lean_object* v_a_207_; 
lean_dec(v_head_182_);
v_a_207_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_a_207_);
lean_dec_ref_known(v___x_184_, 1);
v_a_150_ = v_a_207_;
goto v___jp_149_;
}
}
else
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(v_a_180_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
lean_dec_ref_known(v_a_180_, 2);
v___y_158_ = v___x_208_;
goto v___jp_157_;
}
}
else
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(v_a_180_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
lean_dec(v_a_180_);
v___y_158_ = v___x_209_;
goto v___jp_157_;
}
}
else
{
lean_object* v_a_210_; 
v_a_210_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_210_);
lean_dec_ref_known(v___x_179_, 1);
v_a_150_ = v_a_210_;
goto v___jp_149_;
}
}
else
{
lean_object* v_a_211_; 
lean_dec(v_a_169_);
lean_dec(v_mvarId_143_);
v_a_211_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_a_211_);
lean_dec_ref_known(v___x_170_, 1);
v_a_150_ = v_a_211_;
goto v___jp_149_;
}
}
else
{
lean_object* v_a_212_; 
lean_dec(v_mvarId_143_);
v_a_212_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_a_212_);
lean_dec_ref_known(v___x_168_, 1);
v_a_150_ = v_a_212_;
goto v___jp_149_;
}
v___jp_149_:
{
uint8_t v___x_151_; 
v___x_151_ = l_Lean_Exception_isInterrupt(v_a_150_);
if (v___x_151_ == 0)
{
uint8_t v___x_152_; 
lean_inc_ref(v_a_150_);
v___x_152_ = l_Lean_Exception_isRuntime(v_a_150_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec_ref(v_a_150_);
v___x_153_ = lean_box(0);
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
else
{
lean_object* v___x_155_; 
v___x_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_155_, 0, v_a_150_);
return v___x_155_;
}
}
else
{
lean_object* v___x_156_; 
v___x_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_156_, 0, v_a_150_);
return v___x_156_;
}
}
v___jp_157_:
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_167_; 
v_a_159_ = lean_ctor_get(v___y_158_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___y_158_);
if (v_isSharedCheck_167_ == 0)
{
v___x_161_ = v___y_158_;
v_isShared_162_ = v_isSharedCheck_167_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___y_158_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_167_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v_a_163_; lean_object* v___x_165_; 
v_a_163_ = lean_ctor_get(v_a_159_, 0);
lean_inc(v_a_163_);
lean_dec(v_a_159_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v_a_163_);
v___x_165_ = v___x_161_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_163_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_grindDischarger___boxed(lean_object* v_mvarId_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Meta_LibrarySearch_grindDischarger(v_mvarId_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
return v_res_219_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_tryDischarger___lam__1(uint8_t v___x_220_, lean_object* v_x_221_){
_start:
{
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryDischarger___lam__1___boxed(lean_object* v___x_222_, lean_object* v_x_223_){
_start:
{
uint8_t v___x_3804__boxed_224_; uint8_t v_res_225_; lean_object* v_r_226_; 
v___x_3804__boxed_224_ = lean_unbox(v___x_222_);
v_res_225_ = l_Lean_Meta_LibrarySearch_tryDischarger___lam__1(v___x_3804__boxed_224_, v_x_223_);
lean_dec(v_x_223_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_tryDischarger___closed__11(void){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Array_mkArray0___redArg();
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryDischarger(lean_object* v_mvarId_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_){
_start:
{
lean_object* v_a_270_; lean_object* v___y_278_; lean_object* v___x_288_; 
lean_inc(v_mvarId_263_);
v___x_288_ = l_Lean_MVarId_getType(v_mvarId_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_a_289_; lean_object* v___x_290_; 
v_a_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc_n(v_a_289_, 2);
lean_dec_ref_known(v___x_288_, 1);
v___x_290_ = l_Lean_Meta_getLevel(v_a_289_, v_a_264_, v_a_265_, v_a_266_, v_a_267_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v_a_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_a_291_);
lean_dec_ref_known(v___x_290_, 1);
v___x_292_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__1));
v___x_293_ = lean_box(0);
v___x_294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_294_, 0, v_a_291_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
v___x_295_ = l_Lean_Expr_const___override(v___x_292_, v___x_294_);
v___x_296_ = l_Lean_Expr_app___override(v___x_295_, v_a_289_);
v___x_297_ = 0;
v___x_298_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__3));
v___x_299_ = lean_box(0);
v___x_300_ = l_Lean_MVarId_apply(v_mvarId_263_, v___x_296_, v___x_298_, v___x_299_, v_a_264_, v_a_265_, v_a_266_, v_a_267_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_351_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_351_ == 0)
{
v___x_303_ = v___x_300_;
v_isShared_304_ = v_isSharedCheck_351_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_351_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
if (lean_obj_tag(v_a_301_) == 1)
{
lean_object* v_tail_305_; 
v_tail_305_ = lean_ctor_get(v_a_301_, 1);
if (lean_obj_tag(v_tail_305_) == 0)
{
lean_object* v_head_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_347_; 
lean_inc(v_tail_305_);
v_head_306_ = lean_ctor_get(v_a_301_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v_a_301_);
if (v_isSharedCheck_347_ == 0)
{
lean_object* v_unused_348_; 
v_unused_348_ = lean_ctor_get(v_a_301_, 1);
lean_dec(v_unused_348_);
v___x_308_ = v_a_301_;
v_isShared_309_ = v_isSharedCheck_347_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_head_306_);
lean_dec(v_a_301_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_347_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v_ref_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_315_; 
v_ref_310_ = lean_ctor_get(v_a_266_, 2);
v___x_311_ = l_Lean_SourceInfo_fromRef(v_ref_310_, v___x_297_);
v___x_312_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__5));
v___x_313_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__6));
lean_inc(v___x_311_);
if (v_isShared_309_ == 0)
{
lean_ctor_set_tag(v___x_308_, 2);
lean_ctor_set(v___x_308_, 1, v___x_313_);
lean_ctor_set(v___x_308_, 0, v___x_311_);
v___x_315_ = v___x_308_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v___x_313_);
v___x_315_ = v_reuseFailAlloc_346_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_316_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__8));
v___x_317_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__10));
v___x_318_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_tryDischarger___closed__11, &l_Lean_Meta_LibrarySearch_tryDischarger___closed__11_once, _init_l_Lean_Meta_LibrarySearch_tryDischarger___closed__11);
lean_inc_n(v___x_311_, 2);
v___x_319_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_319_, 0, v___x_311_);
lean_ctor_set(v___x_319_, 1, v___x_317_);
lean_ctor_set(v___x_319_, 2, v___x_318_);
v___x_320_ = l_Lean_Syntax_node1(v___x_311_, v___x_316_, v___x_319_);
v___x_321_ = l_Lean_Syntax_node2(v___x_311_, v___x_312_, v___x_315_, v___x_320_);
v___x_322_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_322_, 0, v___x_321_);
v___x_323_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSuppressedMessages___boxed), 11, 2);
lean_closure_set(v___x_323_, 0, lean_box(0));
lean_closure_set(v___x_323_, 1, v___x_322_);
v___x_324_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___boxed), 9, 2);
lean_closure_set(v___x_324_, 0, v_head_306_);
lean_closure_set(v___x_324_, 1, v___x_323_);
v___x_325_ = lean_box(1);
v___x_326_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryDischarger___closed__13));
v___x_327_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_327_, 0, v___x_293_);
lean_ctor_set(v___x_327_, 1, v___x_325_);
lean_ctor_set(v___x_327_, 2, v_tail_305_);
lean_ctor_set(v___x_327_, 3, v___x_293_);
lean_ctor_set(v___x_327_, 4, v___x_293_);
lean_ctor_set(v___x_327_, 5, v___x_325_);
lean_ctor_set(v___x_327_, 6, v___x_293_);
v___x_328_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_324_, v___x_326_, v___x_327_, v_a_264_, v_a_265_, v_a_266_, v_a_267_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_344_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_344_ == 0)
{
v___x_331_ = v___x_328_;
v_isShared_332_ = v_isSharedCheck_344_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_328_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_344_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v_fst_333_; uint8_t v___x_334_; 
v_fst_333_ = lean_ctor_get(v_a_329_, 0);
lean_inc(v_fst_333_);
lean_dec(v_a_329_);
v___x_334_ = l_List_isEmpty___redArg(v_fst_333_);
lean_dec(v_fst_333_);
if (v___x_334_ == 0)
{
lean_object* v___x_336_; 
lean_del_object(v___x_303_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_299_);
v___x_336_ = v___x_331_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_299_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
else
{
lean_object* v___x_339_; 
if (v_isShared_304_ == 0)
{
lean_ctor_set_tag(v___x_303_, 1);
lean_ctor_set(v___x_303_, 0, v_tail_305_);
v___x_339_ = v___x_303_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_tail_305_);
v___x_339_ = v_reuseFailAlloc_343_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
lean_object* v___x_341_; 
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_339_);
v___x_341_ = v___x_331_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
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
}
else
{
lean_object* v_a_345_; 
lean_del_object(v___x_303_);
v_a_345_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_a_345_);
lean_dec_ref_known(v___x_328_, 1);
v_a_270_ = v_a_345_;
goto v___jp_269_;
}
}
}
}
else
{
lean_object* v___x_349_; 
lean_del_object(v___x_303_);
v___x_349_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(v_a_301_, v_a_264_, v_a_265_, v_a_266_, v_a_267_);
lean_dec_ref_known(v_a_301_, 2);
v___y_278_ = v___x_349_;
goto v___jp_277_;
}
}
else
{
lean_object* v___x_350_; 
lean_del_object(v___x_303_);
v___x_350_ = l_Lean_Meta_LibrarySearch_grindDischarger___lam__0(v_a_301_, v_a_264_, v_a_265_, v_a_266_, v_a_267_);
lean_dec(v_a_301_);
v___y_278_ = v___x_350_;
goto v___jp_277_;
}
}
}
else
{
lean_object* v_a_352_; 
v_a_352_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_a_352_);
lean_dec_ref_known(v___x_300_, 1);
v_a_270_ = v_a_352_;
goto v___jp_269_;
}
}
else
{
lean_object* v_a_353_; 
lean_dec(v_a_289_);
lean_dec(v_mvarId_263_);
v_a_353_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_a_353_);
lean_dec_ref_known(v___x_290_, 1);
v_a_270_ = v_a_353_;
goto v___jp_269_;
}
}
else
{
lean_object* v_a_354_; 
lean_dec(v_mvarId_263_);
v_a_354_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_a_354_);
lean_dec_ref_known(v___x_288_, 1);
v_a_270_ = v_a_354_;
goto v___jp_269_;
}
v___jp_269_:
{
uint8_t v___x_271_; 
v___x_271_ = l_Lean_Exception_isInterrupt(v_a_270_);
if (v___x_271_ == 0)
{
uint8_t v___x_272_; 
lean_inc_ref(v_a_270_);
v___x_272_ = l_Lean_Exception_isRuntime(v_a_270_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; 
lean_dec_ref(v_a_270_);
v___x_273_ = lean_box(0);
v___x_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
return v___x_274_;
}
else
{
lean_object* v___x_275_; 
v___x_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_275_, 0, v_a_270_);
return v___x_275_;
}
}
else
{
lean_object* v___x_276_; 
v___x_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_276_, 0, v_a_270_);
return v___x_276_;
}
}
v___jp_277_:
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_287_; 
v_a_279_ = lean_ctor_get(v___y_278_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___y_278_);
if (v_isSharedCheck_287_ == 0)
{
v___x_281_ = v___y_278_;
v_isShared_282_ = v_isSharedCheck_287_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___y_278_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_287_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v_a_283_; lean_object* v___x_285_; 
v_a_283_ = lean_ctor_get(v_a_279_, 0);
lean_inc(v_a_283_);
lean_dec(v_a_279_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v_a_283_);
v___x_285_ = v___x_281_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_a_283_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryDischarger___boxed(lean_object* v_mvarId_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_Meta_LibrarySearch_tryDischarger(v_mvarId_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__0(lean_object* v_x_362_, lean_object* v_x_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = lean_box(0);
v___x_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__0___boxed(lean_object* v_x_371_, lean_object* v_x_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_Meta_LibrarySearch_solveByElim___lam__0(v_x_371_, v_x_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v_x_372_);
lean_dec(v_x_371_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__1(lean_object* v_x_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
uint8_t v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_385_ = 0;
v___x_386_ = lean_box(v___x_385_);
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__1___boxed(lean_object* v_x_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_Meta_LibrarySearch_solveByElim___lam__1(v_x_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v_x_388_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(lean_object* v_msgData_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___x_401_; lean_object* v_env_402_; uint8_t v___x_403_; lean_object* v_env_404_; lean_object* v___x_405_; lean_object* v_toCold_406_; lean_object* v_mctx_407_; lean_object* v_lctx_408_; lean_object* v_options_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_401_ = lean_st_ref_get(v___y_399_);
v_env_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc_ref(v_env_402_);
lean_dec(v___x_401_);
v___x_403_ = 0;
v_env_404_ = l_Lean_Environment_setRecordingDeps(v_env_402_, v___x_403_);
v___x_405_ = lean_st_ref_get(v___y_397_);
v_toCold_406_ = lean_ctor_get(v___y_398_, 0);
v_mctx_407_ = lean_ctor_get(v___x_405_, 0);
lean_inc_ref(v_mctx_407_);
lean_dec(v___x_405_);
v_lctx_408_ = lean_ctor_get(v___y_396_, 2);
v_options_409_ = lean_ctor_get(v_toCold_406_, 2);
lean_inc_ref(v_options_409_);
lean_inc_ref(v_lctx_408_);
v___x_410_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_410_, 0, v_env_404_);
lean_ctor_set(v___x_410_, 1, v_mctx_407_);
lean_ctor_set(v___x_410_, 2, v_lctx_408_);
lean_ctor_set(v___x_410_, 3, v_options_409_);
v___x_411_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v_msgData_395_);
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0___boxed(lean_object* v_msgData_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msgData_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(lean_object* v_msg_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_ref_426_; lean_object* v___x_427_; lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_436_; 
v_ref_426_ = lean_ctor_get(v___y_423_, 2);
v___x_427_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msg_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
v_a_428_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_436_ == 0)
{
v___x_430_ = v___x_427_;
v_isShared_431_ = v_isSharedCheck_436_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_436_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_432_; lean_object* v___x_434_; 
lean_inc(v_ref_426_);
v___x_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_432_, 0, v_ref_426_);
lean_ctor_set(v___x_432_, 1, v_a_428_);
if (v_isShared_431_ == 0)
{
lean_ctor_set_tag(v___x_430_, 1);
lean_ctor_set(v___x_430_, 0, v___x_432_);
v___x_434_ = v___x_430_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg___boxed(lean_object* v_msg_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v_msg_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
return v_res_443_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__0));
v___x_446_ = l_Lean_stringToMessageData(v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__2(lean_object* v_x_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1);
v___x_454_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_453_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__2___boxed(lean_object* v_x_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_Meta_LibrarySearch_solveByElim___lam__2(v_x_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v_x_455_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim(lean_object* v_required_469_, uint8_t v_exfalso_470_, lean_object* v_goals_471_, lean_object* v_maxDepth_472_, uint8_t v_grind_473_, uint8_t v_try_x3f_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v___x_480_; uint8_t v_transparency_481_; lean_object* v___f_482_; lean_object* v___f_483_; lean_object* v___f_484_; uint8_t v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; lean_object* v___y_489_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_480_ = l_Lean_Meta_Context_config(v_a_475_);
v_transparency_481_ = lean_ctor_get_uint8(v___x_480_, 9);
lean_dec_ref(v___x_480_);
v___f_482_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__0));
v___f_483_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__1));
v___f_484_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__2));
v___x_485_ = 1;
v___x_486_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_486_, 0, v_maxDepth_472_);
lean_ctor_set(v___x_486_, 1, v___f_482_);
lean_ctor_set(v___x_486_, 2, v___f_483_);
lean_ctor_set(v___x_486_, 3, v___f_484_);
lean_ctor_set_uint8(v___x_486_, sizeof(void*)*4, v___x_485_);
v___x_487_ = 0;
v___x_508_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__3));
v___x_509_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_509_, 0, v___x_486_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
lean_ctor_set_uint8(v___x_509_, sizeof(void*)*2, v_transparency_481_);
lean_ctor_set_uint8(v___x_509_, sizeof(void*)*2 + 1, v___x_485_);
lean_ctor_set_uint8(v___x_509_, sizeof(void*)*2 + 2, v_exfalso_470_);
v___x_510_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_510_, 0, v___x_509_);
lean_ctor_set_uint8(v___x_510_, sizeof(void*)*1, v___x_485_);
lean_ctor_set_uint8(v___x_510_, sizeof(void*)*1 + 1, v___x_485_);
lean_ctor_set_uint8(v___x_510_, sizeof(void*)*1 + 2, v___x_487_);
lean_ctor_set_uint8(v___x_510_, sizeof(void*)*1 + 3, v___x_487_);
if (v_try_x3f_474_ == 0)
{
if (v_grind_473_ == 0)
{
v___y_489_ = v___x_510_;
goto v___jp_488_;
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__4));
v___x_512_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v___x_510_, v___x_511_);
v___y_489_ = v___x_512_;
goto v___jp_488_;
}
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__5));
v___x_514_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v___x_510_, v___x_513_);
v___y_489_ = v___x_514_;
goto v___jp_488_;
}
v___jp_488_:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_490_ = lean_box(0);
v___x_491_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__3));
v___x_492_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v___x_487_, v___x_487_, v___x_490_, v___x_490_, v___x_491_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v_fst_494_; lean_object* v_snd_495_; uint8_t v___x_496_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_a_493_);
lean_dec_ref_known(v___x_492_, 1);
v_fst_494_ = lean_ctor_get(v_a_493_, 0);
lean_inc(v_fst_494_);
v_snd_495_ = lean_ctor_get(v_a_493_, 1);
lean_inc(v_snd_495_);
lean_dec(v_a_493_);
v___x_496_ = l_List_isEmpty___redArg(v_required_469_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(v___y_489_, v_required_469_);
v___x_498_ = l_Lean_Meta_SolveByElim_solveByElim(v___x_497_, v_fst_494_, v_snd_495_, v_goals_471_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
return v___x_498_;
}
else
{
lean_object* v___x_499_; 
lean_dec(v_required_469_);
v___x_499_ = l_Lean_Meta_SolveByElim_solveByElim(v___y_489_, v_fst_494_, v_snd_495_, v_goals_471_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
return v___x_499_;
}
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
lean_dec_ref(v___y_489_);
lean_dec(v_goals_471_);
lean_dec(v_required_469_);
v_a_500_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_492_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_492_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___boxed(lean_object* v_required_515_, lean_object* v_exfalso_516_, lean_object* v_goals_517_, lean_object* v_maxDepth_518_, lean_object* v_grind_519_, lean_object* v_try_x3f_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
uint8_t v_exfalso_boxed_526_; uint8_t v_grind_boxed_527_; uint8_t v_try_x3f_boxed_528_; lean_object* v_res_529_; 
v_exfalso_boxed_526_ = lean_unbox(v_exfalso_516_);
v_grind_boxed_527_ = lean_unbox(v_grind_519_);
v_try_x3f_boxed_528_ = lean_unbox(v_try_x3f_520_);
v_res_529_ = l_Lean_Meta_LibrarySearch_solveByElim(v_required_515_, v_exfalso_boxed_526_, v_goals_517_, v_maxDepth_518_, v_grind_boxed_527_, v_try_x3f_boxed_528_, v_a_521_, v_a_522_, v_a_523_, v_a_524_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0(lean_object* v_00_u03b1_530_, lean_object* v_msg_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v_msg_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___boxed(lean_object* v_00_u03b1_538_, lean_object* v_msg_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0(v_00_u03b1_538_, v_msg_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx___impl(uint8_t v_x_546_){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_box(v_x_546_);
v___x_548_ = lean_obj_tag_nat(v___x_547_);
lean_dec(v___x_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx___impl___boxed(lean_object* v_x_549_){
_start:
{
uint8_t v_x_4__boxed_550_; lean_object* v_res_551_; 
v_x_4__boxed_550_ = lean_unbox(v_x_549_);
v_res_551_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx___impl(v_x_4__boxed_550_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg(lean_object* v_k_552_){
_start:
{
lean_inc(v_k_552_);
return v_k_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg___boxed(lean_object* v_k_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg(v_k_553_);
lean_dec(v_k_553_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim(lean_object* v_motive_555_, lean_object* v_ctorIdx_556_, uint8_t v_t_557_, lean_object* v_h_558_, lean_object* v_k_559_){
_start:
{
lean_inc(v_k_559_);
return v_k_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___boxed(lean_object* v_motive_560_, lean_object* v_ctorIdx_561_, lean_object* v_t_562_, lean_object* v_h_563_, lean_object* v_k_564_){
_start:
{
uint8_t v_t_boxed_565_; lean_object* v_res_566_; 
v_t_boxed_565_ = lean_unbox(v_t_562_);
v_res_566_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorElim(v_motive_560_, v_ctorIdx_561_, v_t_boxed_565_, v_h_563_, v_k_564_);
lean_dec(v_k_564_);
lean_dec(v_ctorIdx_561_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg(lean_object* v_none_567_){
_start:
{
lean_inc(v_none_567_);
return v_none_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg___boxed(lean_object* v_none_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg(v_none_568_);
lean_dec(v_none_568_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim(lean_object* v_motive_570_, uint8_t v_t_571_, lean_object* v_h_572_, lean_object* v_none_573_){
_start:
{
lean_inc(v_none_573_);
return v_none_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___boxed(lean_object* v_motive_574_, lean_object* v_t_575_, lean_object* v_h_576_, lean_object* v_none_577_){
_start:
{
uint8_t v_t_boxed_578_; lean_object* v_res_579_; 
v_t_boxed_578_ = lean_unbox(v_t_575_);
v_res_579_ = l_Lean_Meta_LibrarySearch_DeclMod_none_elim(v_motive_574_, v_t_boxed_578_, v_h_576_, v_none_577_);
lean_dec(v_none_577_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg(lean_object* v_mp_580_){
_start:
{
lean_inc(v_mp_580_);
return v_mp_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg___boxed(lean_object* v_mp_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg(v_mp_581_);
lean_dec(v_mp_581_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim(lean_object* v_motive_583_, uint8_t v_t_584_, lean_object* v_h_585_, lean_object* v_mp_586_){
_start:
{
lean_inc(v_mp_586_);
return v_mp_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___boxed(lean_object* v_motive_587_, lean_object* v_t_588_, lean_object* v_h_589_, lean_object* v_mp_590_){
_start:
{
uint8_t v_t_boxed_591_; lean_object* v_res_592_; 
v_t_boxed_591_ = lean_unbox(v_t_588_);
v_res_592_ = l_Lean_Meta_LibrarySearch_DeclMod_mp_elim(v_motive_587_, v_t_boxed_591_, v_h_589_, v_mp_590_);
lean_dec(v_mp_590_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg(lean_object* v_mpr_593_){
_start:
{
lean_inc(v_mpr_593_);
return v_mpr_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg___boxed(lean_object* v_mpr_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg(v_mpr_594_);
lean_dec(v_mpr_594_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim(lean_object* v_motive_596_, uint8_t v_t_597_, lean_object* v_h_598_, lean_object* v_mpr_599_){
_start:
{
lean_inc(v_mpr_599_);
return v_mpr_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___boxed(lean_object* v_motive_600_, lean_object* v_t_601_, lean_object* v_h_602_, lean_object* v_mpr_603_){
_start:
{
uint8_t v_t_boxed_604_; lean_object* v_res_605_; 
v_t_boxed_604_ = lean_unbox(v_t_601_);
v_res_605_ = l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim(v_motive_600_, v_t_boxed_604_, v_h_602_, v_mpr_603_);
lean_dec(v_mpr_603_);
return v_res_605_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_DeclMod_ofNat(lean_object* v_n_606_){
_start:
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = lean_nat_dec_le(v_n_606_, v___x_607_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_609_ = lean_unsigned_to_nat(1u);
v___x_610_ = lean_nat_dec_le(v_n_606_, v___x_609_);
if (v___x_610_ == 0)
{
uint8_t v___x_611_; 
v___x_611_ = 2;
return v___x_611_;
}
else
{
uint8_t v___x_612_; 
v___x_612_ = 1;
return v___x_612_;
}
}
else
{
uint8_t v___x_613_; 
v___x_613_ = 0;
return v___x_613_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ofNat___boxed(lean_object* v_n_614_){
_start:
{
uint8_t v_res_615_; lean_object* v_r_616_; 
v_res_615_ = l_Lean_Meta_LibrarySearch_DeclMod_ofNat(v_n_614_);
lean_dec(v_n_614_);
v_r_616_ = lean_box(v_res_615_);
return v_r_616_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod(uint8_t v_x_617_, uint8_t v_y_618_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_619_ = lean_box(v_x_617_);
v___x_620_ = lean_obj_tag_nat(v___x_619_);
lean_dec(v___x_619_);
v___x_621_ = lean_box(v_y_618_);
v___x_622_ = lean_obj_tag_nat(v___x_621_);
lean_dec(v___x_621_);
v___x_623_ = lean_nat_dec_eq(v___x_620_, v___x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod___boxed(lean_object* v_x_624_, lean_object* v_y_625_){
_start:
{
uint8_t v_x_23__boxed_626_; uint8_t v_y_24__boxed_627_; uint8_t v_res_628_; lean_object* v_r_629_; 
v_x_23__boxed_626_ = lean_unbox(v_x_624_);
v_y_24__boxed_627_ = lean_unbox(v_y_625_);
v_res_628_ = l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod(v_x_23__boxed_626_, v_y_24__boxed_627_);
v_r_629_ = lean_box(v_res_628_);
return v_r_629_;
}
}
static uint8_t _init_l_Lean_Meta_LibrarySearch_instInhabitedDeclMod_default(void){
_start:
{
uint8_t v___x_630_; 
v___x_630_ = 0;
return v___x_630_;
}
}
static uint8_t _init_l_Lean_Meta_LibrarySearch_instInhabitedDeclMod(void){
_start:
{
uint8_t v___x_631_; 
v___x_631_ = 0;
return v___x_631_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord(uint8_t v_x_632_, uint8_t v_y_633_){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_634_ = lean_box(v_x_632_);
v___x_635_ = lean_obj_tag_nat(v___x_634_);
lean_dec(v___x_634_);
v___x_636_ = lean_box(v_y_633_);
v___x_637_ = lean_obj_tag_nat(v___x_636_);
lean_dec(v___x_636_);
v___x_638_ = lean_nat_dec_lt(v___x_635_, v___x_637_);
if (v___x_638_ == 0)
{
uint8_t v___x_639_; 
v___x_639_ = lean_nat_dec_eq(v___x_635_, v___x_637_);
if (v___x_639_ == 0)
{
uint8_t v___x_640_; 
v___x_640_ = 2;
return v___x_640_;
}
else
{
uint8_t v___x_641_; 
v___x_641_ = 1;
return v___x_641_;
}
}
else
{
uint8_t v___x_642_; 
v___x_642_ = 0;
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord___boxed(lean_object* v_x_643_, lean_object* v_y_644_){
_start:
{
uint8_t v_x_33__boxed_645_; uint8_t v_y_34__boxed_646_; uint8_t v_res_647_; lean_object* v_r_648_; 
v_x_33__boxed_645_ = lean_unbox(v_x_643_);
v_y_34__boxed_646_ = lean_unbox(v_y_644_);
v_res_647_ = l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord(v_x_33__boxed_645_, v_y_34__boxed_646_);
v_r_648_ = lean_box(v_res_647_);
return v_r_648_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash(uint8_t v_x_651_){
_start:
{
switch(v_x_651_)
{
case 0:
{
uint64_t v___x_652_; 
v___x_652_ = 0ULL;
return v___x_652_;
}
case 1:
{
uint64_t v___x_653_; 
v___x_653_ = 1ULL;
return v___x_653_;
}
default: 
{
uint64_t v___x_654_; 
v___x_654_ = 2ULL;
return v___x_654_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash___boxed(lean_object* v_x_655_){
_start:
{
uint8_t v_x_40__boxed_656_; uint64_t v_res_657_; lean_object* v_r_658_; 
v_x_40__boxed_656_ = lean_unbox(v_x_655_);
v_res_657_ = l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash(v_x_40__boxed_656_);
v_r_658_ = lean_box_uint64(v_res_657_);
return v_r_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0(lean_object* v_k_661_, lean_object* v_b_662_, lean_object* v_c_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v___x_669_; 
lean_inc(v___y_667_);
lean_inc_ref(v___y_666_);
lean_inc(v___y_665_);
lean_inc_ref(v___y_664_);
v___x_669_ = lean_apply_7(v_k_661_, v_b_662_, v_c_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, lean_box(0));
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0___boxed(lean_object* v_k_670_, lean_object* v_b_671_, lean_object* v_c_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0(v_k_670_, v_b_671_, v_c_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(lean_object* v_type_679_, lean_object* v_k_680_, uint8_t v_cleanupAnnotations_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v___f_687_; uint8_t v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___f_687_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_687_, 0, v_k_680_);
v___x_688_ = 0;
v___x_689_ = lean_box(0);
v___x_690_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_688_, v___x_689_, v_type_679_, v___f_687_, v_cleanupAnnotations_681_, v___x_688_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_690_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_690_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
v_a_699_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_690_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_690_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___boxed(lean_object* v_type_707_, lean_object* v_k_708_, lean_object* v_cleanupAnnotations_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_715_; lean_object* v_res_716_; 
v_cleanupAnnotations_boxed_715_ = lean_unbox(v_cleanupAnnotations_709_);
v_res_716_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_707_, v_k_708_, v_cleanupAnnotations_boxed_715_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0(lean_object* v_00_u03b1_717_, lean_object* v_type_718_, lean_object* v_k_719_, uint8_t v_cleanupAnnotations_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_718_, v_k_719_, v_cleanupAnnotations_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___boxed(lean_object* v_00_u03b1_727_, lean_object* v_type_728_, lean_object* v_k_729_, lean_object* v_cleanupAnnotations_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_736_; lean_object* v_res_737_; 
v_cleanupAnnotations_boxed_736_ = lean_unbox(v_cleanupAnnotations_730_);
v_res_737_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0(v_00_u03b1_727_, v_type_728_, v_k_729_, v_cleanupAnnotations_boxed_736_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0(lean_object* v_name_744_, lean_object* v_x_745_, lean_object* v_type_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
uint8_t v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_752_ = 0;
v___x_753_ = lean_box(v___x_752_);
lean_inc(v_name_744_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v_name_744_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_type_746_, v___x_754_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_805_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_805_ == 0)
{
v___x_758_ = v___x_755_;
v_isShared_759_ = v_isSharedCheck_805_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_755_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_805_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v_key_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v_key_760_ = lean_ctor_get(v_a_756_, 0);
v___x_761_ = lean_unsigned_to_nat(1u);
v___x_762_ = lean_mk_empty_array_with_capacity(v___x_761_);
lean_inc(v_a_756_);
v___x_763_ = lean_array_push(v___x_762_, v_a_756_);
v___x_764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__2));
v___x_765_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_760_, v___x_764_);
if (v___x_765_ == 0)
{
lean_object* v___x_767_; 
lean_dec(v_a_756_);
lean_dec(v_name_744_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v___x_763_);
v___x_767_ = v___x_758_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_763_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
else
{
lean_object* v___x_769_; uint8_t v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
lean_del_object(v___x_758_);
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = 1;
v___x_771_ = lean_box(v___x_770_);
lean_inc(v_name_744_);
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v_name_744_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
lean_inc(v_a_756_);
v___x_773_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_a_756_, v___x_769_, v___x_772_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v___x_775_; uint8_t v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_774_);
lean_dec_ref_known(v___x_773_, 1);
v___x_775_ = lean_array_push(v___x_763_, v_a_774_);
v___x_776_ = 2;
v___x_777_ = lean_box(v___x_776_);
v___x_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_778_, 0, v_name_744_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_a_756_, v___x_761_, v___x_778_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_788_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_788_ == 0)
{
v___x_782_ = v___x_779_;
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_784_ = lean_array_push(v___x_775_, v_a_780_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_784_);
v___x_786_ = v___x_782_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
else
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
lean_dec_ref(v___x_775_);
v_a_789_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___x_779_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_779_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
lean_dec_ref(v___x_763_);
lean_dec(v_a_756_);
lean_dec(v_name_744_);
v_a_797_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_773_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_773_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
}
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_dec(v_name_744_);
v_a_806_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_755_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_755_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___boxed(lean_object* v_name_814_, lean_object* v_x_815_, lean_object* v_type_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0(v_name_814_, v_x_815_, v_type_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec_ref(v_x_815_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport(lean_object* v_name_825_, lean_object* v_c_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
lean_object* v___f_832_; lean_object* v___x_833_; lean_object* v_env_834_; uint8_t v___x_835_; 
lean_inc_n(v_name_825_, 2);
v___f_832_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___boxed), 8, 1);
lean_closure_set(v___f_832_, 0, v_name_825_);
v___x_833_ = lean_st_ref_get(v_a_830_);
v_env_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc_ref(v_env_834_);
lean_dec(v___x_833_);
v___x_835_ = l_Lean_Linter_isDeprecated(v_env_834_, v_name_825_);
if (v___x_835_ == 0)
{
uint8_t v___x_836_; 
v___x_836_ = l_Lean_Name_isMetaprogramming(v_name_825_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; lean_object* v_type_838_; lean_object* v___x_839_; 
v___x_837_ = l_Lean_AsyncConstantInfo_toConstantVal(v_c_826_);
v_type_838_ = lean_ctor_get(v___x_837_, 2);
lean_inc_ref(v_type_838_);
lean_dec_ref(v___x_837_);
v___x_839_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_838_, v___f_832_, v___x_836_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
return v___x_839_;
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; 
lean_dec_ref(v___f_832_);
lean_dec_ref(v_c_826_);
v___x_840_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0));
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
}
else
{
lean_object* v___x_842_; lean_object* v___x_843_; 
lean_dec_ref(v___f_832_);
lean_dec_ref(v_c_826_);
lean_dec(v_name_825_);
v___x_842_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0));
v___x_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
return v___x_843_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___boxed(lean_object* v_name_844_, lean_object* v_c_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport(v_name_844_, v_c_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_858108106____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_853_ = lean_box(0);
v___x_854_ = lean_st_mk_ref(v___x_853_);
v___x_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_858108106____hygCtx___hyg_2____boxed(lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_858108106____hygCtx___hyg_2_();
return v_res_857_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_constantsPerImportTask(void){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = lean_unsigned_to_nat(6500u);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2955776588____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_885_ = lean_box(0);
v___x_886_ = lean_st_mk_ref(v___x_885_);
v___x_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2955776588____hygCtx___hyg_2____boxed(lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2955776588____hygCtx___hyg_2_();
return v_res_889_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1(void){
_start:
{
lean_object* v_droppedRef_891_; lean_object* v___x_892_; 
v_droppedRef_891_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt;
v___x_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_892_, 0, v_droppedRef_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_libSearchFindDecls(lean_object* v_ty_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_899_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_ext;
v___x_900_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__0));
v___x_901_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_droppedKeys));
v___x_902_ = lean_unsigned_to_nat(6500u);
v___x_903_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1, &l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1_once, _init_l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1);
v___x_904_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v___x_899_, v___x_900_, v___x_901_, v___x_902_, v___x_903_, v_ty_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_libSearchFindDecls___boxed(lean_object* v_ty_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_Meta_LibrarySearch_libSearchFindDecls(v_ty_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
return v_res_911_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_915_ = lean_box(0);
v___x_916_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_getStarLemmas___closed__1));
v___x_917_ = l_Lean_mkConst(v___x_916_, v___x_915_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_getStarLemmas(lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v_ref_925_; lean_object* v___x_926_; 
v_ref_925_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt;
v___x_926_ = lean_st_ref_get(v_ref_925_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2, &l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2_once, _init_l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2);
v___x_928_ = l_Lean_Meta_LibrarySearch_libSearchFindDecls(v___x_927_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_941_; 
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_941_ == 0)
{
lean_object* v_unused_942_; 
v_unused_942_ = lean_ctor_get(v___x_928_, 0);
lean_dec(v_unused_942_);
v___x_930_ = v___x_928_;
v_isShared_931_ = v_isSharedCheck_941_;
goto v_resetjp_929_;
}
else
{
lean_dec(v___x_928_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_941_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_932_; 
v___x_932_ = lean_st_ref_get(v_ref_925_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_933_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_getStarLemmas___closed__3));
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_933_);
v___x_935_ = v___x_930_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
else
{
lean_object* v_val_937_; lean_object* v___x_939_; 
v_val_937_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_val_937_);
lean_dec_ref_known(v___x_932_, 1);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v_val_937_);
v___x_939_ = v___x_930_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_val_937_);
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
return v___x_928_;
}
}
else
{
lean_object* v_val_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
v_val_943_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_926_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_val_943_);
lean_dec(v___x_926_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set_tag(v___x_945_, 0);
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_val_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_getStarLemmas___boxed(lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v_a_951_, v_a_952_, v_a_953_, v_a_954_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0(uint8_t v___x_957_, lean_object* v___x_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
if (v___x_957_ == 0)
{
lean_object* v___x_964_; 
v___x_964_ = l_Lean_getRemainingHeartbeats___redArg(v___y_961_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_974_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_974_ == 0)
{
v___x_967_ = v___x_964_;
v_isShared_968_ = v_isSharedCheck_974_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_964_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_974_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
uint8_t v___x_969_; lean_object* v___x_970_; lean_object* v___x_972_; 
v___x_969_ = lean_nat_dec_lt(v_a_965_, v___x_958_);
lean_dec(v_a_965_);
v___x_970_ = lean_box(v___x_969_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 0, v___x_970_);
v___x_972_ = v___x_967_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
v_a_975_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_964_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_964_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
else
{
uint8_t v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_983_ = 0;
v___x_984_ = lean_box(v___x_983_);
v___x_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
return v___x_985_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0___boxed(lean_object* v___x_986_, lean_object* v___x_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
uint8_t v___x_649__boxed_993_; lean_object* v_res_994_; 
v___x_649__boxed_993_ = lean_unbox(v___x_986_);
v_res_994_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0(v___x_649__boxed_993_, v___x_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___x_987_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(lean_object* v_leavePercent_995_, lean_object* v_a_996_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_getMaxHeartbeats___redArg(v_a_996_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1000_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref_known(v___x_998_, 1);
v___x_1000_ = l_Lean_getRemainingHeartbeats___redArg(v_a_996_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1015_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1003_ = v___x_1000_;
v_isShared_1004_ = v_isSharedCheck_1015_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_1000_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1015_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; uint8_t v___x_1009_; lean_object* v___x_1010_; lean_object* v___y_1011_; lean_object* v___x_1013_; 
v___x_1005_ = lean_nat_mul(v_a_1001_, v_leavePercent_995_);
lean_dec(v_a_1001_);
v___x_1006_ = lean_unsigned_to_nat(100u);
v___x_1007_ = lean_nat_div(v___x_1005_, v___x_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_unsigned_to_nat(0u);
v___x_1009_ = lean_nat_dec_eq(v_a_999_, v___x_1008_);
lean_dec(v_a_999_);
v___x_1010_ = lean_box(v___x_1009_);
v___y_1011_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___y_1011_, 0, v___x_1010_);
lean_closure_set(v___y_1011_, 1, v___x_1007_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v___y_1011_);
v___x_1013_ = v___x_1003_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___y_1011_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_dec(v_a_999_);
v_a_1016_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_1000_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1000_);
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
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
v_a_1024_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_998_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_998_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___boxed(lean_object* v_leavePercent_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercent_1032_, v_a_1033_);
lean_dec_ref(v_a_1033_);
lean_dec(v_leavePercent_1032_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck(lean_object* v_leavePercent_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercent_1036_, v_a_1039_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___boxed(lean_object* v_leavePercent_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck(v_leavePercent_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
lean_dec(v_leavePercent_1043_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(lean_object* v_upperBound_1050_, lean_object* v_x_1051_, lean_object* v_f_1052_, lean_object* v_y_1053_, lean_object* v_g_1054_, lean_object* v_a_1055_, lean_object* v_b_1056_){
_start:
{
uint8_t v___x_1057_; 
v___x_1057_ = lean_nat_dec_lt(v_a_1055_, v_upperBound_1050_);
if (v___x_1057_ == 0)
{
lean_dec(v_a_1055_);
lean_dec(v_g_1054_);
lean_dec(v_f_1052_);
return v_b_1056_;
}
else
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1058_ = lean_array_fget_borrowed(v_x_1051_, v_a_1055_);
lean_inc(v_f_1052_);
lean_inc(v___x_1058_);
v___x_1059_ = lean_apply_1(v_f_1052_, v___x_1058_);
v___x_1060_ = lean_array_push(v_b_1056_, v___x_1059_);
v___x_1061_ = lean_array_fget_borrowed(v_y_1053_, v_a_1055_);
lean_inc(v_g_1054_);
lean_inc(v___x_1061_);
v___x_1062_ = lean_apply_1(v_g_1054_, v___x_1061_);
v___x_1063_ = lean_array_push(v___x_1060_, v___x_1062_);
v___x_1064_ = lean_unsigned_to_nat(1u);
v___x_1065_ = lean_nat_add(v_a_1055_, v___x_1064_);
lean_dec(v_a_1055_);
v_a_1055_ = v___x_1065_;
v_b_1056_ = v___x_1063_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg___boxed(lean_object* v_upperBound_1067_, lean_object* v_x_1068_, lean_object* v_f_1069_, lean_object* v_y_1070_, lean_object* v_g_1071_, lean_object* v_a_1072_, lean_object* v_b_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v_upperBound_1067_, v_x_1068_, v_f_1069_, v_y_1070_, v_g_1071_, v_a_1072_, v_b_1073_);
lean_dec_ref(v_y_1070_);
lean_dec_ref(v_x_1068_);
lean_dec(v_upperBound_1067_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(lean_object* v_g_1075_, size_t v_sz_1076_, size_t v_i_1077_, lean_object* v_bs_1078_){
_start:
{
uint8_t v___x_1079_; 
v___x_1079_ = lean_usize_dec_lt(v_i_1077_, v_sz_1076_);
if (v___x_1079_ == 0)
{
lean_dec(v_g_1075_);
return v_bs_1078_;
}
else
{
lean_object* v_v_1080_; lean_object* v___x_1081_; lean_object* v_bs_x27_1082_; lean_object* v___x_1083_; size_t v___x_1084_; size_t v___x_1085_; lean_object* v___x_1086_; 
v_v_1080_ = lean_array_uget(v_bs_1078_, v_i_1077_);
v___x_1081_ = lean_unsigned_to_nat(0u);
v_bs_x27_1082_ = lean_array_uset(v_bs_1078_, v_i_1077_, v___x_1081_);
lean_inc(v_g_1075_);
v___x_1083_ = lean_apply_1(v_g_1075_, v_v_1080_);
v___x_1084_ = ((size_t)1ULL);
v___x_1085_ = lean_usize_add(v_i_1077_, v___x_1084_);
v___x_1086_ = lean_array_uset(v_bs_x27_1082_, v_i_1077_, v___x_1083_);
v_i_1077_ = v___x_1085_;
v_bs_1078_ = v___x_1086_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg___boxed(lean_object* v_g_1088_, lean_object* v_sz_1089_, lean_object* v_i_1090_, lean_object* v_bs_1091_){
_start:
{
size_t v_sz_boxed_1092_; size_t v_i_boxed_1093_; lean_object* v_res_1094_; 
v_sz_boxed_1092_ = lean_unbox_usize(v_sz_1089_);
lean_dec(v_sz_1089_);
v_i_boxed_1093_ = lean_unbox_usize(v_i_1090_);
lean_dec(v_i_1090_);
v_res_1094_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1088_, v_sz_boxed_1092_, v_i_boxed_1093_, v_bs_1091_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___redArg(lean_object* v_f_1095_, lean_object* v_x_1096_, lean_object* v_g_1097_, lean_object* v_y_1098_){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v_res_1102_; lean_object* v___y_1104_; uint8_t v___x_1118_; 
v___x_1099_ = lean_array_get_size(v_x_1096_);
v___x_1100_ = lean_array_get_size(v_y_1098_);
v___x_1101_ = lean_nat_add(v___x_1099_, v___x_1100_);
v_res_1102_ = lean_mk_empty_array_with_capacity(v___x_1101_);
lean_dec(v___x_1101_);
v___x_1118_ = lean_nat_dec_le(v___x_1099_, v___x_1100_);
if (v___x_1118_ == 0)
{
v___y_1104_ = v___x_1100_;
goto v___jp_1103_;
}
else
{
v___y_1104_ = v___x_1099_;
goto v___jp_1103_;
}
v___jp_1103_:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1105_ = lean_unsigned_to_nat(0u);
lean_inc(v_g_1097_);
lean_inc(v_f_1095_);
v___x_1106_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v___y_1104_, v_x_1096_, v_f_1095_, v_y_1098_, v_g_1097_, v___x_1105_, v_res_1102_);
v___x_1107_ = lean_nat_dec_lt(v___y_1104_, v___x_1099_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; size_t v_sz_1109_; size_t v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
lean_dec(v_f_1095_);
v___x_1108_ = l_Array_extract___redArg(v_y_1098_, v___y_1104_, v___x_1100_);
v_sz_1109_ = lean_array_size(v___x_1108_);
v___x_1110_ = ((size_t)0ULL);
v___x_1111_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1097_, v_sz_1109_, v___x_1110_, v___x_1108_);
v___x_1112_ = l_Array_append___redArg(v___x_1106_, v___x_1111_);
lean_dec_ref(v___x_1111_);
return v___x_1112_;
}
else
{
lean_object* v___x_1113_; size_t v_sz_1114_; size_t v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
lean_dec(v_g_1097_);
v___x_1113_ = l_Array_extract___redArg(v_x_1096_, v___y_1104_, v___x_1099_);
v_sz_1114_ = lean_array_size(v___x_1113_);
v___x_1115_ = ((size_t)0ULL);
v___x_1116_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_f_1095_, v_sz_1114_, v___x_1115_, v___x_1113_);
v___x_1117_ = l_Array_append___redArg(v___x_1106_, v___x_1116_);
lean_dec_ref(v___x_1116_);
return v___x_1117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___redArg___boxed(lean_object* v_f_1119_, lean_object* v_x_1120_, lean_object* v_g_1121_, lean_object* v_y_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v_f_1119_, v_x_1120_, v_g_1121_, v_y_1122_);
lean_dec_ref(v_y_1122_);
lean_dec_ref(v_x_1120_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith(lean_object* v_00_u03b1_1124_, lean_object* v_00_u03b2_1125_, lean_object* v_00_u03b3_1126_, lean_object* v_f_1127_, lean_object* v_x_1128_, lean_object* v_g_1129_, lean_object* v_y_1130_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v_f_1127_, v_x_1128_, v_g_1129_, v_y_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___boxed(lean_object* v_00_u03b1_1132_, lean_object* v_00_u03b2_1133_, lean_object* v_00_u03b3_1134_, lean_object* v_f_1135_, lean_object* v_x_1136_, lean_object* v_g_1137_, lean_object* v_y_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_Meta_LibrarySearch_interleaveWith(v_00_u03b1_1132_, v_00_u03b2_1133_, v_00_u03b3_1134_, v_f_1135_, v_x_1136_, v_g_1137_, v_y_1138_);
lean_dec_ref(v_y_1138_);
lean_dec_ref(v_x_1136_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0(lean_object* v_00_u03b2_1140_, lean_object* v_00_u03b3_1141_, lean_object* v_g_1142_, size_t v_sz_1143_, size_t v_i_1144_, lean_object* v_bs_1145_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1142_, v_sz_1143_, v_i_1144_, v_bs_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___boxed(lean_object* v_00_u03b2_1147_, lean_object* v_00_u03b3_1148_, lean_object* v_g_1149_, lean_object* v_sz_1150_, lean_object* v_i_1151_, lean_object* v_bs_1152_){
_start:
{
size_t v_sz_boxed_1153_; size_t v_i_boxed_1154_; lean_object* v_res_1155_; 
v_sz_boxed_1153_ = lean_unbox_usize(v_sz_1150_);
lean_dec(v_sz_1150_);
v_i_boxed_1154_ = lean_unbox_usize(v_i_1151_);
lean_dec(v_i_1151_);
v_res_1155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0(v_00_u03b2_1147_, v_00_u03b3_1148_, v_g_1149_, v_sz_boxed_1153_, v_i_boxed_1154_, v_bs_1152_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1(lean_object* v_00_u03b3_1156_, lean_object* v_upperBound_1157_, lean_object* v_00_u03b1_1158_, lean_object* v_x_1159_, lean_object* v_f_1160_, lean_object* v_00_u03b2_1161_, lean_object* v_y_1162_, lean_object* v_g_1163_, lean_object* v_inst_1164_, lean_object* v_R_1165_, lean_object* v_a_1166_, lean_object* v_b_1167_, lean_object* v_c_1168_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v_upperBound_1157_, v_x_1159_, v_f_1160_, v_y_1162_, v_g_1163_, v_a_1166_, v_b_1167_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___boxed(lean_object* v_00_u03b3_1170_, lean_object* v_upperBound_1171_, lean_object* v_00_u03b1_1172_, lean_object* v_x_1173_, lean_object* v_f_1174_, lean_object* v_00_u03b2_1175_, lean_object* v_y_1176_, lean_object* v_g_1177_, lean_object* v_inst_1178_, lean_object* v_R_1179_, lean_object* v_a_1180_, lean_object* v_b_1181_, lean_object* v_c_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1(v_00_u03b3_1170_, v_upperBound_1171_, v_00_u03b1_1172_, v_x_1173_, v_f_1174_, v_00_u03b2_1175_, v_y_1176_, v_g_1177_, v_inst_1178_, v_R_1179_, v_a_1180_, v_b_1181_, v_c_1182_);
lean_dec_ref(v_y_1176_);
lean_dec_ref(v_x_1173_);
lean_dec(v_upperBound_1171_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_));
v___x_1192_ = l_Lean_registerInternalExceptionId(v___x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2____boxed(lean_object* v_a_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_();
return v_res_1194_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = lean_box(0);
v___x_1196_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_abortSpeculationId;
v___x_1197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
lean_ctor_set(v___x_1197_, 1, v___x_1195_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___redArg(lean_object* v_inst_1198_){
_start:
{
lean_object* v_throw_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v_throw_1199_ = lean_ctor_get(v_inst_1198_, 0);
lean_inc(v_throw_1199_);
lean_dec_ref(v_inst_1198_);
v___x_1200_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0, &l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0_once, _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0);
v___x_1201_ = lean_apply_2(v_throw_1199_, lean_box(0), v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation(lean_object* v_m_1202_, lean_object* v_00_u03b1_1203_, lean_object* v_inst_1204_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Lean_Meta_LibrarySearch_abortSpeculation___redArg(v_inst_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_isAbortSpeculation(lean_object* v_x_1206_){
_start:
{
if (lean_obj_tag(v_x_1206_) == 1)
{
lean_object* v_id_1207_; lean_object* v___x_1208_; uint8_t v___x_1209_; 
v_id_1207_ = lean_ctor_get(v_x_1206_, 0);
v___x_1208_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_abortSpeculationId;
v___x_1209_ = l_Lean_instBEqInternalExceptionId_beq(v_id_1207_, v___x_1208_);
return v___x_1209_;
}
else
{
uint8_t v___x_1210_; 
v___x_1210_ = 0;
return v___x_1210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_isAbortSpeculation___boxed(lean_object* v_x_1211_){
_start:
{
uint8_t v_res_1212_; lean_object* v_r_1213_; 
v_res_1212_ = l_Lean_Meta_LibrarySearch_isAbortSpeculation(v_x_1211_);
lean_dec_ref(v_x_1211_);
v_r_1213_ = lean_box(v_res_1212_);
return v_r_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(lean_object* v_x_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Lean_Meta_saveState___redArg(v___y_1216_, v___y_1218_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; lean_object* v___x_1222_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref_known(v___x_1220_, 1);
lean_inc(v___y_1218_);
lean_inc_ref(v___y_1217_);
lean_inc(v___y_1216_);
lean_inc_ref(v___y_1215_);
v___x_1222_ = lean_apply_5(v_x_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, lean_box(0));
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1231_; 
lean_dec(v_a_1221_);
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1225_ = v___x_1222_;
v_isShared_1226_ = v_isSharedCheck_1231_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1222_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1231_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1227_; lean_object* v___x_1229_; 
v___x_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1227_, 0, v_a_1223_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v___x_1227_);
v___x_1229_ = v___x_1225_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1227_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1262_; 
v_a_1232_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1234_ = v___x_1222_;
v_isShared_1235_ = v_isSharedCheck_1262_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1222_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1262_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
uint8_t v___x_1236_; 
v___x_1236_ = l_Lean_Exception_isInterrupt(v_a_1232_);
if (v___x_1236_ == 0)
{
uint8_t v___x_1237_; 
lean_inc(v_a_1232_);
v___x_1237_ = l_Lean_Exception_isRuntime(v_a_1232_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; 
lean_del_object(v___x_1234_);
lean_dec(v_a_1232_);
v___x_1238_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1221_, v___y_1216_, v___y_1218_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1246_; 
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1246_ == 0)
{
lean_object* v_unused_1247_; 
v_unused_1247_ = lean_ctor_get(v___x_1238_, 0);
lean_dec(v_unused_1247_);
v___x_1240_ = v___x_1238_;
v_isShared_1241_ = v_isSharedCheck_1246_;
goto v_resetjp_1239_;
}
else
{
lean_dec(v___x_1238_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1246_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1242_; lean_object* v___x_1244_; 
v___x_1242_ = lean_box(0);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 0, v___x_1242_);
v___x_1244_ = v___x_1240_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1242_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
v_a_1248_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1238_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1238_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
else
{
lean_object* v___x_1257_; 
lean_dec(v_a_1221_);
if (v_isShared_1235_ == 0)
{
v___x_1257_ = v___x_1234_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1232_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
else
{
lean_object* v___x_1260_; 
lean_dec(v_a_1221_);
if (v_isShared_1235_ == 0)
{
v___x_1260_ = v___x_1234_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1232_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
lean_dec_ref(v_x_1214_);
v_a_1263_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1220_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1220_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg___boxed(lean_object* v_x_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v_x_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0(lean_object* v_00_u03b1_1278_, lean_object* v_x_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v_x_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___boxed(lean_object* v_00_u03b1_1286_, lean_object* v_x_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0(v_00_u03b1_1286_, v_x_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(lean_object* v_e_1294_, lean_object* v___y_1295_){
_start:
{
uint8_t v___x_1297_; 
v___x_1297_ = l_Lean_Expr_hasMVar(v_e_1294_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1298_; 
v___x_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1298_, 0, v_e_1294_);
return v___x_1298_;
}
else
{
lean_object* v___x_1299_; lean_object* v_mctx_1300_; lean_object* v___x_1301_; lean_object* v_fst_1302_; lean_object* v_snd_1303_; lean_object* v___x_1304_; lean_object* v_cache_1305_; lean_object* v_zetaDeltaFVarIds_1306_; lean_object* v_postponed_1307_; lean_object* v_diag_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1317_; 
v___x_1299_ = lean_st_ref_get(v___y_1295_);
v_mctx_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc_ref(v_mctx_1300_);
lean_dec(v___x_1299_);
v___x_1301_ = l_Lean_instantiateMVarsCore(v_mctx_1300_, v_e_1294_);
v_fst_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_fst_1302_);
v_snd_1303_ = lean_ctor_get(v___x_1301_, 1);
lean_inc(v_snd_1303_);
lean_dec_ref(v___x_1301_);
v___x_1304_ = lean_st_ref_take(v___y_1295_);
v_cache_1305_ = lean_ctor_get(v___x_1304_, 1);
v_zetaDeltaFVarIds_1306_ = lean_ctor_get(v___x_1304_, 2);
v_postponed_1307_ = lean_ctor_get(v___x_1304_, 3);
v_diag_1308_ = lean_ctor_get(v___x_1304_, 4);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1317_ == 0)
{
lean_object* v_unused_1318_; 
v_unused_1318_ = lean_ctor_get(v___x_1304_, 0);
lean_dec(v_unused_1318_);
v___x_1310_ = v___x_1304_;
v_isShared_1311_ = v_isSharedCheck_1317_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_diag_1308_);
lean_inc(v_postponed_1307_);
lean_inc(v_zetaDeltaFVarIds_1306_);
lean_inc(v_cache_1305_);
lean_dec(v___x_1304_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1317_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v_snd_1303_);
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_snd_1303_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v_cache_1305_);
lean_ctor_set(v_reuseFailAlloc_1316_, 2, v_zetaDeltaFVarIds_1306_);
lean_ctor_set(v_reuseFailAlloc_1316_, 3, v_postponed_1307_);
lean_ctor_set(v_reuseFailAlloc_1316_, 4, v_diag_1308_);
v___x_1313_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_st_ref_put(v___y_1295_, v___x_1313_);
v___x_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1315_, 0, v_fst_1302_);
return v___x_1315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg___boxed(lean_object* v_e_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_e_1319_, v___y_1320_);
lean_dec(v___y_1320_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1(lean_object* v_e_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_e_1323_, v___y_1325_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___boxed(lean_object* v_e_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1(v_e_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0(lean_object* v___x_1337_, lean_object* v_x_1338_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1337_);
lean_ctor_set(v___x_1339_, 1, v_x_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(lean_object* v___x_1340_, size_t v_sz_1341_, size_t v_i_1342_, lean_object* v_bs_1343_){
_start:
{
uint8_t v___x_1344_; 
v___x_1344_ = lean_usize_dec_lt(v_i_1342_, v_sz_1341_);
if (v___x_1344_ == 0)
{
lean_dec_ref(v___x_1340_);
return v_bs_1343_;
}
else
{
lean_object* v_v_1345_; lean_object* v___x_1346_; lean_object* v_bs_x27_1347_; lean_object* v___x_1348_; size_t v___x_1349_; size_t v___x_1350_; lean_object* v___x_1351_; 
v_v_1345_ = lean_array_uget(v_bs_1343_, v_i_1342_);
v___x_1346_ = lean_unsigned_to_nat(0u);
v_bs_x27_1347_ = lean_array_uset(v_bs_1343_, v_i_1342_, v___x_1346_);
lean_inc_ref(v___x_1340_);
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1340_);
lean_ctor_set(v___x_1348_, 1, v_v_1345_);
v___x_1349_ = ((size_t)1ULL);
v___x_1350_ = lean_usize_add(v_i_1342_, v___x_1349_);
v___x_1351_ = lean_array_uset(v_bs_x27_1347_, v_i_1342_, v___x_1348_);
v_i_1342_ = v___x_1350_;
v_bs_1343_ = v___x_1351_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2___boxed(lean_object* v___x_1353_, lean_object* v_sz_1354_, lean_object* v_i_1355_, lean_object* v_bs_1356_){
_start:
{
size_t v_sz_boxed_1357_; size_t v_i_boxed_1358_; lean_object* v_res_1359_; 
v_sz_boxed_1357_ = lean_unbox_usize(v_sz_1354_);
lean_dec(v_sz_1354_);
v_i_boxed_1358_ = lean_unbox_usize(v_i_1355_);
lean_dec(v_i_1355_);
v_res_1359_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(v___x_1353_, v_sz_boxed_1357_, v_i_boxed_1358_, v_bs_1356_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm(lean_object* v_searchFn_1360_, lean_object* v_goal_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v___x_1367_; 
lean_inc(v_goal_1361_);
v___x_1367_ = l_Lean_MVarId_getType(v_goal_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; lean_object* v___x_1369_; 
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_a_1368_);
lean_dec_ref_known(v___x_1367_, 1);
lean_inc_ref(v_searchFn_1360_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_a_1363_);
lean_inc_ref(v_a_1362_);
v___x_1369_ = lean_apply_6(v_searchFn_1360_, v_a_1368_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, lean_box(0));
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v___x_1371_; lean_object* v_mctx_1372_; lean_object* v___x_1373_; lean_object* v___f_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref_known(v___x_1369_, 1);
v___x_1371_ = lean_st_ref_get(v_a_1363_);
v_mctx_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc_ref_n(v_mctx_1372_, 2);
lean_dec(v___x_1371_);
lean_inc(v_goal_1361_);
v___x_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1373_, 0, v_goal_1361_);
lean_ctor_set(v___x_1373_, 1, v_mctx_1372_);
lean_inc_ref(v___x_1373_);
v___f_1374_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0), 2, 1);
lean_closure_set(v___f_1374_, 0, v___x_1373_);
v___x_1375_ = lean_alloc_closure((void*)(l_Lean_MVarId_applySymm___boxed), 6, 1);
lean_closure_set(v___x_1375_, 0, v_goal_1361_);
v___x_1376_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v___x_1375_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1436_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1379_ = v___x_1376_;
v_isShared_1380_ = v_isSharedCheck_1436_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1376_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1436_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
if (lean_obj_tag(v_a_1377_) == 1)
{
lean_object* v_val_1381_; lean_object* v___x_1382_; 
lean_del_object(v___x_1379_);
lean_dec_ref_known(v___x_1373_, 2);
v_val_1381_ = lean_ctor_get(v_a_1377_, 0);
lean_inc_n(v_val_1381_, 2);
lean_dec_ref_known(v_a_1377_, 1);
v___x_1382_ = l_Lean_MVarId_getType(v_val_1381_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1384_; lean_object* v_a_1385_; lean_object* v___x_1386_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1383_);
lean_dec_ref_known(v___x_1382_, 1);
v___x_1384_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_a_1383_, v_a_1363_);
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref(v___x_1384_);
lean_inc(v_a_1365_);
lean_inc_ref(v_a_1364_);
lean_inc(v_a_1363_);
lean_inc_ref(v_a_1362_);
v___x_1386_ = lean_apply_6(v_searchFn_1360_, v_a_1385_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, lean_box(0));
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1413_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1413_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1413_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v_mctx_1392_; lean_object* v___x_1393_; lean_object* v___f_1394_; lean_object* v___x_1395_; lean_object* v_cache_1396_; lean_object* v_zetaDeltaFVarIds_1397_; lean_object* v_postponed_1398_; lean_object* v_diag_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1411_; 
v___x_1391_ = lean_st_ref_get(v_a_1363_);
v_mctx_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc_ref(v_mctx_1392_);
lean_dec(v___x_1391_);
v___x_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1393_, 0, v_val_1381_);
lean_ctor_set(v___x_1393_, 1, v_mctx_1392_);
v___f_1394_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0), 2, 1);
lean_closure_set(v___f_1394_, 0, v___x_1393_);
v___x_1395_ = lean_st_ref_take(v_a_1363_);
v_cache_1396_ = lean_ctor_get(v___x_1395_, 1);
v_zetaDeltaFVarIds_1397_ = lean_ctor_get(v___x_1395_, 2);
v_postponed_1398_ = lean_ctor_get(v___x_1395_, 3);
v_diag_1399_ = lean_ctor_get(v___x_1395_, 4);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; 
v_unused_1412_ = lean_ctor_get(v___x_1395_, 0);
lean_dec(v_unused_1412_);
v___x_1401_ = v___x_1395_;
v_isShared_1402_ = v_isSharedCheck_1411_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_diag_1399_);
lean_inc(v_postponed_1398_);
lean_inc(v_zetaDeltaFVarIds_1397_);
lean_inc(v_cache_1396_);
lean_dec(v___x_1395_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1411_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 0, v_mctx_1372_);
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_mctx_1372_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_cache_1396_);
lean_ctor_set(v_reuseFailAlloc_1410_, 2, v_zetaDeltaFVarIds_1397_);
lean_ctor_set(v_reuseFailAlloc_1410_, 3, v_postponed_1398_);
lean_ctor_set(v_reuseFailAlloc_1410_, 4, v_diag_1399_);
v___x_1404_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1405_ = lean_st_ref_put(v_a_1363_, v___x_1404_);
v___x_1406_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v___f_1374_, v_a_1370_, v___f_1394_, v_a_1387_);
lean_dec(v_a_1387_);
lean_dec(v_a_1370_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1406_);
v___x_1408_ = v___x_1389_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec(v_val_1381_);
lean_dec_ref(v___f_1374_);
lean_dec_ref(v_mctx_1372_);
lean_dec(v_a_1370_);
v_a_1414_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1386_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1386_);
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
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
lean_dec(v_val_1381_);
lean_dec_ref(v___f_1374_);
lean_dec_ref(v_mctx_1372_);
lean_dec(v_a_1370_);
lean_dec_ref(v_searchFn_1360_);
v_a_1422_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1382_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1382_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
else
{
size_t v_sz_1430_; size_t v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1434_; 
lean_dec(v_a_1377_);
lean_dec_ref(v___f_1374_);
lean_dec_ref(v_mctx_1372_);
lean_dec_ref(v_searchFn_1360_);
v_sz_1430_ = lean_array_size(v_a_1370_);
v___x_1431_ = ((size_t)0ULL);
v___x_1432_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(v___x_1373_, v_sz_1430_, v___x_1431_, v_a_1370_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v___x_1432_);
v___x_1434_ = v___x_1379_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec_ref(v___f_1374_);
lean_dec_ref_known(v___x_1373_, 2);
lean_dec_ref(v_mctx_1372_);
lean_dec(v_a_1370_);
lean_dec_ref(v_searchFn_1360_);
v_a_1437_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1376_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1376_);
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
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
lean_dec(v_goal_1361_);
lean_dec_ref(v_searchFn_1360_);
v_a_1445_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1369_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1369_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
else
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
lean_dec(v_goal_1361_);
lean_dec_ref(v_searchFn_1360_);
v_a_1453_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1367_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1367_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1453_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm___boxed(lean_object* v_searchFn_1461_, lean_object* v_goal_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v_searchFn_1461_, v_goal_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0(lean_object* v_e_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1479_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__1));
v___x_1480_ = lean_unsigned_to_nat(1u);
v___x_1481_ = lean_mk_empty_array_with_capacity(v___x_1480_);
v___x_1482_ = lean_array_push(v___x_1481_, v_e_1473_);
v___x_1483_ = l_Lean_Meta_mkAppM(v___x_1479_, v___x_1482_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___boxed(lean_object* v_e_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0(v_e_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1(lean_object* v_e_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1501_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__1));
v___x_1502_ = lean_unsigned_to_nat(1u);
v___x_1503_ = lean_mk_empty_array_with_capacity(v___x_1502_);
v___x_1504_ = lean_array_push(v___x_1503_, v_e_1495_);
v___x_1505_ = l_Lean_Meta_mkAppM(v___x_1501_, v___x_1504_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___boxed(lean_object* v_e_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1(v_e_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(lean_object* v_lem_1515_, uint8_t v_mod_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v___f_1522_; lean_object* v___f_1523_; lean_object* v___x_1524_; 
v___f_1522_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__0));
v___f_1523_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__1));
v___x_1524_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_lem_1515_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1524_) == 0)
{
switch(v_mod_1516_)
{
case 0:
{
return v___x_1524_;
}
case 1:
{
lean_object* v_a_1525_; lean_object* v___x_1526_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v___x_1524_, 1);
v___x_1526_ = l_Lean_Meta_mapForallTelescope(v___f_1522_, v_a_1525_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
return v___x_1526_;
}
default: 
{
lean_object* v_a_1527_; lean_object* v___x_1528_; 
v_a_1527_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1524_, 1);
v___x_1528_ = l_Lean_Meta_mapForallTelescope(v___f_1523_, v_a_1527_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
return v___x_1528_;
}
}
}
else
{
return v___x_1524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___boxed(lean_object* v_lem_1529_, lean_object* v_mod_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_){
_start:
{
uint8_t v_mod_boxed_1536_; lean_object* v_res_1537_; 
v_mod_boxed_1536_ = lean_unbox(v_mod_1530_);
v_res_1537_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_lem_1529_, v_mod_boxed_1536_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
lean_dec(v_a_1534_);
lean_dec_ref(v_a_1533_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
return v_res_1537_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar(lean_object* v_e_1538_){
_start:
{
switch(lean_obj_tag(v_e_1538_))
{
case 0:
{
uint8_t v___x_1539_; 
v___x_1539_ = 1;
return v___x_1539_;
}
case 1:
{
uint8_t v___x_1540_; 
v___x_1540_ = 1;
return v___x_1540_;
}
case 2:
{
uint8_t v___x_1541_; 
v___x_1541_ = 1;
return v___x_1541_;
}
default: 
{
uint8_t v___x_1542_; 
v___x_1542_ = 0;
return v___x_1542_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar___boxed(lean_object* v_e_1543_){
_start:
{
uint8_t v_res_1544_; lean_object* v_r_1545_; 
v_res_1544_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar(v_e_1543_);
lean_dec_ref(v_e_1543_);
v_r_1545_ = lean_box(v_res_1544_);
return v_r_1545_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1546_ = lean_unsigned_to_nat(32u);
v___x_1547_ = lean_mk_empty_array_with_capacity(v___x_1546_);
v___x_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1547_);
return v___x_1548_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1549_ = ((size_t)5ULL);
v___x_1550_ = lean_unsigned_to_nat(0u);
v___x_1551_ = lean_unsigned_to_nat(32u);
v___x_1552_ = lean_mk_empty_array_with_capacity(v___x_1551_);
v___x_1553_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0);
v___x_1554_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
lean_ctor_set(v___x_1554_, 1, v___x_1552_);
lean_ctor_set(v___x_1554_, 2, v___x_1550_);
lean_ctor_set(v___x_1554_, 3, v___x_1550_);
lean_ctor_set_usize(v___x_1554_, 4, v___x_1549_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(lean_object* v___y_1555_){
_start:
{
lean_object* v___x_1557_; lean_object* v_traceState_1558_; lean_object* v_traces_1559_; lean_object* v___x_1560_; lean_object* v_traceState_1561_; lean_object* v_env_1562_; lean_object* v_nextMacroScope_1563_; lean_object* v_ngen_1564_; lean_object* v_auxDeclNGen_1565_; lean_object* v_cache_1566_; lean_object* v_recordedDeps_1567_; lean_object* v_messages_1568_; lean_object* v_infoState_1569_; lean_object* v_snapshotTasks_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1589_; 
v___x_1557_ = lean_st_ref_get(v___y_1555_);
v_traceState_1558_ = lean_ctor_get(v___x_1557_, 4);
lean_inc_ref(v_traceState_1558_);
lean_dec(v___x_1557_);
v_traces_1559_ = lean_ctor_get(v_traceState_1558_, 0);
lean_inc_ref(v_traces_1559_);
lean_dec_ref(v_traceState_1558_);
v___x_1560_ = lean_st_ref_take(v___y_1555_);
v_traceState_1561_ = lean_ctor_get(v___x_1560_, 4);
v_env_1562_ = lean_ctor_get(v___x_1560_, 0);
v_nextMacroScope_1563_ = lean_ctor_get(v___x_1560_, 1);
v_ngen_1564_ = lean_ctor_get(v___x_1560_, 2);
v_auxDeclNGen_1565_ = lean_ctor_get(v___x_1560_, 3);
v_cache_1566_ = lean_ctor_get(v___x_1560_, 5);
v_recordedDeps_1567_ = lean_ctor_get(v___x_1560_, 6);
v_messages_1568_ = lean_ctor_get(v___x_1560_, 7);
v_infoState_1569_ = lean_ctor_get(v___x_1560_, 8);
v_snapshotTasks_1570_ = lean_ctor_get(v___x_1560_, 9);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1572_ = v___x_1560_;
v_isShared_1573_ = v_isSharedCheck_1589_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_snapshotTasks_1570_);
lean_inc(v_infoState_1569_);
lean_inc(v_messages_1568_);
lean_inc(v_recordedDeps_1567_);
lean_inc(v_cache_1566_);
lean_inc(v_traceState_1561_);
lean_inc(v_auxDeclNGen_1565_);
lean_inc(v_ngen_1564_);
lean_inc(v_nextMacroScope_1563_);
lean_inc(v_env_1562_);
lean_dec(v___x_1560_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1589_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
uint64_t v_tid_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1587_; 
v_tid_1574_ = lean_ctor_get_uint64(v_traceState_1561_, sizeof(void*)*1);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_traceState_1561_);
if (v_isSharedCheck_1587_ == 0)
{
lean_object* v_unused_1588_; 
v_unused_1588_ = lean_ctor_get(v_traceState_1561_, 0);
lean_dec(v_unused_1588_);
v___x_1576_ = v_traceState_1561_;
v_isShared_1577_ = v_isSharedCheck_1587_;
goto v_resetjp_1575_;
}
else
{
lean_dec(v_traceState_1561_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1587_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1578_; lean_object* v___x_1580_; 
v___x_1578_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v___x_1578_);
v___x_1580_ = v___x_1576_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1578_);
lean_ctor_set_uint64(v_reuseFailAlloc_1586_, sizeof(void*)*1, v_tid_1574_);
v___x_1580_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_object* v___x_1582_; 
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 4, v___x_1580_);
v___x_1582_ = v___x_1572_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_env_1562_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_nextMacroScope_1563_);
lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_ngen_1564_);
lean_ctor_set(v_reuseFailAlloc_1585_, 3, v_auxDeclNGen_1565_);
lean_ctor_set(v_reuseFailAlloc_1585_, 4, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1585_, 5, v_cache_1566_);
lean_ctor_set(v_reuseFailAlloc_1585_, 6, v_recordedDeps_1567_);
lean_ctor_set(v_reuseFailAlloc_1585_, 7, v_messages_1568_);
lean_ctor_set(v_reuseFailAlloc_1585_, 8, v_infoState_1569_);
lean_ctor_set(v_reuseFailAlloc_1585_, 9, v_snapshotTasks_1570_);
v___x_1582_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = lean_st_ref_put(v___y_1555_, v___x_1582_);
v___x_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1584_, 0, v_traces_1559_);
return v___x_1584_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___boxed(lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v___y_1590_);
lean_dec(v___y_1590_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0(lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v___y_1596_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___boxed(lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0(v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
return v_res_1604_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(lean_object* v_opts_1605_, lean_object* v_opt_1606_){
_start:
{
lean_object* v_name_1607_; lean_object* v_defValue_1608_; lean_object* v_map_1609_; lean_object* v___x_1610_; 
v_name_1607_ = lean_ctor_get(v_opt_1606_, 0);
v_defValue_1608_ = lean_ctor_get(v_opt_1606_, 1);
v_map_1609_ = lean_ctor_get(v_opts_1605_, 0);
v___x_1610_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1609_, v_name_1607_);
if (lean_obj_tag(v___x_1610_) == 0)
{
uint8_t v___x_1611_; 
v___x_1611_ = lean_unbox(v_defValue_1608_);
return v___x_1611_;
}
else
{
lean_object* v_val_1612_; 
v_val_1612_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_val_1612_);
lean_dec_ref_known(v___x_1610_, 1);
if (lean_obj_tag(v_val_1612_) == 1)
{
uint8_t v_v_1613_; 
v_v_1613_ = lean_ctor_get_uint8(v_val_1612_, 0);
lean_dec_ref_known(v_val_1612_, 0);
return v_v_1613_;
}
else
{
uint8_t v___x_1614_; 
lean_dec(v_val_1612_);
v___x_1614_ = lean_unbox(v_defValue_1608_);
return v___x_1614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___boxed(lean_object* v_opts_1615_, lean_object* v_opt_1616_){
_start:
{
uint8_t v_res_1617_; lean_object* v_r_1618_; 
v_res_1617_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1615_, v_opt_1616_);
lean_dec_ref(v_opt_1616_);
lean_dec_ref(v_opts_1615_);
v_r_1618_ = lean_box(v_res_1617_);
return v_r_1618_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__0));
v___x_1621_ = l_Lean_stringToMessageData(v___x_1620_);
return v___x_1621_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__2));
v___x_1624_ = l_Lean_stringToMessageData(v___x_1623_);
return v___x_1624_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__5));
v___x_1629_ = l_Lean_MessageData_ofFormat(v___x_1628_);
return v___x_1629_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__8));
v___x_1634_ = l_Lean_MessageData_ofFormat(v___x_1633_);
return v___x_1634_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12(void){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__11));
v___x_1639_ = l_Lean_MessageData_ofFormat(v___x_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0(lean_object* v_fst_1640_, uint8_t v_snd_1641_, lean_object* v_x_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___y_1652_; 
v___x_1648_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1);
v___x_1649_ = l_Lean_MessageData_ofName(v_fst_1640_);
v___x_1650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1648_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
switch(v_snd_1641_)
{
case 0:
{
lean_object* v___x_1657_; 
v___x_1657_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6);
v___y_1652_ = v___x_1657_;
goto v___jp_1651_;
}
case 1:
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9);
v___y_1652_ = v___x_1658_;
goto v___jp_1651_;
}
default: 
{
lean_object* v___x_1659_; 
v___x_1659_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12);
v___y_1652_ = v___x_1659_;
goto v___jp_1651_;
}
}
v___jp_1651_:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
lean_inc_ref(v___y_1652_);
v___x_1653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1650_);
lean_ctor_set(v___x_1653_, 1, v___y_1652_);
v___x_1654_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3);
v___x_1655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1653_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
return v___x_1656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___boxed(lean_object* v_fst_1660_, lean_object* v_snd_1661_, lean_object* v_x_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
uint8_t v_snd_11046__boxed_1668_; lean_object* v_res_1669_; 
v_snd_11046__boxed_1668_ = lean_unbox(v_snd_1661_);
v_res_1669_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0(v_fst_1660_, v_snd_11046__boxed_1668_, v_x_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec_ref(v_x_1662_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(lean_object* v_opts_1670_, lean_object* v_opt_1671_){
_start:
{
lean_object* v_name_1672_; lean_object* v_defValue_1673_; lean_object* v_map_1674_; lean_object* v___x_1675_; 
v_name_1672_ = lean_ctor_get(v_opt_1671_, 0);
v_defValue_1673_ = lean_ctor_get(v_opt_1671_, 1);
v_map_1674_ = lean_ctor_get(v_opts_1670_, 0);
v___x_1675_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1674_, v_name_1672_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_inc(v_defValue_1673_);
return v_defValue_1673_;
}
else
{
lean_object* v_val_1676_; 
v_val_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_val_1676_);
lean_dec_ref_known(v___x_1675_, 1);
if (lean_obj_tag(v_val_1676_) == 3)
{
lean_object* v_v_1677_; 
v_v_1677_ = lean_ctor_get(v_val_1676_, 0);
lean_inc(v_v_1677_);
lean_dec_ref_known(v_val_1676_, 1);
return v_v_1677_;
}
else
{
lean_dec(v_val_1676_);
lean_inc(v_defValue_1673_);
return v_defValue_1673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5___boxed(lean_object* v_opts_1678_, lean_object* v_opt_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1678_, v_opt_1679_);
lean_dec_ref(v_opt_1679_);
lean_dec_ref(v_opts_1678_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(lean_object* v_x_1681_){
_start:
{
if (lean_obj_tag(v_x_1681_) == 0)
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
v_a_1683_ = lean_ctor_get(v_x_1681_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_x_1681_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v_x_1681_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v_x_1681_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
lean_ctor_set_tag(v___x_1685_, 1);
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
v_a_1691_ = lean_ctor_get(v_x_1681_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_x_1681_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v_x_1681_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v_x_1681_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
lean_ctor_set_tag(v___x_1693_, 0);
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg___boxed(lean_object* v_x_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_x_1699_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(size_t v_sz_1702_, size_t v_i_1703_, lean_object* v_bs_1704_){
_start:
{
uint8_t v___x_1705_; 
v___x_1705_ = lean_usize_dec_lt(v_i_1703_, v_sz_1702_);
if (v___x_1705_ == 0)
{
return v_bs_1704_;
}
else
{
lean_object* v_v_1706_; lean_object* v_msg_1707_; lean_object* v___x_1708_; lean_object* v_bs_x27_1709_; size_t v___x_1710_; size_t v___x_1711_; lean_object* v___x_1712_; 
v_v_1706_ = lean_array_uget_borrowed(v_bs_1704_, v_i_1703_);
v_msg_1707_ = lean_ctor_get(v_v_1706_, 1);
lean_inc_ref(v_msg_1707_);
v___x_1708_ = lean_unsigned_to_nat(0u);
v_bs_x27_1709_ = lean_array_uset(v_bs_1704_, v_i_1703_, v___x_1708_);
v___x_1710_ = ((size_t)1ULL);
v___x_1711_ = lean_usize_add(v_i_1703_, v___x_1710_);
v___x_1712_ = lean_array_uset(v_bs_x27_1709_, v_i_1703_, v_msg_1707_);
v_i_1703_ = v___x_1711_;
v_bs_1704_ = v___x_1712_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1714_, lean_object* v_i_1715_, lean_object* v_bs_1716_){
_start:
{
size_t v_sz_boxed_1717_; size_t v_i_boxed_1718_; lean_object* v_res_1719_; 
v_sz_boxed_1717_ = lean_unbox_usize(v_sz_1714_);
lean_dec(v_sz_1714_);
v_i_boxed_1718_ = lean_unbox_usize(v_i_1715_);
lean_dec(v_i_1715_);
v_res_1719_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(v_sz_boxed_1717_, v_i_boxed_1718_, v_bs_1716_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(lean_object* v_oldTraces_1720_, lean_object* v_data_1721_, lean_object* v_ref_1722_, lean_object* v_msg_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v_toCold_1729_; lean_object* v_currRecDepth_1730_; lean_object* v_ref_1731_; uint16_t v_optionFlags_1732_; uint8_t v_suppressElabErrors_1733_; uint8_t v_isRecordingDeps_1734_; lean_object* v_ref_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v_traceState_1738_; lean_object* v_traces_1739_; lean_object* v___x_1740_; size_t v_sz_1741_; size_t v___x_1742_; lean_object* v___x_1743_; lean_object* v_msg_1744_; lean_object* v___x_1745_; lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1784_; 
v_toCold_1729_ = lean_ctor_get(v___y_1726_, 0);
v_currRecDepth_1730_ = lean_ctor_get(v___y_1726_, 1);
v_ref_1731_ = lean_ctor_get(v___y_1726_, 2);
v_optionFlags_1732_ = lean_ctor_get_uint16(v___y_1726_, sizeof(void*)*3);
v_suppressElabErrors_1733_ = lean_ctor_get_uint8(v___y_1726_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1734_ = lean_ctor_get_uint8(v___y_1726_, sizeof(void*)*3 + 3);
v_ref_1735_ = l_Lean_replaceRef(v_ref_1722_, v_ref_1731_);
lean_inc(v_currRecDepth_1730_);
lean_inc_ref(v_toCold_1729_);
v___x_1736_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1736_, 0, v_toCold_1729_);
lean_ctor_set(v___x_1736_, 1, v_currRecDepth_1730_);
lean_ctor_set(v___x_1736_, 2, v_ref_1735_);
lean_ctor_set_uint16(v___x_1736_, sizeof(void*)*3, v_optionFlags_1732_);
lean_ctor_set_uint8(v___x_1736_, sizeof(void*)*3 + 2, v_suppressElabErrors_1733_);
lean_ctor_set_uint8(v___x_1736_, sizeof(void*)*3 + 3, v_isRecordingDeps_1734_);
v___x_1737_ = lean_st_ref_get(v___y_1727_);
v_traceState_1738_ = lean_ctor_get(v___x_1737_, 4);
lean_inc_ref(v_traceState_1738_);
lean_dec(v___x_1737_);
v_traces_1739_ = lean_ctor_get(v_traceState_1738_, 0);
lean_inc_ref(v_traces_1739_);
lean_dec_ref(v_traceState_1738_);
v___x_1740_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1739_);
lean_dec_ref(v_traces_1739_);
v_sz_1741_ = lean_array_size(v___x_1740_);
v___x_1742_ = ((size_t)0ULL);
v___x_1743_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(v_sz_1741_, v___x_1742_, v___x_1740_);
v_msg_1744_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1744_, 0, v_data_1721_);
lean_ctor_set(v_msg_1744_, 1, v_msg_1723_);
lean_ctor_set(v_msg_1744_, 2, v___x_1743_);
v___x_1745_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msg_1744_, v___y_1724_, v___y_1725_, v___x_1736_, v___y_1727_);
lean_dec_ref_known(v___x_1736_, 3);
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1748_ = v___x_1745_;
v_isShared_1749_ = v_isSharedCheck_1784_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1745_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1784_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; lean_object* v_traceState_1751_; lean_object* v_env_1752_; lean_object* v_nextMacroScope_1753_; lean_object* v_ngen_1754_; lean_object* v_auxDeclNGen_1755_; lean_object* v_cache_1756_; lean_object* v_recordedDeps_1757_; lean_object* v_messages_1758_; lean_object* v_infoState_1759_; lean_object* v_snapshotTasks_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1783_; 
v___x_1750_ = lean_st_ref_take(v___y_1727_);
v_traceState_1751_ = lean_ctor_get(v___x_1750_, 4);
v_env_1752_ = lean_ctor_get(v___x_1750_, 0);
v_nextMacroScope_1753_ = lean_ctor_get(v___x_1750_, 1);
v_ngen_1754_ = lean_ctor_get(v___x_1750_, 2);
v_auxDeclNGen_1755_ = lean_ctor_get(v___x_1750_, 3);
v_cache_1756_ = lean_ctor_get(v___x_1750_, 5);
v_recordedDeps_1757_ = lean_ctor_get(v___x_1750_, 6);
v_messages_1758_ = lean_ctor_get(v___x_1750_, 7);
v_infoState_1759_ = lean_ctor_get(v___x_1750_, 8);
v_snapshotTasks_1760_ = lean_ctor_get(v___x_1750_, 9);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1762_ = v___x_1750_;
v_isShared_1763_ = v_isSharedCheck_1783_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_snapshotTasks_1760_);
lean_inc(v_infoState_1759_);
lean_inc(v_messages_1758_);
lean_inc(v_recordedDeps_1757_);
lean_inc(v_cache_1756_);
lean_inc(v_traceState_1751_);
lean_inc(v_auxDeclNGen_1755_);
lean_inc(v_ngen_1754_);
lean_inc(v_nextMacroScope_1753_);
lean_inc(v_env_1752_);
lean_dec(v___x_1750_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1783_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
uint64_t v_tid_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1781_; 
v_tid_1764_ = lean_ctor_get_uint64(v_traceState_1751_, sizeof(void*)*1);
v_isSharedCheck_1781_ = !lean_is_exclusive(v_traceState_1751_);
if (v_isSharedCheck_1781_ == 0)
{
lean_object* v_unused_1782_; 
v_unused_1782_ = lean_ctor_get(v_traceState_1751_, 0);
lean_dec(v_unused_1782_);
v___x_1766_ = v_traceState_1751_;
v_isShared_1767_ = v_isSharedCheck_1781_;
goto v_resetjp_1765_;
}
else
{
lean_dec(v_traceState_1751_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1781_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1772_; 
v___x_1768_ = lean_box(0);
v___x_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1769_, 0, v_ref_1722_);
lean_ctor_set(v___x_1769_, 1, v_a_1746_);
v___x_1770_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1720_, v___x_1769_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 0, v___x_1770_);
v___x_1772_ = v___x_1766_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1770_);
lean_ctor_set_uint64(v_reuseFailAlloc_1780_, sizeof(void*)*1, v_tid_1764_);
v___x_1772_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1774_; 
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 4, v___x_1772_);
v___x_1774_ = v___x_1762_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_env_1752_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_nextMacroScope_1753_);
lean_ctor_set(v_reuseFailAlloc_1779_, 2, v_ngen_1754_);
lean_ctor_set(v_reuseFailAlloc_1779_, 3, v_auxDeclNGen_1755_);
lean_ctor_set(v_reuseFailAlloc_1779_, 4, v___x_1772_);
lean_ctor_set(v_reuseFailAlloc_1779_, 5, v_cache_1756_);
lean_ctor_set(v_reuseFailAlloc_1779_, 6, v_recordedDeps_1757_);
lean_ctor_set(v_reuseFailAlloc_1779_, 7, v_messages_1758_);
lean_ctor_set(v_reuseFailAlloc_1779_, 8, v_infoState_1759_);
lean_ctor_set(v_reuseFailAlloc_1779_, 9, v_snapshotTasks_1760_);
v___x_1774_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1775_; lean_object* v___x_1777_; 
v___x_1775_ = lean_st_ref_put(v___y_1727_, v___x_1774_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 0, v___x_1768_);
v___x_1777_ = v___x_1748_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1768_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2___boxed(lean_object* v_oldTraces_1785_, lean_object* v_data_1786_, lean_object* v_ref_1787_, lean_object* v_msg_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_1785_, v_data_1786_, v_ref_1787_, v_msg_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
return v_res_1794_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(lean_object* v_e_1795_){
_start:
{
if (lean_obj_tag(v_e_1795_) == 0)
{
uint8_t v___x_1796_; 
v___x_1796_ = 2;
return v___x_1796_;
}
else
{
uint8_t v___x_1797_; 
v___x_1797_ = 0;
return v___x_1797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___boxed(lean_object* v_e_1798_){
_start:
{
uint8_t v_res_1799_; lean_object* v_r_1800_; 
v_res_1799_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(v_e_1798_);
lean_dec_ref(v_e_1798_);
v_r_1800_ = lean_box(v_res_1799_);
return v_r_1800_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1801_; double v___x_1802_; 
v___x_1801_ = lean_unsigned_to_nat(0u);
v___x_1802_ = lean_float_of_nat(v___x_1801_);
return v___x_1802_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1804_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__1));
v___x_1805_ = l_Lean_stringToMessageData(v___x_1804_);
return v___x_1805_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1806_; double v___x_1807_; 
v___x_1806_ = lean_unsigned_to_nat(1000u);
v___x_1807_ = lean_float_of_nat(v___x_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(lean_object* v_cls_1808_, uint8_t v_collapsed_1809_, lean_object* v_tag_1810_, lean_object* v_opts_1811_, uint8_t v_clsEnabled_1812_, lean_object* v_oldTraces_1813_, lean_object* v_msg_1814_, lean_object* v_resStartStop_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v_fst_1821_; lean_object* v_snd_1822_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v_data_1826_; lean_object* v_fst_1837_; lean_object* v_snd_1838_; lean_object* v___x_1839_; uint8_t v___x_1840_; lean_object* v___y_1842_; lean_object* v_a_1843_; uint8_t v___y_1858_; double v___y_1890_; 
v_fst_1821_ = lean_ctor_get(v_resStartStop_1815_, 0);
lean_inc(v_fst_1821_);
v_snd_1822_ = lean_ctor_get(v_resStartStop_1815_, 1);
lean_inc(v_snd_1822_);
lean_dec_ref(v_resStartStop_1815_);
v_fst_1837_ = lean_ctor_get(v_snd_1822_, 0);
lean_inc(v_fst_1837_);
v_snd_1838_ = lean_ctor_get(v_snd_1822_, 1);
lean_inc(v_snd_1838_);
lean_dec(v_snd_1822_);
v___x_1839_ = l_Lean_trace_profiler;
v___x_1840_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1811_, v___x_1839_);
if (v___x_1840_ == 0)
{
v___y_1858_ = v___x_1840_;
goto v___jp_1857_;
}
else
{
lean_object* v___x_1895_; uint8_t v___x_1896_; 
v___x_1895_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1896_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1811_, v___x_1895_);
if (v___x_1896_ == 0)
{
lean_object* v___x_1897_; lean_object* v___x_1898_; double v___x_1899_; double v___x_1900_; double v___x_1901_; 
v___x_1897_ = l_Lean_trace_profiler_threshold;
v___x_1898_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1811_, v___x_1897_);
v___x_1899_ = lean_float_of_nat(v___x_1898_);
v___x_1900_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3);
v___x_1901_ = lean_float_div(v___x_1899_, v___x_1900_);
v___y_1890_ = v___x_1901_;
goto v___jp_1889_;
}
else
{
lean_object* v___x_1902_; lean_object* v___x_1903_; double v___x_1904_; 
v___x_1902_ = l_Lean_trace_profiler_threshold;
v___x_1903_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1811_, v___x_1902_);
v___x_1904_ = lean_float_of_nat(v___x_1903_);
v___y_1890_ = v___x_1904_;
goto v___jp_1889_;
}
}
v___jp_1823_:
{
lean_object* v___x_1827_; 
lean_inc(v___y_1825_);
v___x_1827_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_1813_, v_data_1826_, v___y_1825_, v___y_1824_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v___x_1828_; 
lean_dec_ref_known(v___x_1827_, 1);
v___x_1828_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_1821_);
return v___x_1828_;
}
else
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
lean_dec(v_fst_1821_);
v_a_1829_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___x_1827_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1827_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
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
v___jp_1841_:
{
uint8_t v_result_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; double v___x_1847_; lean_object* v_data_1848_; 
v_result_1844_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(v_fst_1821_);
v___x_1845_ = lean_box(v_result_1844_);
v___x_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
v___x_1847_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0);
lean_inc_ref(v_tag_1810_);
lean_inc_ref(v___x_1846_);
lean_inc(v_cls_1808_);
v_data_1848_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1848_, 0, v_cls_1808_);
lean_ctor_set(v_data_1848_, 1, v___x_1846_);
lean_ctor_set(v_data_1848_, 2, v_tag_1810_);
lean_ctor_set_float(v_data_1848_, sizeof(void*)*3, v___x_1847_);
lean_ctor_set_float(v_data_1848_, sizeof(void*)*3 + 8, v___x_1847_);
lean_ctor_set_uint8(v_data_1848_, sizeof(void*)*3 + 16, v_collapsed_1809_);
if (v___x_1840_ == 0)
{
lean_dec_ref_known(v___x_1846_, 1);
lean_dec(v_snd_1838_);
lean_dec(v_fst_1837_);
lean_dec_ref(v_tag_1810_);
lean_dec(v_cls_1808_);
v___y_1824_ = v_a_1843_;
v___y_1825_ = v___y_1842_;
v_data_1826_ = v_data_1848_;
goto v___jp_1823_;
}
else
{
lean_object* v_data_1849_; double v___x_1850_; double v___x_1851_; 
lean_dec_ref_known(v_data_1848_, 3);
v_data_1849_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1849_, 0, v_cls_1808_);
lean_ctor_set(v_data_1849_, 1, v___x_1846_);
lean_ctor_set(v_data_1849_, 2, v_tag_1810_);
v___x_1850_ = lean_unbox_float(v_fst_1837_);
lean_dec(v_fst_1837_);
lean_ctor_set_float(v_data_1849_, sizeof(void*)*3, v___x_1850_);
v___x_1851_ = lean_unbox_float(v_snd_1838_);
lean_dec(v_snd_1838_);
lean_ctor_set_float(v_data_1849_, sizeof(void*)*3 + 8, v___x_1851_);
lean_ctor_set_uint8(v_data_1849_, sizeof(void*)*3 + 16, v_collapsed_1809_);
v___y_1824_ = v_a_1843_;
v___y_1825_ = v___y_1842_;
v_data_1826_ = v_data_1849_;
goto v___jp_1823_;
}
}
v___jp_1852_:
{
lean_object* v_ref_1853_; lean_object* v___x_1854_; 
v_ref_1853_ = lean_ctor_get(v___y_1818_, 2);
lean_inc(v___y_1819_);
lean_inc_ref(v___y_1818_);
lean_inc(v___y_1817_);
lean_inc_ref(v___y_1816_);
lean_inc(v_fst_1821_);
v___x_1854_ = lean_apply_6(v_msg_1814_, v_fst_1821_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, lean_box(0));
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_a_1855_);
lean_dec_ref_known(v___x_1854_, 1);
v___y_1842_ = v_ref_1853_;
v_a_1843_ = v_a_1855_;
goto v___jp_1841_;
}
else
{
lean_object* v___x_1856_; 
lean_dec_ref_known(v___x_1854_, 1);
v___x_1856_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2);
v___y_1842_ = v_ref_1853_;
v_a_1843_ = v___x_1856_;
goto v___jp_1841_;
}
}
v___jp_1857_:
{
if (v_clsEnabled_1812_ == 0)
{
if (v___y_1858_ == 0)
{
lean_object* v___x_1859_; lean_object* v_traceState_1860_; lean_object* v_env_1861_; lean_object* v_nextMacroScope_1862_; lean_object* v_ngen_1863_; lean_object* v_auxDeclNGen_1864_; lean_object* v_cache_1865_; lean_object* v_recordedDeps_1866_; lean_object* v_messages_1867_; lean_object* v_infoState_1868_; lean_object* v_snapshotTasks_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1888_; 
lean_dec(v_snd_1838_);
lean_dec(v_fst_1837_);
lean_dec_ref(v_msg_1814_);
lean_dec_ref(v_tag_1810_);
lean_dec(v_cls_1808_);
v___x_1859_ = lean_st_ref_take(v___y_1819_);
v_traceState_1860_ = lean_ctor_get(v___x_1859_, 4);
v_env_1861_ = lean_ctor_get(v___x_1859_, 0);
v_nextMacroScope_1862_ = lean_ctor_get(v___x_1859_, 1);
v_ngen_1863_ = lean_ctor_get(v___x_1859_, 2);
v_auxDeclNGen_1864_ = lean_ctor_get(v___x_1859_, 3);
v_cache_1865_ = lean_ctor_get(v___x_1859_, 5);
v_recordedDeps_1866_ = lean_ctor_get(v___x_1859_, 6);
v_messages_1867_ = lean_ctor_get(v___x_1859_, 7);
v_infoState_1868_ = lean_ctor_get(v___x_1859_, 8);
v_snapshotTasks_1869_ = lean_ctor_get(v___x_1859_, 9);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1871_ = v___x_1859_;
v_isShared_1872_ = v_isSharedCheck_1888_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_snapshotTasks_1869_);
lean_inc(v_infoState_1868_);
lean_inc(v_messages_1867_);
lean_inc(v_recordedDeps_1866_);
lean_inc(v_cache_1865_);
lean_inc(v_traceState_1860_);
lean_inc(v_auxDeclNGen_1864_);
lean_inc(v_ngen_1863_);
lean_inc(v_nextMacroScope_1862_);
lean_inc(v_env_1861_);
lean_dec(v___x_1859_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1888_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
uint64_t v_tid_1873_; lean_object* v_traces_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1887_; 
v_tid_1873_ = lean_ctor_get_uint64(v_traceState_1860_, sizeof(void*)*1);
v_traces_1874_ = lean_ctor_get(v_traceState_1860_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v_traceState_1860_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1876_ = v_traceState_1860_;
v_isShared_1877_ = v_isSharedCheck_1887_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_traces_1874_);
lean_dec(v_traceState_1860_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1887_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1878_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1813_, v_traces_1874_);
lean_dec_ref(v_traces_1874_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1878_);
v___x_1880_ = v___x_1876_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1878_);
lean_ctor_set_uint64(v_reuseFailAlloc_1886_, sizeof(void*)*1, v_tid_1873_);
v___x_1880_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1882_; 
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 4, v___x_1880_);
v___x_1882_ = v___x_1871_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_env_1861_);
lean_ctor_set(v_reuseFailAlloc_1885_, 1, v_nextMacroScope_1862_);
lean_ctor_set(v_reuseFailAlloc_1885_, 2, v_ngen_1863_);
lean_ctor_set(v_reuseFailAlloc_1885_, 3, v_auxDeclNGen_1864_);
lean_ctor_set(v_reuseFailAlloc_1885_, 4, v___x_1880_);
lean_ctor_set(v_reuseFailAlloc_1885_, 5, v_cache_1865_);
lean_ctor_set(v_reuseFailAlloc_1885_, 6, v_recordedDeps_1866_);
lean_ctor_set(v_reuseFailAlloc_1885_, 7, v_messages_1867_);
lean_ctor_set(v_reuseFailAlloc_1885_, 8, v_infoState_1868_);
lean_ctor_set(v_reuseFailAlloc_1885_, 9, v_snapshotTasks_1869_);
v___x_1882_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = lean_st_ref_put(v___y_1819_, v___x_1882_);
v___x_1884_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_1821_);
return v___x_1884_;
}
}
}
}
}
else
{
goto v___jp_1852_;
}
}
else
{
goto v___jp_1852_;
}
}
v___jp_1889_:
{
double v___x_1891_; double v___x_1892_; double v___x_1893_; uint8_t v___x_1894_; 
v___x_1891_ = lean_unbox_float(v_snd_1838_);
v___x_1892_ = lean_unbox_float(v_fst_1837_);
v___x_1893_ = lean_float_sub(v___x_1891_, v___x_1892_);
v___x_1894_ = lean_float_decLt(v___y_1890_, v___x_1893_);
v___y_1858_ = v___x_1894_;
goto v___jp_1857_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___boxed(lean_object* v_cls_1905_, lean_object* v_collapsed_1906_, lean_object* v_tag_1907_, lean_object* v_opts_1908_, lean_object* v_clsEnabled_1909_, lean_object* v_oldTraces_1910_, lean_object* v_msg_1911_, lean_object* v_resStartStop_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
uint8_t v_collapsed_boxed_1918_; uint8_t v_clsEnabled_boxed_1919_; lean_object* v_res_1920_; 
v_collapsed_boxed_1918_ = lean_unbox(v_collapsed_1906_);
v_clsEnabled_boxed_1919_ = lean_unbox(v_clsEnabled_1909_);
v_res_1920_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v_cls_1905_, v_collapsed_boxed_1918_, v_tag_1907_, v_opts_1908_, v_clsEnabled_boxed_1919_, v_oldTraces_1910_, v_msg_1911_, v_resStartStop_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec_ref(v_opts_1908_);
return v_res_1920_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2(void){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1924_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_1925_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__1));
v___x_1926_ = l_Lean_Name_append(v___x_1925_, v___x_1924_);
return v___x_1926_;
}
}
static double _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3(void){
_start:
{
lean_object* v___x_1927_; double v___x_1928_; 
v___x_1927_ = lean_unsigned_to_nat(1000000000u);
v___x_1928_ = lean_float_of_nat(v___x_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(lean_object* v_cfg_1929_, lean_object* v_act_1930_, lean_object* v_allowFailure_1931_, lean_object* v_cand_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v_fst_1938_; lean_object* v_snd_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_2202_; 
v_fst_1938_ = lean_ctor_get(v_cand_1932_, 0);
v_snd_1939_ = lean_ctor_get(v_cand_1932_, 1);
v_isSharedCheck_2202_ = !lean_is_exclusive(v_cand_1932_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_1941_ = v_cand_1932_;
v_isShared_1942_ = v_isSharedCheck_2202_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_snd_1939_);
lean_inc(v_fst_1938_);
lean_dec(v_cand_1932_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_2202_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v_toCold_1943_; lean_object* v_options_1944_; uint8_t v_hasTrace_1945_; 
v_toCold_1943_ = lean_ctor_get(v_a_1935_, 0);
v_options_1944_ = lean_ctor_get(v_toCold_1943_, 2);
v_hasTrace_1945_ = lean_ctor_get_uint8(v_options_1944_, sizeof(void*)*1);
if (v_hasTrace_1945_ == 0)
{
lean_object* v_fst_1946_; lean_object* v_snd_1947_; lean_object* v_fst_1948_; lean_object* v_snd_1949_; lean_object* v___x_1950_; lean_object* v_cache_1951_; lean_object* v_zetaDeltaFVarIds_1952_; lean_object* v_postponed_1953_; lean_object* v_diag_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_2000_; 
lean_del_object(v___x_1941_);
v_fst_1946_ = lean_ctor_get(v_fst_1938_, 0);
lean_inc(v_fst_1946_);
v_snd_1947_ = lean_ctor_get(v_fst_1938_, 1);
lean_inc(v_snd_1947_);
lean_dec(v_fst_1938_);
v_fst_1948_ = lean_ctor_get(v_snd_1939_, 0);
lean_inc(v_fst_1948_);
v_snd_1949_ = lean_ctor_get(v_snd_1939_, 1);
lean_inc(v_snd_1949_);
lean_dec(v_snd_1939_);
v___x_1950_ = lean_st_ref_take(v_a_1934_);
v_cache_1951_ = lean_ctor_get(v___x_1950_, 1);
v_zetaDeltaFVarIds_1952_ = lean_ctor_get(v___x_1950_, 2);
v_postponed_1953_ = lean_ctor_get(v___x_1950_, 3);
v_diag_1954_ = lean_ctor_get(v___x_1950_, 4);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_2000_ == 0)
{
lean_object* v_unused_2001_; 
v_unused_2001_ = lean_ctor_get(v___x_1950_, 0);
lean_dec(v_unused_2001_);
v___x_1956_ = v___x_1950_;
v_isShared_1957_ = v_isSharedCheck_2000_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_diag_1954_);
lean_inc(v_postponed_1953_);
lean_inc(v_zetaDeltaFVarIds_1952_);
lean_inc(v_cache_1951_);
lean_dec(v___x_1950_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_2000_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 0, v_snd_1947_);
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_snd_1947_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_cache_1951_);
lean_ctor_set(v_reuseFailAlloc_1999_, 2, v_zetaDeltaFVarIds_1952_);
lean_ctor_set(v_reuseFailAlloc_1999_, 3, v_postponed_1953_);
lean_ctor_set(v_reuseFailAlloc_1999_, 4, v_diag_1954_);
v___x_1959_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
lean_object* v___x_1960_; uint8_t v___x_1961_; lean_object* v___x_1962_; 
v___x_1960_ = lean_st_ref_put(v_a_1934_, v___x_1959_);
v___x_1961_ = lean_unbox(v_snd_1949_);
lean_dec(v_snd_1949_);
v___x_1962_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_1948_, v___x_1961_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref_known(v___x_1962_, 1);
v___x_1964_ = lean_box(0);
lean_inc(v_fst_1946_);
v___x_1965_ = l_Lean_MVarId_apply(v_fst_1946_, v_a_1963_, v_cfg_1929_, v___x_1964_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v___x_1967_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc_n(v_a_1966_, 2);
lean_dec_ref_known(v___x_1965_, 1);
lean_inc(v_a_1936_);
lean_inc_ref(v_a_1935_);
lean_inc(v_a_1934_);
lean_inc_ref(v_a_1933_);
v___x_1967_ = lean_apply_6(v_act_1930_, v_a_1966_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, lean_box(0));
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_dec(v_a_1966_);
lean_dec(v_fst_1946_);
lean_dec_ref(v_allowFailure_1931_);
return v___x_1967_;
}
else
{
lean_object* v_a_1968_; uint8_t v___x_1969_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
v___x_1969_ = l_Lean_Exception_isInterrupt(v_a_1968_);
if (v___x_1969_ == 0)
{
uint8_t v___x_1970_; 
v___x_1970_ = l_Lean_Exception_isRuntime(v_a_1968_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; 
lean_dec_ref_known(v___x_1967_, 1);
lean_inc(v_a_1936_);
lean_inc_ref(v_a_1935_);
lean_inc(v_a_1934_);
lean_inc_ref(v_a_1933_);
v___x_1971_ = lean_apply_6(v_allowFailure_1931_, v_fst_1946_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, lean_box(0));
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1982_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1974_ = v___x_1971_;
v_isShared_1975_ = v_isSharedCheck_1982_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1971_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1982_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
uint8_t v___x_1976_; 
v___x_1976_ = lean_unbox(v_a_1972_);
lean_dec(v_a_1972_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
lean_del_object(v___x_1974_);
lean_dec(v_a_1966_);
v___x_1977_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1);
v___x_1978_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_1977_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
return v___x_1978_;
}
else
{
lean_object* v___x_1980_; 
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 0, v_a_1966_);
v___x_1980_ = v___x_1974_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1966_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
lean_dec(v_a_1966_);
v_a_1983_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1971_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1971_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
else
{
lean_dec(v_a_1966_);
lean_dec(v_fst_1946_);
lean_dec_ref(v_allowFailure_1931_);
return v___x_1967_;
}
}
else
{
lean_dec(v_a_1968_);
lean_dec(v_a_1966_);
lean_dec(v_fst_1946_);
lean_dec_ref(v_allowFailure_1931_);
return v___x_1967_;
}
}
}
else
{
lean_dec(v_fst_1946_);
lean_dec_ref(v_allowFailure_1931_);
lean_dec_ref(v_act_1930_);
return v___x_1965_;
}
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
lean_dec(v_fst_1946_);
lean_dec_ref(v_allowFailure_1931_);
lean_dec_ref(v_act_1930_);
lean_dec_ref(v_cfg_1929_);
v_a_1991_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___x_1962_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1962_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_a_1991_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
}
}
else
{
lean_object* v_fst_2002_; lean_object* v_snd_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2201_; 
v_fst_2002_ = lean_ctor_get(v_fst_1938_, 0);
v_snd_2003_ = lean_ctor_get(v_fst_1938_, 1);
v_isSharedCheck_2201_ = !lean_is_exclusive(v_fst_1938_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2005_ = v_fst_1938_;
v_isShared_2006_ = v_isSharedCheck_2201_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_snd_2003_);
lean_inc(v_fst_2002_);
lean_dec(v_fst_1938_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2201_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v_fst_2007_; lean_object* v_snd_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2200_; 
v_fst_2007_ = lean_ctor_get(v_snd_1939_, 0);
v_snd_2008_ = lean_ctor_get(v_snd_1939_, 1);
v_isSharedCheck_2200_ = !lean_is_exclusive(v_snd_1939_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2010_ = v_snd_1939_;
v_isShared_2011_ = v_isSharedCheck_2200_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_snd_2008_);
lean_inc(v_fst_2007_);
lean_dec(v_snd_1939_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2200_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v_inheritedTraceOptions_2012_; lean_object* v___f_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; uint8_t v___x_2017_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v_a_2021_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v_a_2040_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v_a_2045_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v_a_2050_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v_a_2064_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v_a_2069_; 
v_inheritedTraceOptions_2012_ = lean_ctor_get(v_toCold_1943_, 11);
lean_inc(v_snd_2008_);
lean_inc(v_fst_2007_);
v___f_2013_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2013_, 0, v_fst_2007_);
lean_closure_set(v___f_2013_, 1, v_snd_2008_);
v___x_2014_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_2015_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4));
v___x_2016_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2);
v___x_2017_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2012_, v_options_1944_, v___x_2016_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2146_; uint8_t v___x_2147_; 
v___x_2146_ = l_Lean_trace_profiler;
v___x_2147_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_1944_, v___x_2146_);
if (v___x_2147_ == 0)
{
lean_object* v___x_2148_; lean_object* v_cache_2149_; lean_object* v_zetaDeltaFVarIds_2150_; lean_object* v_postponed_2151_; lean_object* v_diag_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2198_; 
lean_dec_ref(v___f_2013_);
lean_del_object(v___x_2010_);
lean_del_object(v___x_2005_);
lean_del_object(v___x_1941_);
v___x_2148_ = lean_st_ref_take(v_a_1934_);
v_cache_2149_ = lean_ctor_get(v___x_2148_, 1);
v_zetaDeltaFVarIds_2150_ = lean_ctor_get(v___x_2148_, 2);
v_postponed_2151_ = lean_ctor_get(v___x_2148_, 3);
v_diag_2152_ = lean_ctor_get(v___x_2148_, 4);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2198_ == 0)
{
lean_object* v_unused_2199_; 
v_unused_2199_ = lean_ctor_get(v___x_2148_, 0);
lean_dec(v_unused_2199_);
v___x_2154_ = v___x_2148_;
v_isShared_2155_ = v_isSharedCheck_2198_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_diag_2152_);
lean_inc(v_postponed_2151_);
lean_inc(v_zetaDeltaFVarIds_2150_);
lean_inc(v_cache_2149_);
lean_dec(v___x_2148_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2198_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 0, v_snd_2003_);
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_snd_2003_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v_cache_2149_);
lean_ctor_set(v_reuseFailAlloc_2197_, 2, v_zetaDeltaFVarIds_2150_);
lean_ctor_set(v_reuseFailAlloc_2197_, 3, v_postponed_2151_);
lean_ctor_set(v_reuseFailAlloc_2197_, 4, v_diag_2152_);
v___x_2157_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
lean_object* v___x_2158_; uint8_t v___x_2159_; lean_object* v___x_2160_; 
v___x_2158_ = lean_st_ref_put(v_a_1934_, v___x_2157_);
v___x_2159_ = lean_unbox(v_snd_2008_);
lean_dec(v_snd_2008_);
v___x_2160_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2007_, v___x_2159_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2161_);
lean_dec_ref_known(v___x_2160_, 1);
v___x_2162_ = lean_box(0);
lean_inc(v_fst_2002_);
v___x_2163_ = l_Lean_MVarId_apply(v_fst_2002_, v_a_2161_, v_cfg_1929_, v___x_2162_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2165_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc_n(v_a_2164_, 2);
lean_dec_ref_known(v___x_2163_, 1);
lean_inc(v_a_1936_);
lean_inc_ref(v_a_1935_);
lean_inc(v_a_1934_);
lean_inc_ref(v_a_1933_);
v___x_2165_ = lean_apply_6(v_act_1930_, v_a_2164_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, lean_box(0));
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_dec(v_a_2164_);
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1931_);
return v___x_2165_;
}
else
{
lean_object* v_a_2166_; uint8_t v___x_2167_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_a_2166_);
v___x_2167_ = l_Lean_Exception_isInterrupt(v_a_2166_);
if (v___x_2167_ == 0)
{
uint8_t v___x_2168_; 
v___x_2168_ = l_Lean_Exception_isRuntime(v_a_2166_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; 
lean_dec_ref_known(v___x_2165_, 1);
lean_inc(v_a_1936_);
lean_inc_ref(v_a_1935_);
lean_inc(v_a_1934_);
lean_inc_ref(v_a_1933_);
v___x_2169_ = lean_apply_6(v_allowFailure_1931_, v_fst_2002_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, lean_box(0));
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2180_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2172_ = v___x_2169_;
v_isShared_2173_ = v_isSharedCheck_2180_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2180_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
uint8_t v___x_2174_; 
v___x_2174_ = lean_unbox(v_a_2170_);
lean_dec(v_a_2170_);
if (v___x_2174_ == 0)
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
lean_del_object(v___x_2172_);
lean_dec(v_a_2164_);
v___x_2175_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1);
v___x_2176_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2175_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
return v___x_2176_;
}
else
{
lean_object* v___x_2178_; 
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v_a_2164_);
v___x_2178_ = v___x_2172_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2164_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
lean_dec(v_a_2164_);
v_a_2181_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2169_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2169_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
else
{
lean_dec(v_a_2164_);
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1931_);
return v___x_2165_;
}
}
else
{
lean_dec(v_a_2166_);
lean_dec(v_a_2164_);
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1931_);
return v___x_2165_;
}
}
}
else
{
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1931_);
lean_dec_ref(v_act_1930_);
return v___x_2163_;
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1931_);
lean_dec_ref(v_act_1930_);
lean_dec_ref(v_cfg_1929_);
v_a_2189_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2160_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2160_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
}
}
else
{
goto v___jp_2071_;
}
}
else
{
goto v___jp_2071_;
}
v___jp_2018_:
{
lean_object* v___x_2022_; double v___x_2023_; double v___x_2024_; double v___x_2025_; double v___x_2026_; double v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2031_; 
v___x_2022_ = lean_io_mono_nanos_now();
v___x_2023_ = lean_float_of_nat(v___y_2019_);
v___x_2024_ = lean_float_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3);
v___x_2025_ = lean_float_div(v___x_2023_, v___x_2024_);
v___x_2026_ = lean_float_of_nat(v___x_2022_);
v___x_2027_ = lean_float_div(v___x_2026_, v___x_2024_);
v___x_2028_ = lean_box_float(v___x_2025_);
v___x_2029_ = lean_box_float(v___x_2027_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 1, v___x_2029_);
lean_ctor_set(v___x_2010_, 0, v___x_2028_);
v___x_2031_ = v___x_2010_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2028_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v___x_2029_);
v___x_2031_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2033_; 
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 1, v___x_2031_);
lean_ctor_set(v___x_2005_, 0, v_a_2021_);
v___x_2033_ = v___x_2005_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2021_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
lean_object* v___x_2034_; 
v___x_2034_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v___x_2014_, v_hasTrace_1945_, v___x_2015_, v_options_1944_, v___x_2017_, v___y_2020_, v___f_2013_, v___x_2033_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
return v___x_2034_;
}
}
}
v___jp_2037_:
{
lean_object* v___x_2041_; 
v___x_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2041_, 0, v_a_2040_);
v___y_2019_ = v___y_2038_;
v___y_2020_ = v___y_2039_;
v_a_2021_ = v___x_2041_;
goto v___jp_2018_;
}
v___jp_2042_:
{
lean_object* v___x_2046_; 
v___x_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2046_, 0, v_a_2045_);
v___y_2019_ = v___y_2043_;
v___y_2020_ = v___y_2044_;
v_a_2021_ = v___x_2046_;
goto v___jp_2018_;
}
v___jp_2047_:
{
lean_object* v___x_2051_; double v___x_2052_; double v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2057_; 
v___x_2051_ = lean_io_get_num_heartbeats();
v___x_2052_ = lean_float_of_nat(v___y_2048_);
v___x_2053_ = lean_float_of_nat(v___x_2051_);
v___x_2054_ = lean_box_float(v___x_2052_);
v___x_2055_ = lean_box_float(v___x_2053_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 1, v___x_2055_);
lean_ctor_set(v___x_1941_, 0, v___x_2054_);
v___x_2057_ = v___x_1941_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2054_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v___x_2055_);
v___x_2057_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2058_, 0, v_a_2050_);
lean_ctor_set(v___x_2058_, 1, v___x_2057_);
v___x_2059_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v___x_2014_, v_hasTrace_1945_, v___x_2015_, v_options_1944_, v___x_2017_, v___y_2049_, v___f_2013_, v___x_2058_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
return v___x_2059_;
}
}
v___jp_2061_:
{
lean_object* v___x_2065_; 
v___x_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2065_, 0, v_a_2064_);
v___y_2048_ = v___y_2062_;
v___y_2049_ = v___y_2063_;
v_a_2050_ = v___x_2065_;
goto v___jp_2047_;
}
v___jp_2066_:
{
lean_object* v___x_2070_; 
v___x_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2070_, 0, v_a_2069_);
v___y_2048_ = v___y_2067_;
v___y_2049_ = v___y_2068_;
v_a_2050_ = v___x_2070_;
goto v___jp_2047_;
}
v___jp_2071_:
{
lean_object* v___x_2072_; lean_object* v_a_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v___x_2072_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v_a_1936_);
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2073_);
lean_dec_ref(v___x_2072_);
v___x_2074_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2075_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_1944_, v___x_2074_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v_cache_2078_; lean_object* v_zetaDeltaFVarIds_2079_; lean_object* v_postponed_2080_; lean_object* v_diag_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2109_; 
lean_del_object(v___x_1941_);
v___x_2076_ = lean_io_mono_nanos_now();
v___x_2077_ = lean_st_ref_take(v_a_1934_);
v_cache_2078_ = lean_ctor_get(v___x_2077_, 1);
v_zetaDeltaFVarIds_2079_ = lean_ctor_get(v___x_2077_, 2);
v_postponed_2080_ = lean_ctor_get(v___x_2077_, 3);
v_diag_2081_ = lean_ctor_get(v___x_2077_, 4);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2109_ == 0)
{
lean_object* v_unused_2110_; 
v_unused_2110_ = lean_ctor_get(v___x_2077_, 0);
lean_dec(v_unused_2110_);
v___x_2083_ = v___x_2077_;
v_isShared_2084_ = v_isSharedCheck_2109_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_diag_2081_);
lean_inc(v_postponed_2080_);
lean_inc(v_zetaDeltaFVarIds_2079_);
lean_inc(v_cache_2078_);
lean_dec(v___x_2077_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2109_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 0, v_snd_2003_);
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_snd_2003_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_cache_2078_);
lean_ctor_set(v_reuseFailAlloc_2108_, 2, v_zetaDeltaFVarIds_2079_);
lean_ctor_set(v_reuseFailAlloc_2108_, 3, v_postponed_2080_);
lean_ctor_set(v_reuseFailAlloc_2108_, 4, v_diag_2081_);
v___x_2086_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
lean_object* v___x_2087_; uint8_t v___x_2088_; lean_object* v___x_2089_; 
v___x_2087_ = lean_st_ref_put(v_a_1934_, v___x_2086_);
v___x_2088_ = lean_unbox(v_snd_2008_);
lean_dec(v_snd_2008_);
v___x_2089_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2007_, v___x_2088_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
lean_dec_ref_known(v___x_2089_, 1);
v___x_2091_ = lean_box(0);
lean_inc(v_fst_2002_);
v___x_2092_ = l_Lean_MVarId_apply(v_fst_2002_, v_a_2090_, v_cfg_1929_, v___x_2091_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v___x_2094_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc_n(v_a_2093_, 2);
lean_dec_ref_known(v___x_2092_, 1);
lean_inc(v_a_1936_);
lean_inc_ref(v_a_1935_);
lean_inc(v_a_1934_);
lean_inc_ref(v_a_1933_);
v___x_2094_ = lean_apply_6(v_act_1930_, v_a_2093_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, lean_box(0));
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; 
lean_dec(v_a_2093_);
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1931_);
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2094_, 1);
v___y_2043_ = v___x_2076_;
v___y_2044_ = v_a_2073_;
v_a_2045_ = v_a_2095_;
goto v___jp_2042_;
}
else
{
lean_object* v_a_2096_; uint8_t v___x_2097_; 
v_a_2096_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2094_, 1);
v___x_2097_ = l_Lean_Exception_isInterrupt(v_a_2096_);
if (v___x_2097_ == 0)
{
uint8_t v___x_2098_; 
lean_inc(v_a_2096_);
v___x_2098_ = l_Lean_Exception_isRuntime(v_a_2096_);
if (v___x_2098_ == 0)
{
lean_object* v___x_2099_; 
lean_dec(v_a_2096_);
lean_inc(v_a_1936_);
lean_inc_ref(v_a_1935_);
lean_inc(v_a_1934_);
lean_inc_ref(v_a_1933_);
v___x_2099_ = lean_apply_6(v_allowFailure_1931_, v_fst_2002_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, lean_box(0));
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; uint8_t v___x_2101_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref_known(v___x_2099_, 1);
v___x_2101_ = lean_unbox(v_a_2100_);
lean_dec(v_a_2100_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v_a_2104_; 
lean_dec(v_a_2093_);
v___x_2102_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1);
v___x_2103_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2102_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2104_);
lean_dec_ref(v___x_2103_);
v___y_2038_ = v___x_2076_;
v___y_2039_ = v_a_2073_;
v_a_2040_ = v_a_2104_;
goto v___jp_2037_;
}
else
{
v___y_2043_ = v___x_2076_;
v___y_2044_ = v_a_2073_;
v_a_2045_ = v_a_2093_;
goto v___jp_2042_;
}
}
else
{
lean_object* v_a_2105_; 
lean_dec(v_a_2093_);
v_a_2105_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2105_);
lean_dec_ref_known(v___x_2099_, 1);
v___y_2038_ = v___x_2076_;
v___y_2039_ = v_a_2073_;
v_a_2040_ = v_a_2105_;
goto v___jp_2037_;
}
}
else
{
lean_dec(v_a_2093_);
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1931_);
v___y_2038_ = v___x_2076_;
v___y_2039_ = v_a_2073_;
v_a_2040_ = v_a_2096_;
goto v___jp_2037_;
}
}
else
{
lean_dec(v_a_2093_);
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1931_);
v___y_2038_ = v___x_2076_;
v___y_2039_ = v_a_2073_;
v_a_2040_ = v_a_2096_;
goto v___jp_2037_;
}
}
}
else
{
lean_object* v_a_2106_; 
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1931_);
lean_dec_ref(v_act_1930_);
v_a_2106_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2106_);
lean_dec_ref_known(v___x_2092_, 1);
v___y_2038_ = v___x_2076_;
v___y_2039_ = v_a_2073_;
v_a_2040_ = v_a_2106_;
goto v___jp_2037_;
}
}
else
{
lean_object* v_a_2107_; 
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1931_);
lean_dec_ref(v_act_1930_);
lean_dec_ref(v_cfg_1929_);
v_a_2107_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2107_);
lean_dec_ref_known(v___x_2089_, 1);
v___y_2038_ = v___x_2076_;
v___y_2039_ = v_a_2073_;
v_a_2040_ = v_a_2107_;
goto v___jp_2037_;
}
}
}
}
else
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v_cache_2113_; lean_object* v_zetaDeltaFVarIds_2114_; lean_object* v_postponed_2115_; lean_object* v_diag_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2144_; 
lean_del_object(v___x_2010_);
lean_del_object(v___x_2005_);
v___x_2111_ = lean_io_get_num_heartbeats();
v___x_2112_ = lean_st_ref_take(v_a_1934_);
v_cache_2113_ = lean_ctor_get(v___x_2112_, 1);
v_zetaDeltaFVarIds_2114_ = lean_ctor_get(v___x_2112_, 2);
v_postponed_2115_ = lean_ctor_get(v___x_2112_, 3);
v_diag_2116_ = lean_ctor_get(v___x_2112_, 4);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2144_ == 0)
{
lean_object* v_unused_2145_; 
v_unused_2145_ = lean_ctor_get(v___x_2112_, 0);
lean_dec(v_unused_2145_);
v___x_2118_ = v___x_2112_;
v_isShared_2119_ = v_isSharedCheck_2144_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_diag_2116_);
lean_inc(v_postponed_2115_);
lean_inc(v_zetaDeltaFVarIds_2114_);
lean_inc(v_cache_2113_);
lean_dec(v___x_2112_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2144_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v_snd_2003_);
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_snd_2003_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_cache_2113_);
lean_ctor_set(v_reuseFailAlloc_2143_, 2, v_zetaDeltaFVarIds_2114_);
lean_ctor_set(v_reuseFailAlloc_2143_, 3, v_postponed_2115_);
lean_ctor_set(v_reuseFailAlloc_2143_, 4, v_diag_2116_);
v___x_2121_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_object* v___x_2122_; uint8_t v___x_2123_; lean_object* v___x_2124_; 
v___x_2122_ = lean_st_ref_put(v_a_1934_, v___x_2121_);
v___x_2123_ = lean_unbox(v_snd_2008_);
lean_dec(v_snd_2008_);
v___x_2124_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2007_, v___x_2123_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2125_);
lean_dec_ref_known(v___x_2124_, 1);
v___x_2126_ = lean_box(0);
lean_inc(v_fst_2002_);
v___x_2127_ = l_Lean_MVarId_apply(v_fst_2002_, v_a_2125_, v_cfg_1929_, v___x_2126_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v___x_2129_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc_n(v_a_2128_, 2);
lean_dec_ref_known(v___x_2127_, 1);
lean_inc(v_a_1936_);
lean_inc_ref(v_a_1935_);
lean_inc(v_a_1934_);
lean_inc_ref(v_a_1933_);
v___x_2129_ = lean_apply_6(v_act_1930_, v_a_2128_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, lean_box(0));
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; 
lean_dec(v_a_2128_);
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1931_);
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v___x_2129_, 1);
v___y_2067_ = v___x_2111_;
v___y_2068_ = v_a_2073_;
v_a_2069_ = v_a_2130_;
goto v___jp_2066_;
}
else
{
lean_object* v_a_2131_; uint8_t v___x_2132_; 
v_a_2131_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2129_, 1);
v___x_2132_ = l_Lean_Exception_isInterrupt(v_a_2131_);
if (v___x_2132_ == 0)
{
uint8_t v___x_2133_; 
lean_inc(v_a_2131_);
v___x_2133_ = l_Lean_Exception_isRuntime(v_a_2131_);
if (v___x_2133_ == 0)
{
lean_object* v___x_2134_; 
lean_dec(v_a_2131_);
lean_inc(v_a_1936_);
lean_inc_ref(v_a_1935_);
lean_inc(v_a_1934_);
lean_inc_ref(v_a_1933_);
v___x_2134_ = lean_apply_6(v_allowFailure_1931_, v_fst_2002_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, lean_box(0));
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; uint8_t v___x_2136_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2134_, 1);
v___x_2136_ = lean_unbox(v_a_2135_);
lean_dec(v_a_2135_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v_a_2139_; 
lean_dec(v_a_2128_);
v___x_2137_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1);
v___x_2138_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2137_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref(v___x_2138_);
v___y_2062_ = v___x_2111_;
v___y_2063_ = v_a_2073_;
v_a_2064_ = v_a_2139_;
goto v___jp_2061_;
}
else
{
v___y_2067_ = v___x_2111_;
v___y_2068_ = v_a_2073_;
v_a_2069_ = v_a_2128_;
goto v___jp_2066_;
}
}
else
{
lean_object* v_a_2140_; 
lean_dec(v_a_2128_);
v_a_2140_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2134_, 1);
v___y_2062_ = v___x_2111_;
v___y_2063_ = v_a_2073_;
v_a_2064_ = v_a_2140_;
goto v___jp_2061_;
}
}
else
{
lean_dec(v_a_2128_);
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1931_);
v___y_2062_ = v___x_2111_;
v___y_2063_ = v_a_2073_;
v_a_2064_ = v_a_2131_;
goto v___jp_2061_;
}
}
else
{
lean_dec(v_a_2128_);
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1931_);
v___y_2062_ = v___x_2111_;
v___y_2063_ = v_a_2073_;
v_a_2064_ = v_a_2131_;
goto v___jp_2061_;
}
}
}
else
{
lean_object* v_a_2141_; 
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1931_);
lean_dec_ref(v_act_1930_);
v_a_2141_ = lean_ctor_get(v___x_2127_, 0);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2127_, 1);
v___y_2062_ = v___x_2111_;
v___y_2063_ = v_a_2073_;
v_a_2064_ = v_a_2141_;
goto v___jp_2061_;
}
}
else
{
lean_object* v_a_2142_; 
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1931_);
lean_dec_ref(v_act_1930_);
lean_dec_ref(v_cfg_1929_);
v_a_2142_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2124_, 1);
v___y_2062_ = v___x_2111_;
v___y_2063_ = v_a_2073_;
v_a_2064_ = v_a_2142_;
goto v___jp_2061_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___boxed(lean_object* v_cfg_2203_, lean_object* v_act_2204_, lean_object* v_allowFailure_2205_, lean_object* v_cand_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(v_cfg_2203_, v_act_2204_, v_allowFailure_2205_, v_cand_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_);
lean_dec(v_a_2210_);
lean_dec_ref(v_a_2209_);
lean_dec(v_a_2208_);
lean_dec_ref(v_a_2207_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(lean_object* v_00_u03b1_2213_, lean_object* v_x_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_x_2214_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2221_, lean_object* v_x_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(v_00_u03b1_2221_, v_x_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(lean_object* v_act_2231_, lean_object* v_a_2232_, uint8_t v_collectAll_2233_, lean_object* v_as_2234_, size_t v_sz_2235_, size_t v_i_2236_, lean_object* v_b_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v_a_2244_; uint8_t v___x_2248_; 
v___x_2248_ = lean_usize_dec_lt(v_i_2236_, v_sz_2235_);
if (v___x_2248_ == 0)
{
lean_object* v___x_2249_; 
lean_dec_ref(v_a_2232_);
lean_dec_ref(v_act_2231_);
v___x_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2249_, 0, v_b_2237_);
return v___x_2249_;
}
else
{
lean_object* v_snd_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2322_; 
v_snd_2250_ = lean_ctor_get(v_b_2237_, 1);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_b_2237_);
if (v_isSharedCheck_2322_ == 0)
{
lean_object* v_unused_2323_; 
v_unused_2323_ = lean_ctor_get(v_b_2237_, 0);
lean_dec(v_unused_2323_);
v___x_2252_ = v_b_2237_;
v_isShared_2253_ = v_isSharedCheck_2322_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_snd_2250_);
lean_dec(v_b_2237_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2322_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2254_; lean_object* v_a_2255_; lean_object* v___x_2256_; 
v___x_2254_ = lean_box(0);
v_a_2255_ = lean_array_uget_borrowed(v_as_2234_, v_i_2236_);
lean_inc_ref(v_act_2231_);
lean_inc(v___y_2241_);
lean_inc_ref(v___y_2240_);
lean_inc(v___y_2239_);
lean_inc_ref(v___y_2238_);
lean_inc(v_a_2255_);
v___x_2256_ = lean_apply_6(v_act_2231_, v_a_2255_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, lean_box(0));
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2284_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2259_ = v___x_2256_;
v_isShared_2260_ = v_isSharedCheck_2284_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2284_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
uint8_t v___x_2278_; 
v___x_2278_ = l_List_isEmpty___redArg(v_a_2257_);
if (v___x_2278_ == 0)
{
lean_del_object(v___x_2259_);
goto v___jp_2261_;
}
else
{
if (v_collectAll_2233_ == 0)
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2282_; 
lean_dec(v_a_2257_);
lean_del_object(v___x_2252_);
lean_dec_ref(v_a_2232_);
lean_dec_ref(v_act_2231_);
v___x_2279_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___closed__0));
v___x_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
lean_ctor_set(v___x_2280_, 1, v_snd_2250_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v___x_2280_);
v___x_2282_ = v___x_2259_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2280_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
else
{
lean_del_object(v___x_2259_);
goto v___jp_2261_;
}
}
v___jp_2261_:
{
lean_object* v___x_2262_; lean_object* v_mctx_2263_; lean_object* v___x_2264_; 
v___x_2262_ = lean_st_ref_get(v___y_2239_);
v_mctx_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc_ref(v_mctx_2263_);
lean_dec(v___x_2262_);
lean_inc_ref(v_a_2232_);
v___x_2264_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2232_, v___y_2239_, v___y_2241_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v___x_2266_; 
lean_dec_ref_known(v___x_2264_, 1);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 1, v_mctx_2263_);
lean_ctor_set(v___x_2252_, 0, v_a_2257_);
v___x_2266_ = v___x_2252_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2257_);
lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_mctx_2263_);
v___x_2266_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2267_ = lean_array_push(v_snd_2250_, v___x_2266_);
v___x_2268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2254_);
lean_ctor_set(v___x_2268_, 1, v___x_2267_);
v_a_2244_ = v___x_2268_;
goto v___jp_2243_;
}
}
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
lean_dec_ref(v_mctx_2263_);
lean_dec(v_a_2257_);
lean_del_object(v___x_2252_);
lean_dec(v_snd_2250_);
lean_dec_ref(v_a_2232_);
lean_dec_ref(v_act_2231_);
v_a_2270_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2264_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2264_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2270_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
}
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2321_; 
v_a_2285_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2287_ = v___x_2256_;
v_isShared_2288_ = v_isSharedCheck_2321_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2256_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2321_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
uint8_t v___x_2289_; 
v___x_2289_ = l_Lean_Exception_isInterrupt(v_a_2285_);
if (v___x_2289_ == 0)
{
uint8_t v___x_2290_; 
lean_inc(v_a_2285_);
v___x_2290_ = l_Lean_Exception_isRuntime(v_a_2285_);
if (v___x_2290_ == 0)
{
lean_object* v___x_2291_; 
lean_del_object(v___x_2287_);
lean_inc_ref(v_a_2232_);
v___x_2291_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2232_, v___y_2239_, v___y_2241_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2305_; 
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2305_ == 0)
{
lean_object* v_unused_2306_; 
v_unused_2306_ = lean_ctor_get(v___x_2291_, 0);
lean_dec(v_unused_2306_);
v___x_2293_ = v___x_2291_;
v_isShared_2294_ = v_isSharedCheck_2305_;
goto v_resetjp_2292_;
}
else
{
lean_dec(v___x_2291_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2305_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
uint8_t v___x_2295_; 
v___x_2295_ = l_Lean_Meta_LibrarySearch_isAbortSpeculation(v_a_2285_);
lean_dec(v_a_2285_);
if (v___x_2295_ == 0)
{
lean_object* v___x_2297_; 
lean_del_object(v___x_2293_);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 0, v___x_2254_);
v___x_2297_ = v___x_2252_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2254_);
lean_ctor_set(v_reuseFailAlloc_2298_, 1, v_snd_2250_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
v_a_2244_ = v___x_2297_;
goto v___jp_2243_;
}
}
else
{
lean_object* v___x_2300_; 
lean_dec_ref(v_a_2232_);
lean_dec_ref(v_act_2231_);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 0, v___x_2254_);
v___x_2300_ = v___x_2252_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v___x_2254_);
lean_ctor_set(v_reuseFailAlloc_2304_, 1, v_snd_2250_);
v___x_2300_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
lean_object* v___x_2302_; 
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 0, v___x_2300_);
v___x_2302_ = v___x_2293_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2300_);
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
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec(v_a_2285_);
lean_del_object(v___x_2252_);
lean_dec(v_snd_2250_);
lean_dec_ref(v_a_2232_);
lean_dec_ref(v_act_2231_);
v_a_2307_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2291_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2291_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
else
{
lean_object* v___x_2316_; 
lean_del_object(v___x_2252_);
lean_dec(v_snd_2250_);
lean_dec_ref(v_a_2232_);
lean_dec_ref(v_act_2231_);
if (v_isShared_2288_ == 0)
{
v___x_2316_ = v___x_2287_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2285_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
else
{
lean_object* v___x_2319_; 
lean_del_object(v___x_2252_);
lean_dec(v_snd_2250_);
lean_dec_ref(v_a_2232_);
lean_dec_ref(v_act_2231_);
if (v_isShared_2288_ == 0)
{
v___x_2319_ = v___x_2287_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2285_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
}
}
v___jp_2243_:
{
size_t v___x_2245_; size_t v___x_2246_; 
v___x_2245_ = ((size_t)1ULL);
v___x_2246_ = lean_usize_add(v_i_2236_, v___x_2245_);
v_i_2236_ = v___x_2246_;
v_b_2237_ = v_a_2244_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___boxed(lean_object* v_act_2324_, lean_object* v_a_2325_, lean_object* v_collectAll_2326_, lean_object* v_as_2327_, lean_object* v_sz_2328_, lean_object* v_i_2329_, lean_object* v_b_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
uint8_t v_collectAll_boxed_2336_; size_t v_sz_boxed_2337_; size_t v_i_boxed_2338_; lean_object* v_res_2339_; 
v_collectAll_boxed_2336_ = lean_unbox(v_collectAll_2326_);
v_sz_boxed_2337_ = lean_unbox_usize(v_sz_2328_);
lean_dec(v_sz_2328_);
v_i_boxed_2338_ = lean_unbox_usize(v_i_2329_);
lean_dec(v_i_2329_);
v_res_2339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(v_act_2324_, v_a_2325_, v_collectAll_boxed_2336_, v_as_2327_, v_sz_boxed_2337_, v_i_boxed_2338_, v_b_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec_ref(v_as_2327_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryOnEach(lean_object* v_act_2345_, lean_object* v_candidates_2346_, uint8_t v_collectAll_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_){
_start:
{
lean_object* v___x_2353_; 
v___x_2353_ = l_Lean_Meta_saveState___redArg(v_a_2349_, v_a_2351_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v___x_2355_; size_t v_sz_2356_; size_t v___x_2357_; lean_object* v___x_2358_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2354_);
lean_dec_ref_known(v___x_2353_, 1);
v___x_2355_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryOnEach___closed__1));
v_sz_2356_ = lean_array_size(v_candidates_2346_);
v___x_2357_ = ((size_t)0ULL);
v___x_2358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(v_act_2345_, v_a_2354_, v_collectAll_2347_, v_candidates_2346_, v_sz_2356_, v___x_2357_, v___x_2355_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2373_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2361_ = v___x_2358_;
v_isShared_2362_ = v_isSharedCheck_2373_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2358_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2373_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v_fst_2363_; 
v_fst_2363_ = lean_ctor_get(v_a_2359_, 0);
if (lean_obj_tag(v_fst_2363_) == 0)
{
lean_object* v_snd_2364_; lean_object* v___x_2365_; lean_object* v___x_2367_; 
v_snd_2364_ = lean_ctor_get(v_a_2359_, 1);
lean_inc(v_snd_2364_);
lean_dec(v_a_2359_);
v___x_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2365_, 0, v_snd_2364_);
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 0, v___x_2365_);
v___x_2367_ = v___x_2361_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2365_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
else
{
lean_object* v_val_2369_; lean_object* v___x_2371_; 
lean_inc_ref(v_fst_2363_);
lean_dec(v_a_2359_);
v_val_2369_ = lean_ctor_get(v_fst_2363_, 0);
lean_inc(v_val_2369_);
lean_dec_ref_known(v_fst_2363_, 1);
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 0, v_val_2369_);
v___x_2371_ = v___x_2361_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_val_2369_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2381_; 
v_a_2374_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2376_ = v___x_2358_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2358_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
lean_dec_ref(v_act_2345_);
v_a_2382_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2353_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2353_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2382_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryOnEach___boxed(lean_object* v_act_2390_, lean_object* v_candidates_2391_, lean_object* v_collectAll_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_){
_start:
{
uint8_t v_collectAll_boxed_2398_; lean_object* v_res_2399_; 
v_collectAll_boxed_2398_ = lean_unbox(v_collectAll_2392_);
v_res_2399_ = l_Lean_Meta_LibrarySearch_tryOnEach(v_act_2390_, v_candidates_2391_, v_collectAll_boxed_2398_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
lean_dec(v_a_2396_);
lean_dec_ref(v_a_2395_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
lean_dec_ref(v_candidates_2391_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg(){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2401_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0, &l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0_once, _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0);
v___x_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2401_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg___boxed(lean_object* v___y_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(lean_object* v_00_u03b1_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___boxed(lean_object* v_00_u03b1_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(v_00_u03b1_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(lean_object* v_category_2419_, lean_object* v_opts_2420_, lean_object* v_act_2421_, lean_object* v_decl_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
lean_inc(v___y_2426_);
lean_inc_ref(v___y_2425_);
lean_inc(v___y_2424_);
lean_inc_ref(v___y_2423_);
v___x_2428_ = lean_apply_4(v_act_2421_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
v___x_2429_ = l_Lean_profileitIOUnsafe___redArg(v_category_2419_, v_opts_2420_, v___x_2428_, v_decl_2422_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg___boxed(lean_object* v_category_2430_, lean_object* v_opts_2431_, lean_object* v_act_2432_, lean_object* v_decl_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v_category_2430_, v_opts_2431_, v_act_2432_, v_decl_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec_ref(v_opts_2431_);
lean_dec_ref(v_category_2430_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(lean_object* v_00_u03b1_2440_, lean_object* v_category_2441_, lean_object* v_opts_2442_, lean_object* v_act_2443_, lean_object* v_decl_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v_category_2441_, v_opts_2442_, v_act_2443_, v_decl_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___boxed(lean_object* v_00_u03b1_2451_, lean_object* v_category_2452_, lean_object* v_opts_2453_, lean_object* v_act_2454_, lean_object* v_decl_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(v_00_u03b1_2451_, v_category_2452_, v_opts_2453_, v_act_2454_, v_decl_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec_ref(v_opts_2453_);
lean_dec_ref(v_category_2452_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0(lean_object* v_a_2462_, lean_object* v___x_2463_, lean_object* v_tactic_2464_, lean_object* v_allowFailure_2465_, lean_object* v_cand_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_){
_start:
{
lean_object* v___x_2472_; 
lean_inc(v___y_2470_);
lean_inc_ref(v___y_2469_);
lean_inc(v___y_2468_);
lean_inc_ref(v___y_2467_);
v___x_2472_ = lean_apply_5(v_a_2462_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, lean_box(0));
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v_a_2473_; uint8_t v___x_2474_; 
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_a_2473_);
lean_dec_ref_known(v___x_2472_, 1);
v___x_2474_ = lean_unbox(v_a_2473_);
lean_dec(v_a_2473_);
if (v___x_2474_ == 0)
{
lean_object* v___x_2475_; 
v___x_2475_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(v___x_2463_, v_tactic_2464_, v_allowFailure_2465_, v_cand_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
return v___x_2475_;
}
else
{
lean_object* v___x_2476_; lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec_ref(v_cand_2466_);
lean_dec_ref(v_allowFailure_2465_);
lean_dec_ref(v_tactic_2464_);
lean_dec_ref(v___x_2463_);
v___x_2476_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2476_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2476_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_dec_ref(v_cand_2466_);
lean_dec_ref(v_allowFailure_2465_);
lean_dec_ref(v_tactic_2464_);
lean_dec_ref(v___x_2463_);
v_a_2485_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2472_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2472_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed(lean_object* v_a_2493_, lean_object* v___x_2494_, lean_object* v_tactic_2495_, lean_object* v_allowFailure_2496_, lean_object* v_cand_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0(v_a_2493_, v___x_2494_, v_tactic_2495_, v_allowFailure_2496_, v_cand_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
return v_res_2503_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(lean_object* v_as_2504_, size_t v_i_2505_, size_t v_stop_2506_){
_start:
{
uint8_t v___x_2507_; 
v___x_2507_ = lean_usize_dec_eq(v_i_2505_, v_stop_2506_);
if (v___x_2507_ == 0)
{
lean_object* v___x_2508_; lean_object* v_fst_2509_; uint8_t v___x_2510_; 
v___x_2508_ = lean_array_uget_borrowed(v_as_2504_, v_i_2505_);
v_fst_2509_ = lean_ctor_get(v___x_2508_, 0);
v___x_2510_ = l_List_isEmpty___redArg(v_fst_2509_);
if (v___x_2510_ == 0)
{
size_t v___x_2511_; size_t v___x_2512_; 
v___x_2511_ = ((size_t)1ULL);
v___x_2512_ = lean_usize_add(v_i_2505_, v___x_2511_);
v_i_2505_ = v___x_2512_;
goto _start;
}
else
{
return v___x_2510_;
}
}
else
{
uint8_t v___x_2514_; 
v___x_2514_ = 0;
return v___x_2514_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2___boxed(lean_object* v_as_2515_, lean_object* v_i_2516_, lean_object* v_stop_2517_){
_start:
{
size_t v_i_boxed_2518_; size_t v_stop_boxed_2519_; uint8_t v_res_2520_; lean_object* v_r_2521_; 
v_i_boxed_2518_ = lean_unbox_usize(v_i_2516_);
lean_dec(v_i_2516_);
v_stop_boxed_2519_ = lean_unbox_usize(v_stop_2517_);
lean_dec(v_stop_2517_);
v_res_2520_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_as_2515_, v_i_boxed_2518_, v_stop_boxed_2519_);
lean_dec_ref(v_as_2515_);
v_r_2521_ = lean_box(v_res_2520_);
return v_r_2521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(lean_object* v_goal_2522_, lean_object* v___x_2523_, size_t v_sz_2524_, size_t v_i_2525_, lean_object* v_bs_2526_){
_start:
{
uint8_t v___x_2527_; 
v___x_2527_ = lean_usize_dec_lt(v_i_2525_, v_sz_2524_);
if (v___x_2527_ == 0)
{
lean_dec_ref(v___x_2523_);
lean_dec(v_goal_2522_);
return v_bs_2526_;
}
else
{
lean_object* v_v_2528_; lean_object* v___x_2529_; lean_object* v_bs_x27_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; size_t v___x_2533_; size_t v___x_2534_; lean_object* v___x_2535_; 
v_v_2528_ = lean_array_uget(v_bs_2526_, v_i_2525_);
v___x_2529_ = lean_unsigned_to_nat(0u);
v_bs_x27_2530_ = lean_array_uset(v_bs_2526_, v_i_2525_, v___x_2529_);
lean_inc_ref(v___x_2523_);
lean_inc(v_goal_2522_);
v___x_2531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2531_, 0, v_goal_2522_);
lean_ctor_set(v___x_2531_, 1, v___x_2523_);
v___x_2532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
lean_ctor_set(v___x_2532_, 1, v_v_2528_);
v___x_2533_ = ((size_t)1ULL);
v___x_2534_ = lean_usize_add(v_i_2525_, v___x_2533_);
v___x_2535_ = lean_array_uset(v_bs_x27_2530_, v_i_2525_, v___x_2532_);
v_i_2525_ = v___x_2534_;
v_bs_2526_ = v___x_2535_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1___boxed(lean_object* v_goal_2537_, lean_object* v___x_2538_, lean_object* v_sz_2539_, lean_object* v_i_2540_, lean_object* v_bs_2541_){
_start:
{
size_t v_sz_boxed_2542_; size_t v_i_boxed_2543_; lean_object* v_res_2544_; 
v_sz_boxed_2542_ = lean_unbox_usize(v_sz_2539_);
lean_dec(v_sz_2539_);
v_i_boxed_2543_ = lean_unbox_usize(v_i_2540_);
lean_dec(v_i_2540_);
v_res_2544_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2537_, v___x_2538_, v_sz_boxed_2542_, v_i_boxed_2543_, v_bs_2541_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(lean_object* v_leavePercentHeartbeats_2546_, lean_object* v___x_2547_, lean_object* v_tactic_2548_, lean_object* v_allowFailure_2549_, lean_object* v_goal_2550_, uint8_t v_collectAll_2551_, uint8_t v_includeStar_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2546_, v___y_2555_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; lean_object* v___f_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_a_2562_);
lean_dec_ref_known(v___x_2561_, 1);
v___f_2563_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2563_, 0, v_a_2562_);
lean_closure_set(v___f_2563_, 1, v___x_2547_);
lean_closure_set(v___f_2563_, 2, v_tactic_2548_);
lean_closure_set(v___f_2563_, 3, v_allowFailure_2549_);
v___x_2564_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0));
lean_inc(v_goal_2550_);
v___x_2565_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2564_, v_goal_2550_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2567_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec_ref_known(v___x_2565_, 1);
lean_inc_ref(v___f_2563_);
v___x_2567_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2563_, v_a_2566_, v_collectAll_2551_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
lean_dec(v_a_2566_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_a_2568_; 
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
if (lean_obj_tag(v_a_2568_) == 0)
{
lean_dec_ref_known(v___x_2567_, 1);
lean_dec_ref(v___f_2563_);
lean_dec(v_goal_2550_);
goto v___jp_2558_;
}
else
{
lean_object* v_val_2569_; lean_object* v___x_2618_; lean_object* v___x_2619_; uint8_t v___x_2620_; 
v_val_2569_ = lean_ctor_get(v_a_2568_, 0);
v___x_2618_ = lean_unsigned_to_nat(0u);
v___x_2619_ = lean_array_get_size(v_val_2569_);
v___x_2620_ = lean_nat_dec_lt(v___x_2618_, v___x_2619_);
if (v___x_2620_ == 0)
{
goto v___jp_2614_;
}
else
{
if (v___x_2620_ == 0)
{
goto v___jp_2614_;
}
else
{
size_t v___x_2621_; size_t v___x_2622_; uint8_t v___x_2623_; 
v___x_2621_ = ((size_t)0ULL);
v___x_2622_ = lean_usize_of_nat(v___x_2619_);
v___x_2623_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_val_2569_, v___x_2621_, v___x_2622_);
if (v___x_2623_ == 0)
{
goto v___jp_2614_;
}
else
{
lean_dec_ref(v___f_2563_);
lean_dec(v_goal_2550_);
return v___x_2567_;
}
}
}
v___jp_2570_:
{
if (v_includeStar_2552_ == 0)
{
lean_dec_ref(v___f_2563_);
lean_dec(v_goal_2550_);
return v___x_2567_;
}
else
{
lean_object* v___x_2571_; 
lean_inc_ref(v_a_2568_);
lean_dec_ref_known(v___x_2567_, 1);
v___x_2571_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2605_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2574_ = v___x_2571_;
v_isShared_2575_ = v_isSharedCheck_2605_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2571_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2605_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; 
v___x_2576_ = lean_array_get_size(v_a_2572_);
v___x_2577_ = lean_unsigned_to_nat(0u);
v___x_2578_ = lean_nat_dec_eq(v___x_2576_, v___x_2577_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2579_; lean_object* v_mctx_2580_; size_t v_sz_2581_; size_t v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
lean_inc(v_val_2569_);
lean_del_object(v___x_2574_);
lean_dec_ref_known(v_a_2568_, 1);
v___x_2579_ = lean_st_ref_get(v___y_2554_);
v_mctx_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc_ref(v_mctx_2580_);
lean_dec(v___x_2579_);
v_sz_2581_ = lean_array_size(v_a_2572_);
v___x_2582_ = ((size_t)0ULL);
v___x_2583_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2550_, v_mctx_2580_, v_sz_2581_, v___x_2582_, v_a_2572_);
v___x_2584_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2563_, v___x_2583_, v_collectAll_2551_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
lean_dec_ref(v___x_2583_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2601_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2587_ = v___x_2584_;
v_isShared_2588_ = v_isSharedCheck_2601_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2584_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2601_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
if (lean_obj_tag(v_a_2585_) == 0)
{
lean_del_object(v___x_2587_);
lean_dec(v_val_2569_);
goto v___jp_2558_;
}
else
{
lean_object* v_val_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2600_; 
v_val_2589_ = lean_ctor_get(v_a_2585_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v_a_2585_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2591_ = v_a_2585_;
v_isShared_2592_ = v_isSharedCheck_2600_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_val_2589_);
lean_dec(v_a_2585_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2600_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2593_; lean_object* v___x_2595_; 
v___x_2593_ = l_Array_append___redArg(v_val_2569_, v_val_2589_);
lean_dec(v_val_2589_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v___x_2593_);
v___x_2595_ = v___x_2591_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2593_);
v___x_2595_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
lean_object* v___x_2597_; 
if (v_isShared_2588_ == 0)
{
lean_ctor_set(v___x_2587_, 0, v___x_2595_);
v___x_2597_ = v___x_2587_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2595_);
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
else
{
lean_dec(v_val_2569_);
return v___x_2584_;
}
}
else
{
lean_object* v___x_2603_; 
lean_dec(v_a_2572_);
lean_dec_ref(v___f_2563_);
lean_dec(v_goal_2550_);
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 0, v_a_2568_);
v___x_2603_ = v___x_2574_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2568_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
lean_dec_ref_known(v_a_2568_, 1);
lean_dec_ref(v___f_2563_);
lean_dec(v_goal_2550_);
v_a_2606_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2571_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2571_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
}
v___jp_2614_:
{
if (v_collectAll_2551_ == 0)
{
lean_object* v___x_2615_; lean_object* v___x_2616_; uint8_t v___x_2617_; 
v___x_2615_ = lean_array_get_size(v_val_2569_);
v___x_2616_ = lean_unsigned_to_nat(0u);
v___x_2617_ = lean_nat_dec_eq(v___x_2615_, v___x_2616_);
if (v___x_2617_ == 0)
{
lean_dec_ref(v___f_2563_);
lean_dec(v_goal_2550_);
return v___x_2567_;
}
else
{
goto v___jp_2570_;
}
}
else
{
goto v___jp_2570_;
}
}
}
}
else
{
lean_dec_ref(v___f_2563_);
lean_dec(v_goal_2550_);
return v___x_2567_;
}
}
else
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_dec_ref(v___f_2563_);
lean_dec(v_goal_2550_);
v_a_2624_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2565_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2565_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
lean_dec(v_goal_2550_);
lean_dec_ref(v_allowFailure_2549_);
lean_dec_ref(v_tactic_2548_);
lean_dec_ref(v___x_2547_);
v_a_2632_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2561_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2561_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
v___jp_2558_:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2559_ = lean_box(0);
v___x_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
return v___x_2560_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed(lean_object* v_leavePercentHeartbeats_2640_, lean_object* v___x_2641_, lean_object* v_tactic_2642_, lean_object* v_allowFailure_2643_, lean_object* v_goal_2644_, lean_object* v_collectAll_2645_, lean_object* v_includeStar_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
uint8_t v_collectAll_boxed_2652_; uint8_t v_includeStar_boxed_2653_; lean_object* v_res_2654_; 
v_collectAll_boxed_2652_ = lean_unbox(v_collectAll_2645_);
v_includeStar_boxed_2653_ = lean_unbox(v_includeStar_2646_);
v_res_2654_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(v_leavePercentHeartbeats_2640_, v___x_2641_, v_tactic_2642_, v_allowFailure_2643_, v_goal_2644_, v_collectAll_boxed_2652_, v_includeStar_boxed_2653_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v_leavePercentHeartbeats_2640_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2(lean_object* v_goal_2655_, lean_object* v_x_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = l_Lean_MVarId_getType(v_goal_2655_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2671_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2665_ = v___x_2662_;
v_isShared_2666_ = v_isSharedCheck_2671_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2662_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2671_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2667_; lean_object* v___x_2669_; 
v___x_2667_ = l_Lean_MessageData_ofExpr(v_a_2663_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 0, v___x_2667_);
v___x_2669_ = v___x_2665_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2667_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
else
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2679_; 
v_a_2672_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2674_ = v___x_2662_;
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2662_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
if (v_isShared_2675_ == 0)
{
v___x_2677_ = v___x_2674_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2672_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___boxed(lean_object* v_goal_2680_, lean_object* v_x_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2(v_goal_2680_, v_x_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec_ref(v_x_2681_);
return v_res_2687_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(lean_object* v_e_2688_){
_start:
{
if (lean_obj_tag(v_e_2688_) == 0)
{
uint8_t v___x_2689_; 
v___x_2689_ = 2;
return v___x_2689_;
}
else
{
lean_object* v_a_2690_; 
v_a_2690_ = lean_ctor_get(v_e_2688_, 0);
if (lean_obj_tag(v_a_2690_) == 0)
{
uint8_t v___x_2691_; 
v___x_2691_ = 1;
return v___x_2691_;
}
else
{
uint8_t v___x_2692_; 
v___x_2692_ = 0;
return v___x_2692_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4___boxed(lean_object* v_e_2693_){
_start:
{
uint8_t v_res_2694_; lean_object* v_r_2695_; 
v_res_2694_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(v_e_2693_);
lean_dec_ref(v_e_2693_);
v_r_2695_ = lean_box(v_res_2694_);
return v_r_2695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(lean_object* v_cls_2696_, uint8_t v_collapsed_2697_, lean_object* v_tag_2698_, lean_object* v_opts_2699_, uint8_t v_clsEnabled_2700_, lean_object* v_oldTraces_2701_, lean_object* v_msg_2702_, lean_object* v_resStartStop_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v_fst_2709_; lean_object* v_snd_2710_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v_data_2714_; lean_object* v_fst_2725_; lean_object* v_snd_2726_; lean_object* v___x_2727_; uint8_t v___x_2728_; lean_object* v___y_2730_; lean_object* v_a_2731_; uint8_t v___y_2746_; double v___y_2778_; 
v_fst_2709_ = lean_ctor_get(v_resStartStop_2703_, 0);
lean_inc(v_fst_2709_);
v_snd_2710_ = lean_ctor_get(v_resStartStop_2703_, 1);
lean_inc(v_snd_2710_);
lean_dec_ref(v_resStartStop_2703_);
v_fst_2725_ = lean_ctor_get(v_snd_2710_, 0);
lean_inc(v_fst_2725_);
v_snd_2726_ = lean_ctor_get(v_snd_2710_, 1);
lean_inc(v_snd_2726_);
lean_dec(v_snd_2710_);
v___x_2727_ = l_Lean_trace_profiler;
v___x_2728_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_2699_, v___x_2727_);
if (v___x_2728_ == 0)
{
v___y_2746_ = v___x_2728_;
goto v___jp_2745_;
}
else
{
lean_object* v___x_2783_; uint8_t v___x_2784_; 
v___x_2783_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2784_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_2699_, v___x_2783_);
if (v___x_2784_ == 0)
{
lean_object* v___x_2785_; lean_object* v___x_2786_; double v___x_2787_; double v___x_2788_; double v___x_2789_; 
v___x_2785_ = l_Lean_trace_profiler_threshold;
v___x_2786_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_2699_, v___x_2785_);
v___x_2787_ = lean_float_of_nat(v___x_2786_);
v___x_2788_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3);
v___x_2789_ = lean_float_div(v___x_2787_, v___x_2788_);
v___y_2778_ = v___x_2789_;
goto v___jp_2777_;
}
else
{
lean_object* v___x_2790_; lean_object* v___x_2791_; double v___x_2792_; 
v___x_2790_ = l_Lean_trace_profiler_threshold;
v___x_2791_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_2699_, v___x_2790_);
v___x_2792_ = lean_float_of_nat(v___x_2791_);
v___y_2778_ = v___x_2792_;
goto v___jp_2777_;
}
}
v___jp_2711_:
{
lean_object* v___x_2715_; 
lean_inc(v___y_2712_);
v___x_2715_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_2701_, v_data_2714_, v___y_2712_, v___y_2713_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v___x_2716_; 
lean_dec_ref_known(v___x_2715_, 1);
v___x_2716_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_2709_);
return v___x_2716_;
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
lean_dec(v_fst_2709_);
v_a_2717_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2719_ = v___x_2715_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2715_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
v___jp_2729_:
{
uint8_t v_result_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; double v___x_2735_; lean_object* v_data_2736_; 
v_result_2732_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(v_fst_2709_);
v___x_2733_ = lean_box(v_result_2732_);
v___x_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2733_);
v___x_2735_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0);
lean_inc_ref(v_tag_2698_);
lean_inc_ref(v___x_2734_);
lean_inc(v_cls_2696_);
v_data_2736_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2736_, 0, v_cls_2696_);
lean_ctor_set(v_data_2736_, 1, v___x_2734_);
lean_ctor_set(v_data_2736_, 2, v_tag_2698_);
lean_ctor_set_float(v_data_2736_, sizeof(void*)*3, v___x_2735_);
lean_ctor_set_float(v_data_2736_, sizeof(void*)*3 + 8, v___x_2735_);
lean_ctor_set_uint8(v_data_2736_, sizeof(void*)*3 + 16, v_collapsed_2697_);
if (v___x_2728_ == 0)
{
lean_dec_ref_known(v___x_2734_, 1);
lean_dec(v_snd_2726_);
lean_dec(v_fst_2725_);
lean_dec_ref(v_tag_2698_);
lean_dec(v_cls_2696_);
v___y_2712_ = v___y_2730_;
v___y_2713_ = v_a_2731_;
v_data_2714_ = v_data_2736_;
goto v___jp_2711_;
}
else
{
lean_object* v_data_2737_; double v___x_2738_; double v___x_2739_; 
lean_dec_ref_known(v_data_2736_, 3);
v_data_2737_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2737_, 0, v_cls_2696_);
lean_ctor_set(v_data_2737_, 1, v___x_2734_);
lean_ctor_set(v_data_2737_, 2, v_tag_2698_);
v___x_2738_ = lean_unbox_float(v_fst_2725_);
lean_dec(v_fst_2725_);
lean_ctor_set_float(v_data_2737_, sizeof(void*)*3, v___x_2738_);
v___x_2739_ = lean_unbox_float(v_snd_2726_);
lean_dec(v_snd_2726_);
lean_ctor_set_float(v_data_2737_, sizeof(void*)*3 + 8, v___x_2739_);
lean_ctor_set_uint8(v_data_2737_, sizeof(void*)*3 + 16, v_collapsed_2697_);
v___y_2712_ = v___y_2730_;
v___y_2713_ = v_a_2731_;
v_data_2714_ = v_data_2737_;
goto v___jp_2711_;
}
}
v___jp_2740_:
{
lean_object* v_ref_2741_; lean_object* v___x_2742_; 
v_ref_2741_ = lean_ctor_get(v___y_2706_, 2);
lean_inc(v___y_2707_);
lean_inc_ref(v___y_2706_);
lean_inc(v___y_2705_);
lean_inc_ref(v___y_2704_);
lean_inc(v_fst_2709_);
v___x_2742_ = lean_apply_6(v_msg_2702_, v_fst_2709_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, lean_box(0));
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_a_2743_);
lean_dec_ref_known(v___x_2742_, 1);
v___y_2730_ = v_ref_2741_;
v_a_2731_ = v_a_2743_;
goto v___jp_2729_;
}
else
{
lean_object* v___x_2744_; 
lean_dec_ref_known(v___x_2742_, 1);
v___x_2744_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2);
v___y_2730_ = v_ref_2741_;
v_a_2731_ = v___x_2744_;
goto v___jp_2729_;
}
}
v___jp_2745_:
{
if (v_clsEnabled_2700_ == 0)
{
if (v___y_2746_ == 0)
{
lean_object* v___x_2747_; lean_object* v_traceState_2748_; lean_object* v_env_2749_; lean_object* v_nextMacroScope_2750_; lean_object* v_ngen_2751_; lean_object* v_auxDeclNGen_2752_; lean_object* v_cache_2753_; lean_object* v_recordedDeps_2754_; lean_object* v_messages_2755_; lean_object* v_infoState_2756_; lean_object* v_snapshotTasks_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2776_; 
lean_dec(v_snd_2726_);
lean_dec(v_fst_2725_);
lean_dec_ref(v_msg_2702_);
lean_dec_ref(v_tag_2698_);
lean_dec(v_cls_2696_);
v___x_2747_ = lean_st_ref_take(v___y_2707_);
v_traceState_2748_ = lean_ctor_get(v___x_2747_, 4);
v_env_2749_ = lean_ctor_get(v___x_2747_, 0);
v_nextMacroScope_2750_ = lean_ctor_get(v___x_2747_, 1);
v_ngen_2751_ = lean_ctor_get(v___x_2747_, 2);
v_auxDeclNGen_2752_ = lean_ctor_get(v___x_2747_, 3);
v_cache_2753_ = lean_ctor_get(v___x_2747_, 5);
v_recordedDeps_2754_ = lean_ctor_get(v___x_2747_, 6);
v_messages_2755_ = lean_ctor_get(v___x_2747_, 7);
v_infoState_2756_ = lean_ctor_get(v___x_2747_, 8);
v_snapshotTasks_2757_ = lean_ctor_get(v___x_2747_, 9);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2759_ = v___x_2747_;
v_isShared_2760_ = v_isSharedCheck_2776_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_snapshotTasks_2757_);
lean_inc(v_infoState_2756_);
lean_inc(v_messages_2755_);
lean_inc(v_recordedDeps_2754_);
lean_inc(v_cache_2753_);
lean_inc(v_traceState_2748_);
lean_inc(v_auxDeclNGen_2752_);
lean_inc(v_ngen_2751_);
lean_inc(v_nextMacroScope_2750_);
lean_inc(v_env_2749_);
lean_dec(v___x_2747_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2776_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
uint64_t v_tid_2761_; lean_object* v_traces_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2775_; 
v_tid_2761_ = lean_ctor_get_uint64(v_traceState_2748_, sizeof(void*)*1);
v_traces_2762_ = lean_ctor_get(v_traceState_2748_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v_traceState_2748_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2764_ = v_traceState_2748_;
v_isShared_2765_ = v_isSharedCheck_2775_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_traces_2762_);
lean_dec(v_traceState_2748_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2775_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2766_; lean_object* v___x_2768_; 
v___x_2766_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2701_, v_traces_2762_);
lean_dec_ref(v_traces_2762_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v___x_2766_);
v___x_2768_ = v___x_2764_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2766_);
lean_ctor_set_uint64(v_reuseFailAlloc_2774_, sizeof(void*)*1, v_tid_2761_);
v___x_2768_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
lean_object* v___x_2770_; 
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 4, v___x_2768_);
v___x_2770_ = v___x_2759_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_env_2749_);
lean_ctor_set(v_reuseFailAlloc_2773_, 1, v_nextMacroScope_2750_);
lean_ctor_set(v_reuseFailAlloc_2773_, 2, v_ngen_2751_);
lean_ctor_set(v_reuseFailAlloc_2773_, 3, v_auxDeclNGen_2752_);
lean_ctor_set(v_reuseFailAlloc_2773_, 4, v___x_2768_);
lean_ctor_set(v_reuseFailAlloc_2773_, 5, v_cache_2753_);
lean_ctor_set(v_reuseFailAlloc_2773_, 6, v_recordedDeps_2754_);
lean_ctor_set(v_reuseFailAlloc_2773_, 7, v_messages_2755_);
lean_ctor_set(v_reuseFailAlloc_2773_, 8, v_infoState_2756_);
lean_ctor_set(v_reuseFailAlloc_2773_, 9, v_snapshotTasks_2757_);
v___x_2770_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = lean_st_ref_put(v___y_2707_, v___x_2770_);
v___x_2772_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_2709_);
return v___x_2772_;
}
}
}
}
}
else
{
goto v___jp_2740_;
}
}
else
{
goto v___jp_2740_;
}
}
v___jp_2777_:
{
double v___x_2779_; double v___x_2780_; double v___x_2781_; uint8_t v___x_2782_; 
v___x_2779_ = lean_unbox_float(v_snd_2726_);
v___x_2780_ = lean_unbox_float(v_fst_2725_);
v___x_2781_ = lean_float_sub(v___x_2779_, v___x_2780_);
v___x_2782_ = lean_float_decLt(v___y_2778_, v___x_2781_);
v___y_2746_ = v___x_2782_;
goto v___jp_2745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4___boxed(lean_object* v_cls_2793_, lean_object* v_collapsed_2794_, lean_object* v_tag_2795_, lean_object* v_opts_2796_, lean_object* v_clsEnabled_2797_, lean_object* v_oldTraces_2798_, lean_object* v_msg_2799_, lean_object* v_resStartStop_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
uint8_t v_collapsed_boxed_2806_; uint8_t v_clsEnabled_boxed_2807_; lean_object* v_res_2808_; 
v_collapsed_boxed_2806_ = lean_unbox(v_collapsed_2794_);
v_clsEnabled_boxed_2807_ = lean_unbox(v_clsEnabled_2797_);
v_res_2808_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v_cls_2793_, v_collapsed_boxed_2806_, v_tag_2795_, v_opts_2796_, v_clsEnabled_boxed_2807_, v_oldTraces_2798_, v_msg_2799_, v_resStartStop_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec_ref(v_opts_2796_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(lean_object* v_goal_2812_, lean_object* v_tactic_2813_, lean_object* v_allowFailure_2814_, lean_object* v_leavePercentHeartbeats_2815_, uint8_t v_includeStar_2816_, uint8_t v_collectAll_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_){
_start:
{
lean_object* v_toCold_2823_; lean_object* v_options_2824_; lean_object* v_inheritedTraceOptions_2825_; uint8_t v_hasTrace_2826_; lean_object* v___x_2827_; 
v_toCold_2823_ = lean_ctor_get(v_a_2820_, 0);
v_options_2824_ = lean_ctor_get(v_toCold_2823_, 2);
v_inheritedTraceOptions_2825_ = lean_ctor_get(v_toCold_2823_, 11);
v_hasTrace_2826_ = lean_ctor_get_uint8(v_options_2824_, sizeof(void*)*1);
v___x_2827_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
if (v_hasTrace_2826_ == 0)
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___f_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2828_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2820_);
v___x_2829_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___closed__0));
v___x_2830_ = lean_box(v_collectAll_2817_);
v___x_2831_ = lean_box(v_includeStar_2816_);
v___f_2832_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed), 12, 7);
lean_closure_set(v___f_2832_, 0, v_leavePercentHeartbeats_2815_);
lean_closure_set(v___f_2832_, 1, v___x_2829_);
lean_closure_set(v___f_2832_, 2, v_tactic_2813_);
lean_closure_set(v___f_2832_, 3, v_allowFailure_2814_);
lean_closure_set(v___f_2832_, 4, v_goal_2812_);
lean_closure_set(v___f_2832_, 5, v___x_2830_);
lean_closure_set(v___f_2832_, 6, v___x_2831_);
v___x_2833_ = lean_box(0);
v___x_2834_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_2827_, v___x_2828_, v___f_2832_, v___x_2833_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_);
lean_dec_ref(v___x_2828_);
return v___x_2834_;
}
else
{
lean_object* v___f_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; uint8_t v___x_2839_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v_a_2843_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v_a_2858_; 
lean_inc(v_goal_2812_);
v___f_2835_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2835_, 0, v_goal_2812_);
v___x_2836_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_2837_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4));
v___x_2838_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2);
v___x_2839_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2825_, v_options_2824_, v___x_2838_);
if (v___x_2839_ == 0)
{
lean_object* v___x_2922_; uint8_t v___x_2923_; 
v___x_2922_ = l_Lean_trace_profiler;
v___x_2923_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_2824_, v___x_2922_);
if (v___x_2923_ == 0)
{
lean_object* v___x_2924_; uint8_t v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___f_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
lean_dec_ref(v___f_2835_);
v___x_2924_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2820_);
v___x_2925_ = 0;
v___x_2926_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2926_, 0, v___x_2925_);
lean_ctor_set_uint8(v___x_2926_, 1, v_hasTrace_2826_);
lean_ctor_set_uint8(v___x_2926_, 2, v_hasTrace_2826_);
lean_ctor_set_uint8(v___x_2926_, 3, v_hasTrace_2826_);
v___x_2927_ = lean_box(v_collectAll_2817_);
v___x_2928_ = lean_box(v_includeStar_2816_);
v___f_2929_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed), 12, 7);
lean_closure_set(v___f_2929_, 0, v_leavePercentHeartbeats_2815_);
lean_closure_set(v___f_2929_, 1, v___x_2926_);
lean_closure_set(v___f_2929_, 2, v_tactic_2813_);
lean_closure_set(v___f_2929_, 3, v_allowFailure_2814_);
lean_closure_set(v___f_2929_, 4, v_goal_2812_);
lean_closure_set(v___f_2929_, 5, v___x_2927_);
lean_closure_set(v___f_2929_, 6, v___x_2928_);
v___x_2930_ = lean_box(0);
v___x_2931_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_2827_, v___x_2924_, v___f_2929_, v___x_2930_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_);
lean_dec_ref(v___x_2924_);
return v___x_2931_;
}
else
{
goto v___jp_2867_;
}
}
else
{
goto v___jp_2867_;
}
v___jp_2840_:
{
lean_object* v___x_2844_; double v___x_2845_; double v___x_2846_; double v___x_2847_; double v___x_2848_; double v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2844_ = lean_io_mono_nanos_now();
v___x_2845_ = lean_float_of_nat(v___y_2842_);
v___x_2846_ = lean_float_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3);
v___x_2847_ = lean_float_div(v___x_2845_, v___x_2846_);
v___x_2848_ = lean_float_of_nat(v___x_2844_);
v___x_2849_ = lean_float_div(v___x_2848_, v___x_2846_);
v___x_2850_ = lean_box_float(v___x_2847_);
v___x_2851_ = lean_box_float(v___x_2849_);
v___x_2852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2850_);
lean_ctor_set(v___x_2852_, 1, v___x_2851_);
v___x_2853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2853_, 0, v_a_2843_);
lean_ctor_set(v___x_2853_, 1, v___x_2852_);
v___x_2854_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v___x_2836_, v_hasTrace_2826_, v___x_2837_, v_options_2824_, v___x_2839_, v___y_2841_, v___f_2835_, v___x_2853_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_);
return v___x_2854_;
}
v___jp_2855_:
{
lean_object* v___x_2859_; double v___x_2860_; double v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2859_ = lean_io_get_num_heartbeats();
v___x_2860_ = lean_float_of_nat(v___y_2857_);
v___x_2861_ = lean_float_of_nat(v___x_2859_);
v___x_2862_ = lean_box_float(v___x_2860_);
v___x_2863_ = lean_box_float(v___x_2861_);
v___x_2864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2862_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
v___x_2865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2865_, 0, v_a_2858_);
lean_ctor_set(v___x_2865_, 1, v___x_2864_);
v___x_2866_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v___x_2836_, v_hasTrace_2826_, v___x_2837_, v_options_2824_, v___x_2839_, v___y_2856_, v___f_2835_, v___x_2865_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_);
return v___x_2866_;
}
v___jp_2867_:
{
lean_object* v___x_2868_; lean_object* v_a_2869_; lean_object* v___x_2870_; uint8_t v___x_2871_; 
v___x_2868_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v_a_2821_);
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2869_);
lean_dec_ref(v___x_2868_);
v___x_2870_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2871_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_2824_, v___x_2870_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; lean_object* v___x_2873_; uint8_t v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___f_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2872_ = lean_io_mono_nanos_now();
v___x_2873_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2820_);
v___x_2874_ = 0;
v___x_2875_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2875_, 0, v___x_2874_);
lean_ctor_set_uint8(v___x_2875_, 1, v_hasTrace_2826_);
lean_ctor_set_uint8(v___x_2875_, 2, v_hasTrace_2826_);
lean_ctor_set_uint8(v___x_2875_, 3, v_hasTrace_2826_);
v___x_2876_ = lean_box(v_collectAll_2817_);
v___x_2877_ = lean_box(v_includeStar_2816_);
v___f_2878_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed), 12, 7);
lean_closure_set(v___f_2878_, 0, v_leavePercentHeartbeats_2815_);
lean_closure_set(v___f_2878_, 1, v___x_2875_);
lean_closure_set(v___f_2878_, 2, v_tactic_2813_);
lean_closure_set(v___f_2878_, 3, v_allowFailure_2814_);
lean_closure_set(v___f_2878_, 4, v_goal_2812_);
lean_closure_set(v___f_2878_, 5, v___x_2876_);
lean_closure_set(v___f_2878_, 6, v___x_2877_);
v___x_2879_ = lean_box(0);
v___x_2880_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_2827_, v___x_2873_, v___f_2878_, v___x_2879_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_);
lean_dec_ref(v___x_2873_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2888_; 
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2883_ = v___x_2880_;
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v___x_2880_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2886_; 
if (v_isShared_2884_ == 0)
{
lean_ctor_set_tag(v___x_2883_, 1);
v___x_2886_ = v___x_2883_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2881_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
v___y_2841_ = v_a_2869_;
v___y_2842_ = v___x_2872_;
v_a_2843_ = v___x_2886_;
goto v___jp_2840_;
}
}
}
else
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
v_a_2889_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2880_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2880_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
lean_ctor_set_tag(v___x_2891_, 0);
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_a_2889_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
v___y_2841_ = v_a_2869_;
v___y_2842_ = v___x_2872_;
v_a_2843_ = v___x_2894_;
goto v___jp_2840_;
}
}
}
}
else
{
lean_object* v___x_2897_; lean_object* v___x_2898_; uint8_t v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___f_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2897_ = lean_io_get_num_heartbeats();
v___x_2898_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2820_);
v___x_2899_ = 0;
v___x_2900_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_2900_, 0, v___x_2899_);
lean_ctor_set_uint8(v___x_2900_, 1, v___x_2871_);
lean_ctor_set_uint8(v___x_2900_, 2, v___x_2871_);
lean_ctor_set_uint8(v___x_2900_, 3, v___x_2871_);
v___x_2901_ = lean_box(v_collectAll_2817_);
v___x_2902_ = lean_box(v_includeStar_2816_);
v___f_2903_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed), 12, 7);
lean_closure_set(v___f_2903_, 0, v_leavePercentHeartbeats_2815_);
lean_closure_set(v___f_2903_, 1, v___x_2900_);
lean_closure_set(v___f_2903_, 2, v_tactic_2813_);
lean_closure_set(v___f_2903_, 3, v_allowFailure_2814_);
lean_closure_set(v___f_2903_, 4, v_goal_2812_);
lean_closure_set(v___f_2903_, 5, v___x_2901_);
lean_closure_set(v___f_2903_, 6, v___x_2902_);
v___x_2904_ = lean_box(0);
v___x_2905_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_2827_, v___x_2898_, v___f_2903_, v___x_2904_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_);
lean_dec_ref(v___x_2898_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2905_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2905_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
lean_ctor_set_tag(v___x_2908_, 1);
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
v___y_2856_ = v_a_2869_;
v___y_2857_ = v___x_2897_;
v_a_2858_ = v___x_2911_;
goto v___jp_2855_;
}
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
v_a_2914_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2905_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2905_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
lean_ctor_set_tag(v___x_2916_, 0);
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
v___y_2856_ = v_a_2869_;
v___y_2857_ = v___x_2897_;
v_a_2858_ = v___x_2919_;
goto v___jp_2855_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___boxed(lean_object* v_goal_2932_, lean_object* v_tactic_2933_, lean_object* v_allowFailure_2934_, lean_object* v_leavePercentHeartbeats_2935_, lean_object* v_includeStar_2936_, lean_object* v_collectAll_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_){
_start:
{
uint8_t v_includeStar_boxed_2943_; uint8_t v_collectAll_boxed_2944_; lean_object* v_res_2945_; 
v_includeStar_boxed_2943_ = lean_unbox(v_includeStar_2936_);
v_collectAll_boxed_2944_ = lean_unbox(v_collectAll_2937_);
v_res_2945_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(v_goal_2932_, v_tactic_2933_, v_allowFailure_2934_, v_leavePercentHeartbeats_2935_, v_includeStar_boxed_2943_, v_collectAll_boxed_2944_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearch(lean_object* v_goal_2946_, lean_object* v_tactic_2947_, lean_object* v_allowFailure_2948_, lean_object* v_leavePercentHeartbeats_2949_, uint8_t v_includeStar_2950_, uint8_t v_collectAll_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_){
_start:
{
lean_object* v___x_2957_; 
v___x_2957_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(v_goal_2946_, v_tactic_2947_, v_allowFailure_2948_, v_leavePercentHeartbeats_2949_, v_includeStar_2950_, v_collectAll_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearch___boxed(lean_object* v_goal_2958_, lean_object* v_tactic_2959_, lean_object* v_allowFailure_2960_, lean_object* v_leavePercentHeartbeats_2961_, lean_object* v_includeStar_2962_, lean_object* v_collectAll_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_){
_start:
{
uint8_t v_includeStar_boxed_2969_; uint8_t v_collectAll_boxed_2970_; lean_object* v_res_2971_; 
v_includeStar_boxed_2969_ = lean_unbox(v_includeStar_2962_);
v_collectAll_boxed_2970_ = lean_unbox(v_collectAll_2963_);
v_res_2971_ = l_Lean_Meta_LibrarySearch_librarySearch(v_goal_2958_, v_tactic_2959_, v_allowFailure_2960_, v_leavePercentHeartbeats_2961_, v_includeStar_boxed_2969_, v_collectAll_boxed_2970_, v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_);
lean_dec(v_a_2967_);
lean_dec_ref(v_a_2966_);
lean_dec(v_a_2965_);
lean_dec_ref(v_a_2964_);
return v_res_2971_;
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
