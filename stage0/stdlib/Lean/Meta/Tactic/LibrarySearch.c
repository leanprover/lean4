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
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx___boxed(lean_object*);
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
lean_object* v___x_405_; lean_object* v_env_406_; lean_object* v___x_407_; lean_object* v_toCold_408_; lean_object* v_mctx_409_; lean_object* v_lctx_410_; lean_object* v_options_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_405_ = lean_st_ref_get(v___y_403_);
v_env_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc_ref(v_env_406_);
lean_dec(v___x_405_);
v___x_407_ = lean_st_ref_get(v___y_401_);
v_toCold_408_ = lean_ctor_get(v___y_402_, 0);
v_mctx_409_ = lean_ctor_get(v___x_407_, 0);
lean_inc_ref(v_mctx_409_);
lean_dec(v___x_407_);
v_lctx_410_ = lean_ctor_get(v___y_400_, 2);
v_options_411_ = lean_ctor_get(v_toCold_408_, 2);
lean_inc_ref(v_options_411_);
lean_inc_ref(v_lctx_410_);
v___x_412_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_412_, 0, v_env_406_);
lean_ctor_set(v___x_412_, 1, v_mctx_409_);
lean_ctor_set(v___x_412_, 2, v_lctx_410_);
lean_ctor_set(v___x_412_, 3, v_options_411_);
v___x_413_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v_msgData_399_);
v___x_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0___boxed(lean_object* v_msgData_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msgData_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(lean_object* v_msg_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_ref_428_; lean_object* v___x_429_; lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_438_; 
v_ref_428_ = lean_ctor_get(v___y_425_, 2);
v___x_429_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msg_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
v_a_430_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_438_ == 0)
{
v___x_432_ = v___x_429_;
v_isShared_433_ = v_isSharedCheck_438_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_429_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_438_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; lean_object* v___x_436_; 
lean_inc(v_ref_428_);
v___x_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_434_, 0, v_ref_428_);
lean_ctor_set(v___x_434_, 1, v_a_430_);
if (v_isShared_433_ == 0)
{
lean_ctor_set_tag(v___x_432_, 1);
lean_ctor_set(v___x_432_, 0, v___x_434_);
v___x_436_ = v___x_432_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_434_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg___boxed(lean_object* v_msg_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v_msg_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
return v_res_445_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__0));
v___x_448_ = l_Lean_stringToMessageData(v___x_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__2(lean_object* v_x_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1);
v___x_456_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_455_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___lam__2___boxed(lean_object* v_x_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Meta_LibrarySearch_solveByElim___lam__2(v_x_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v_x_457_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim(lean_object* v_required_471_, uint8_t v_exfalso_472_, lean_object* v_goals_473_, lean_object* v_maxDepth_474_, uint8_t v_grind_475_, uint8_t v_try_x3f_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_){
_start:
{
lean_object* v___x_482_; uint8_t v_transparency_483_; lean_object* v___f_484_; lean_object* v___f_485_; lean_object* v___f_486_; uint8_t v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; lean_object* v___y_491_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_482_ = l_Lean_Meta_Context_config(v_a_477_);
v_transparency_483_ = lean_ctor_get_uint8(v___x_482_, 9);
lean_dec_ref(v___x_482_);
v___f_484_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__0));
v___f_485_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__1));
v___f_486_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__2));
v___x_487_ = 1;
v___x_488_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_488_, 0, v_maxDepth_474_);
lean_ctor_set(v___x_488_, 1, v___f_484_);
lean_ctor_set(v___x_488_, 2, v___f_485_);
lean_ctor_set(v___x_488_, 3, v___f_486_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*4, v___x_487_);
v___x_489_ = 0;
v___x_510_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_grindDischarger___closed__3));
v___x_511_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_511_, 0, v___x_488_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
lean_ctor_set_uint8(v___x_511_, sizeof(void*)*2, v_transparency_483_);
lean_ctor_set_uint8(v___x_511_, sizeof(void*)*2 + 1, v___x_487_);
lean_ctor_set_uint8(v___x_511_, sizeof(void*)*2 + 2, v_exfalso_472_);
v___x_512_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_512_, 0, v___x_511_);
lean_ctor_set_uint8(v___x_512_, sizeof(void*)*1, v___x_487_);
lean_ctor_set_uint8(v___x_512_, sizeof(void*)*1 + 1, v___x_487_);
lean_ctor_set_uint8(v___x_512_, sizeof(void*)*1 + 2, v___x_489_);
lean_ctor_set_uint8(v___x_512_, sizeof(void*)*1 + 3, v___x_489_);
if (v_try_x3f_476_ == 0)
{
if (v_grind_475_ == 0)
{
v___y_491_ = v___x_512_;
goto v___jp_490_;
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__4));
v___x_514_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v___x_512_, v___x_513_);
v___y_491_ = v___x_514_;
goto v___jp_490_;
}
}
else
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__5));
v___x_516_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(v___x_512_, v___x_515_);
v___y_491_ = v___x_516_;
goto v___jp_490_;
}
v___jp_490_:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_492_ = lean_box(0);
v___x_493_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_solveByElim___closed__3));
v___x_494_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v___x_489_, v___x_489_, v___x_492_, v___x_492_, v___x_493_, v_a_477_, v_a_478_, v_a_479_, v_a_480_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_a_495_; lean_object* v_fst_496_; lean_object* v_snd_497_; uint8_t v___x_498_; 
v_a_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_a_495_);
lean_dec_ref_known(v___x_494_, 1);
v_fst_496_ = lean_ctor_get(v_a_495_, 0);
lean_inc(v_fst_496_);
v_snd_497_ = lean_ctor_get(v_a_495_, 1);
lean_inc(v_snd_497_);
lean_dec(v_a_495_);
v___x_498_ = l_List_isEmpty___redArg(v_required_471_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(v___y_491_, v_required_471_);
v___x_500_ = l_Lean_Meta_SolveByElim_solveByElim(v___x_499_, v_fst_496_, v_snd_497_, v_goals_473_, v_a_477_, v_a_478_, v_a_479_, v_a_480_);
return v___x_500_;
}
else
{
lean_object* v___x_501_; 
lean_dec(v_required_471_);
v___x_501_ = l_Lean_Meta_SolveByElim_solveByElim(v___y_491_, v_fst_496_, v_snd_497_, v_goals_473_, v_a_477_, v_a_478_, v_a_479_, v_a_480_);
return v___x_501_;
}
}
else
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
lean_dec_ref(v___y_491_);
lean_dec(v_goals_473_);
lean_dec(v_required_471_);
v_a_502_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_494_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_494_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_solveByElim___boxed(lean_object* v_required_517_, lean_object* v_exfalso_518_, lean_object* v_goals_519_, lean_object* v_maxDepth_520_, lean_object* v_grind_521_, lean_object* v_try_x3f_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
uint8_t v_exfalso_boxed_528_; uint8_t v_grind_boxed_529_; uint8_t v_try_x3f_boxed_530_; lean_object* v_res_531_; 
v_exfalso_boxed_528_ = lean_unbox(v_exfalso_518_);
v_grind_boxed_529_ = lean_unbox(v_grind_521_);
v_try_x3f_boxed_530_ = lean_unbox(v_try_x3f_522_);
v_res_531_ = l_Lean_Meta_LibrarySearch_solveByElim(v_required_517_, v_exfalso_boxed_528_, v_goals_519_, v_maxDepth_520_, v_grind_boxed_529_, v_try_x3f_boxed_530_, v_a_523_, v_a_524_, v_a_525_, v_a_526_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0(lean_object* v_00_u03b1_532_, lean_object* v_msg_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v_msg_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___boxed(lean_object* v_00_u03b1_540_, lean_object* v_msg_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0(v_00_u03b1_540_, v_msg_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(uint8_t v_x_548_){
_start:
{
switch(v_x_548_)
{
case 0:
{
lean_object* v___x_549_; 
v___x_549_ = lean_unsigned_to_nat(0u);
return v___x_549_;
}
case 1:
{
lean_object* v___x_550_; 
v___x_550_ = lean_unsigned_to_nat(1u);
return v___x_550_;
}
default: 
{
lean_object* v___x_551_; 
v___x_551_ = lean_unsigned_to_nat(2u);
return v___x_551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx___boxed(lean_object* v_x_552_){
_start:
{
uint8_t v_x_boxed_553_; lean_object* v_res_554_; 
v_x_boxed_553_ = lean_unbox(v_x_552_);
v_res_554_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_x_boxed_553_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg(lean_object* v_k_555_){
_start:
{
lean_inc(v_k_555_);
return v_k_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg___boxed(lean_object* v_k_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___redArg(v_k_556_);
lean_dec(v_k_556_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim(lean_object* v_motive_558_, lean_object* v_ctorIdx_559_, uint8_t v_t_560_, lean_object* v_h_561_, lean_object* v_k_562_){
_start:
{
lean_inc(v_k_562_);
return v_k_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ctorElim___boxed(lean_object* v_motive_563_, lean_object* v_ctorIdx_564_, lean_object* v_t_565_, lean_object* v_h_566_, lean_object* v_k_567_){
_start:
{
uint8_t v_t_boxed_568_; lean_object* v_res_569_; 
v_t_boxed_568_ = lean_unbox(v_t_565_);
v_res_569_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorElim(v_motive_563_, v_ctorIdx_564_, v_t_boxed_568_, v_h_566_, v_k_567_);
lean_dec(v_k_567_);
lean_dec(v_ctorIdx_564_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg(lean_object* v_none_570_){
_start:
{
lean_inc(v_none_570_);
return v_none_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg___boxed(lean_object* v_none_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_Meta_LibrarySearch_DeclMod_none_elim___redArg(v_none_571_);
lean_dec(v_none_571_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim(lean_object* v_motive_573_, uint8_t v_t_574_, lean_object* v_h_575_, lean_object* v_none_576_){
_start:
{
lean_inc(v_none_576_);
return v_none_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_none_elim___boxed(lean_object* v_motive_577_, lean_object* v_t_578_, lean_object* v_h_579_, lean_object* v_none_580_){
_start:
{
uint8_t v_t_boxed_581_; lean_object* v_res_582_; 
v_t_boxed_581_ = lean_unbox(v_t_578_);
v_res_582_ = l_Lean_Meta_LibrarySearch_DeclMod_none_elim(v_motive_577_, v_t_boxed_581_, v_h_579_, v_none_580_);
lean_dec(v_none_580_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg(lean_object* v_mp_583_){
_start:
{
lean_inc(v_mp_583_);
return v_mp_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg___boxed(lean_object* v_mp_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___redArg(v_mp_584_);
lean_dec(v_mp_584_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim(lean_object* v_motive_586_, uint8_t v_t_587_, lean_object* v_h_588_, lean_object* v_mp_589_){
_start:
{
lean_inc(v_mp_589_);
return v_mp_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mp_elim___boxed(lean_object* v_motive_590_, lean_object* v_t_591_, lean_object* v_h_592_, lean_object* v_mp_593_){
_start:
{
uint8_t v_t_boxed_594_; lean_object* v_res_595_; 
v_t_boxed_594_ = lean_unbox(v_t_591_);
v_res_595_ = l_Lean_Meta_LibrarySearch_DeclMod_mp_elim(v_motive_590_, v_t_boxed_594_, v_h_592_, v_mp_593_);
lean_dec(v_mp_593_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg(lean_object* v_mpr_596_){
_start:
{
lean_inc(v_mpr_596_);
return v_mpr_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg___boxed(lean_object* v_mpr_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___redArg(v_mpr_597_);
lean_dec(v_mpr_597_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim(lean_object* v_motive_599_, uint8_t v_t_600_, lean_object* v_h_601_, lean_object* v_mpr_602_){
_start:
{
lean_inc(v_mpr_602_);
return v_mpr_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim___boxed(lean_object* v_motive_603_, lean_object* v_t_604_, lean_object* v_h_605_, lean_object* v_mpr_606_){
_start:
{
uint8_t v_t_boxed_607_; lean_object* v_res_608_; 
v_t_boxed_607_ = lean_unbox(v_t_604_);
v_res_608_ = l_Lean_Meta_LibrarySearch_DeclMod_mpr_elim(v_motive_603_, v_t_boxed_607_, v_h_605_, v_mpr_606_);
lean_dec(v_mpr_606_);
return v_res_608_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_DeclMod_ofNat(lean_object* v_n_609_){
_start:
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = lean_unsigned_to_nat(0u);
v___x_611_ = lean_nat_dec_le(v_n_609_, v___x_610_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = lean_unsigned_to_nat(1u);
v___x_613_ = lean_nat_dec_le(v_n_609_, v___x_612_);
if (v___x_613_ == 0)
{
uint8_t v___x_614_; 
v___x_614_ = 2;
return v___x_614_;
}
else
{
uint8_t v___x_615_; 
v___x_615_ = 1;
return v___x_615_;
}
}
else
{
uint8_t v___x_616_; 
v___x_616_ = 0;
return v___x_616_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_DeclMod_ofNat___boxed(lean_object* v_n_617_){
_start:
{
uint8_t v_res_618_; lean_object* v_r_619_; 
v_res_618_ = l_Lean_Meta_LibrarySearch_DeclMod_ofNat(v_n_617_);
lean_dec(v_n_617_);
v_r_619_ = lean_box(v_res_618_);
return v_r_619_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod(uint8_t v_x_620_, uint8_t v_y_621_){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_622_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_x_620_);
v___x_623_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_y_621_);
v___x_624_ = lean_nat_dec_eq(v___x_622_, v___x_623_);
lean_dec(v___x_623_);
lean_dec(v___x_622_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod___boxed(lean_object* v_x_625_, lean_object* v_y_626_){
_start:
{
uint8_t v_x_20__boxed_627_; uint8_t v_y_21__boxed_628_; uint8_t v_res_629_; lean_object* v_r_630_; 
v_x_20__boxed_627_ = lean_unbox(v_x_625_);
v_y_21__boxed_628_ = lean_unbox(v_y_626_);
v_res_629_ = l_Lean_Meta_LibrarySearch_instDecidableEqDeclMod(v_x_20__boxed_627_, v_y_21__boxed_628_);
v_r_630_ = lean_box(v_res_629_);
return v_r_630_;
}
}
static uint8_t _init_l_Lean_Meta_LibrarySearch_instInhabitedDeclMod_default(void){
_start:
{
uint8_t v___x_631_; 
v___x_631_ = 0;
return v___x_631_;
}
}
static uint8_t _init_l_Lean_Meta_LibrarySearch_instInhabitedDeclMod(void){
_start:
{
uint8_t v___x_632_; 
v___x_632_ = 0;
return v___x_632_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord(uint8_t v_x_633_, uint8_t v_y_634_){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_635_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_x_633_);
v___x_636_ = l_Lean_Meta_LibrarySearch_DeclMod_ctorIdx(v_y_634_);
v___x_637_ = lean_nat_dec_lt(v___x_635_, v___x_636_);
if (v___x_637_ == 0)
{
uint8_t v___x_638_; 
v___x_638_ = lean_nat_dec_eq(v___x_635_, v___x_636_);
lean_dec(v___x_636_);
lean_dec(v___x_635_);
if (v___x_638_ == 0)
{
uint8_t v___x_639_; 
v___x_639_ = 2;
return v___x_639_;
}
else
{
uint8_t v___x_640_; 
v___x_640_ = 1;
return v___x_640_;
}
}
else
{
uint8_t v___x_641_; 
lean_dec(v___x_636_);
lean_dec(v___x_635_);
v___x_641_ = 0;
return v___x_641_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord___boxed(lean_object* v_x_642_, lean_object* v_y_643_){
_start:
{
uint8_t v_x_30__boxed_644_; uint8_t v_y_31__boxed_645_; uint8_t v_res_646_; lean_object* v_r_647_; 
v_x_30__boxed_644_ = lean_unbox(v_x_642_);
v_y_31__boxed_645_ = lean_unbox(v_y_643_);
v_res_646_ = l_Lean_Meta_LibrarySearch_instOrdDeclMod_ord(v_x_30__boxed_644_, v_y_31__boxed_645_);
v_r_647_ = lean_box(v_res_646_);
return v_r_647_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash(uint8_t v_x_650_){
_start:
{
switch(v_x_650_)
{
case 0:
{
uint64_t v___x_651_; 
v___x_651_ = 0ULL;
return v___x_651_;
}
case 1:
{
uint64_t v___x_652_; 
v___x_652_ = 1ULL;
return v___x_652_;
}
default: 
{
uint64_t v___x_653_; 
v___x_653_ = 2ULL;
return v___x_653_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash___boxed(lean_object* v_x_654_){
_start:
{
uint8_t v_x_40__boxed_655_; uint64_t v_res_656_; lean_object* v_r_657_; 
v_x_40__boxed_655_ = lean_unbox(v_x_654_);
v_res_656_ = l_Lean_Meta_LibrarySearch_instHashableDeclMod_hash(v_x_40__boxed_655_);
v_r_657_ = lean_box_uint64(v_res_656_);
return v_r_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0(lean_object* v_k_660_, lean_object* v_b_661_, lean_object* v_c_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v___x_668_; 
lean_inc(v___y_666_);
lean_inc_ref(v___y_665_);
lean_inc(v___y_664_);
lean_inc_ref(v___y_663_);
v___x_668_ = lean_apply_7(v_k_660_, v_b_661_, v_c_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, lean_box(0));
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0___boxed(lean_object* v_k_669_, lean_object* v_b_670_, lean_object* v_c_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0(v_k_669_, v_b_670_, v_c_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(lean_object* v_type_678_, lean_object* v_k_679_, uint8_t v_cleanupAnnotations_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v___f_686_; uint8_t v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___f_686_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_686_, 0, v_k_679_);
v___x_687_ = 0;
v___x_688_ = lean_box(0);
v___x_689_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_687_, v___x_688_, v_type_678_, v___f_686_, v_cleanupAnnotations_680_, v___x_687_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
v_a_698_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_689_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_689_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg___boxed(lean_object* v_type_706_, lean_object* v_k_707_, lean_object* v_cleanupAnnotations_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_714_; lean_object* v_res_715_; 
v_cleanupAnnotations_boxed_714_ = lean_unbox(v_cleanupAnnotations_708_);
v_res_715_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_706_, v_k_707_, v_cleanupAnnotations_boxed_714_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0(lean_object* v_00_u03b1_716_, lean_object* v_type_717_, lean_object* v_k_718_, uint8_t v_cleanupAnnotations_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_717_, v_k_718_, v_cleanupAnnotations_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___boxed(lean_object* v_00_u03b1_726_, lean_object* v_type_727_, lean_object* v_k_728_, lean_object* v_cleanupAnnotations_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_735_; lean_object* v_res_736_; 
v_cleanupAnnotations_boxed_735_ = lean_unbox(v_cleanupAnnotations_729_);
v_res_736_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0(v_00_u03b1_726_, v_type_727_, v_k_728_, v_cleanupAnnotations_boxed_735_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0(lean_object* v_name_743_, lean_object* v_x_744_, lean_object* v_type_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
uint8_t v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_751_ = 0;
v___x_752_ = lean_box(v___x_751_);
lean_inc(v_name_743_);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v_name_743_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v_type_745_, v___x_753_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_804_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_804_ == 0)
{
v___x_757_ = v___x_754_;
v_isShared_758_ = v_isSharedCheck_804_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_754_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_804_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v_key_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
v_key_759_ = lean_ctor_get(v_a_755_, 0);
v___x_760_ = lean_unsigned_to_nat(1u);
v___x_761_ = lean_mk_empty_array_with_capacity(v___x_760_);
lean_inc(v_a_755_);
v___x_762_ = lean_array_push(v___x_761_, v_a_755_);
v___x_763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___closed__2));
v___x_764_ = l_Lean_Meta_LazyDiscrTree_instBEqKey_beq(v_key_759_, v___x_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_766_; 
lean_dec(v_a_755_);
lean_dec(v_name_743_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v___x_762_);
v___x_766_ = v___x_757_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_762_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
else
{
lean_object* v___x_768_; uint8_t v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
lean_del_object(v___x_757_);
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = 1;
v___x_770_ = lean_box(v___x_769_);
lean_inc(v_name_743_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v_name_743_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
lean_inc(v_a_755_);
v___x_772_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_a_755_, v___x_768_, v___x_771_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v___x_774_; uint8_t v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_773_);
lean_dec_ref_known(v___x_772_, 1);
v___x_774_ = lean_array_push(v___x_762_, v_a_773_);
v___x_775_ = 2;
v___x_776_ = lean_box(v___x_775_);
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v_name_743_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = l_Lean_Meta_LazyDiscrTree_InitEntry_mkSubEntry___redArg(v_a_755_, v___x_760_, v___x_777_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_787_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_787_ == 0)
{
v___x_781_ = v___x_778_;
v_isShared_782_ = v_isSharedCheck_787_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_778_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_787_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_783_ = lean_array_push(v___x_774_, v_a_779_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_783_);
v___x_785_ = v___x_781_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec_ref(v___x_774_);
v_a_788_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_778_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_778_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec_ref(v___x_762_);
lean_dec(v_a_755_);
lean_dec(v_name_743_);
v_a_796_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_772_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_772_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_dec(v_name_743_);
v_a_805_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_754_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_754_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___boxed(lean_object* v_name_813_, lean_object* v_x_814_, lean_object* v_type_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0(v_name_813_, v_x_814_, v_type_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec_ref(v_x_814_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport(lean_object* v_name_824_, lean_object* v_c_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v___f_831_; lean_object* v___x_832_; lean_object* v_env_833_; uint8_t v___x_834_; 
lean_inc_n(v_name_824_, 2);
v___f_831_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___lam__0___boxed), 8, 1);
lean_closure_set(v___f_831_, 0, v_name_824_);
v___x_832_ = lean_st_ref_get(v_a_829_);
v_env_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc_ref(v_env_833_);
lean_dec(v___x_832_);
v___x_834_ = l_Lean_Linter_isDeprecated(v_env_833_, v_name_824_);
if (v___x_834_ == 0)
{
uint8_t v___x_835_; 
v___x_835_ = l_Lean_Name_isMetaprogramming(v_name_824_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; lean_object* v_type_837_; lean_object* v___x_838_; 
v___x_836_ = l_Lean_AsyncConstantInfo_toConstantVal(v_c_825_);
v_type_837_ = lean_ctor_get(v___x_836_, 2);
lean_inc_ref(v_type_837_);
lean_dec_ref(v___x_836_);
v___x_838_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport_spec__0___redArg(v_type_837_, v___f_831_, v___x_835_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
return v___x_838_;
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec_ref(v___f_831_);
lean_dec_ref(v_c_825_);
v___x_839_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0));
v___x_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
return v___x_840_;
}
}
else
{
lean_object* v___x_841_; lean_object* v___x_842_; 
lean_dec_ref(v___f_831_);
lean_dec_ref(v_c_825_);
lean_dec(v_name_824_);
v___x_841_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___closed__0));
v___x_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
return v___x_842_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport___boxed(lean_object* v_name_843_, lean_object* v_c_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_addImport(v_name_843_, v_c_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_858108106____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_852_ = lean_box(0);
v___x_853_ = lean_st_mk_ref(v___x_852_);
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_858108106____hygCtx___hyg_2____boxed(lean_object* v_a_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_858108106____hygCtx___hyg_2_();
return v_res_856_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_constantsPerImportTask(void){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = lean_unsigned_to_nat(6500u);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2955776588____hygCtx___hyg_2_(){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2955776588____hygCtx___hyg_2____boxed(lean_object* v_a_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_2955776588____hygCtx___hyg_2_();
return v_res_888_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1(void){
_start:
{
lean_object* v_droppedRef_890_; lean_object* v___x_891_; 
v_droppedRef_890_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt;
v___x_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_891_, 0, v_droppedRef_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_libSearchFindDecls(lean_object* v_ty_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_898_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_ext;
v___x_899_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__0));
v___x_900_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_droppedKeys));
v___x_901_ = lean_unsigned_to_nat(6500u);
v___x_902_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1, &l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1_once, _init_l_Lean_Meta_LibrarySearch_libSearchFindDecls___closed__1);
v___x_903_ = l_Lean_Meta_LazyDiscrTree_findMatches___redArg(v___x_898_, v___x_899_, v___x_900_, v___x_901_, v___x_902_, v_ty_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_libSearchFindDecls___boxed(lean_object* v_ty_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_Meta_LibrarySearch_libSearchFindDecls(v_ty_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
return v_res_910_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_914_ = lean_box(0);
v___x_915_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_getStarLemmas___closed__1));
v___x_916_ = l_Lean_mkConst(v___x_915_, v___x_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_getStarLemmas(lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_ref_924_; lean_object* v___x_925_; 
v_ref_924_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_starLemmasExt;
v___x_925_ = lean_st_ref_get(v_ref_924_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2, &l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2_once, _init_l_Lean_Meta_LibrarySearch_getStarLemmas___closed__2);
v___x_927_ = l_Lean_Meta_LibrarySearch_libSearchFindDecls(v___x_926_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_940_; 
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_940_ == 0)
{
lean_object* v_unused_941_; 
v_unused_941_ = lean_ctor_get(v___x_927_, 0);
lean_dec(v_unused_941_);
v___x_929_ = v___x_927_;
v_isShared_930_ = v_isSharedCheck_940_;
goto v_resetjp_928_;
}
else
{
lean_dec(v___x_927_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_940_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; 
v___x_931_ = lean_st_ref_get(v_ref_924_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_932_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_getStarLemmas___closed__3));
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_932_);
v___x_934_ = v___x_929_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
else
{
lean_object* v_val_936_; lean_object* v___x_938_; 
v_val_936_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_val_936_);
lean_dec_ref_known(v___x_931_, 1);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v_val_936_);
v___x_938_ = v___x_929_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_val_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
else
{
return v___x_927_;
}
}
else
{
lean_object* v_val_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
v_val_942_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_925_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_val_942_);
lean_dec(v___x_925_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
lean_ctor_set_tag(v___x_944_, 0);
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_val_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_getStarLemmas___boxed(lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v_a_950_, v_a_951_, v_a_952_, v_a_953_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0(uint8_t v___x_956_, lean_object* v___x_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
if (v___x_956_ == 0)
{
lean_object* v___x_963_; 
v___x_963_ = l_Lean_getRemainingHeartbeats___redArg(v___y_960_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_973_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_973_ == 0)
{
v___x_966_ = v___x_963_;
v_isShared_967_ = v_isSharedCheck_973_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_973_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
uint8_t v___x_968_; lean_object* v___x_969_; lean_object* v___x_971_; 
v___x_968_ = lean_nat_dec_lt(v_a_964_, v___x_957_);
lean_dec(v_a_964_);
v___x_969_ = lean_box(v___x_968_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_969_);
v___x_971_ = v___x_966_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
v_a_974_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_963_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_963_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
else
{
uint8_t v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_982_ = 0;
v___x_983_ = lean_box(v___x_982_);
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0___boxed(lean_object* v___x_985_, lean_object* v___x_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
uint8_t v___x_649__boxed_992_; lean_object* v_res_993_; 
v___x_649__boxed_992_ = lean_unbox(v___x_985_);
v_res_993_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0(v___x_649__boxed_992_, v___x_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___x_986_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(lean_object* v_leavePercent_994_, lean_object* v_a_995_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Lean_getMaxHeartbeats___redArg(v_a_995_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_999_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref_known(v___x_997_, 1);
v___x_999_ = l_Lean_getRemainingHeartbeats___redArg(v_a_995_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1014_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1014_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1014_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___y_1010_; lean_object* v___x_1012_; 
v___x_1004_ = lean_nat_mul(v_a_1000_, v_leavePercent_994_);
lean_dec(v_a_1000_);
v___x_1005_ = lean_unsigned_to_nat(100u);
v___x_1006_ = lean_nat_div(v___x_1004_, v___x_1005_);
lean_dec(v___x_1004_);
v___x_1007_ = lean_unsigned_to_nat(0u);
v___x_1008_ = lean_nat_dec_eq(v_a_998_, v___x_1007_);
lean_dec(v_a_998_);
v___x_1009_ = lean_box(v___x_1008_);
v___y_1010_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___y_1010_, 0, v___x_1009_);
lean_closure_set(v___y_1010_, 1, v___x_1006_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v___y_1010_);
v___x_1012_ = v___x_1002_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___y_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec(v_a_998_);
v_a_1015_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_999_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_999_);
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
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
v_a_1023_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_997_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_997_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg___boxed(lean_object* v_leavePercent_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercent_1031_, v_a_1032_);
lean_dec_ref(v_a_1032_);
lean_dec(v_leavePercent_1031_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck(lean_object* v_leavePercent_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercent_1035_, v_a_1038_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___boxed(lean_object* v_leavePercent_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck(v_leavePercent_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_leavePercent_1042_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(lean_object* v_upperBound_1049_, lean_object* v_x_1050_, lean_object* v_f_1051_, lean_object* v_y_1052_, lean_object* v_g_1053_, lean_object* v_a_1054_, lean_object* v_b_1055_){
_start:
{
uint8_t v___x_1056_; 
v___x_1056_ = lean_nat_dec_lt(v_a_1054_, v_upperBound_1049_);
if (v___x_1056_ == 0)
{
lean_dec(v_a_1054_);
lean_dec(v_g_1053_);
lean_dec(v_f_1051_);
return v_b_1055_;
}
else
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1057_ = lean_array_fget_borrowed(v_x_1050_, v_a_1054_);
lean_inc(v_f_1051_);
lean_inc(v___x_1057_);
v___x_1058_ = lean_apply_1(v_f_1051_, v___x_1057_);
v___x_1059_ = lean_array_push(v_b_1055_, v___x_1058_);
v___x_1060_ = lean_array_fget_borrowed(v_y_1052_, v_a_1054_);
lean_inc(v_g_1053_);
lean_inc(v___x_1060_);
v___x_1061_ = lean_apply_1(v_g_1053_, v___x_1060_);
v___x_1062_ = lean_array_push(v___x_1059_, v___x_1061_);
v___x_1063_ = lean_unsigned_to_nat(1u);
v___x_1064_ = lean_nat_add(v_a_1054_, v___x_1063_);
lean_dec(v_a_1054_);
v_a_1054_ = v___x_1064_;
v_b_1055_ = v___x_1062_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg___boxed(lean_object* v_upperBound_1066_, lean_object* v_x_1067_, lean_object* v_f_1068_, lean_object* v_y_1069_, lean_object* v_g_1070_, lean_object* v_a_1071_, lean_object* v_b_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v_upperBound_1066_, v_x_1067_, v_f_1068_, v_y_1069_, v_g_1070_, v_a_1071_, v_b_1072_);
lean_dec_ref(v_y_1069_);
lean_dec_ref(v_x_1067_);
lean_dec(v_upperBound_1066_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(lean_object* v_g_1074_, size_t v_sz_1075_, size_t v_i_1076_, lean_object* v_bs_1077_){
_start:
{
uint8_t v___x_1078_; 
v___x_1078_ = lean_usize_dec_lt(v_i_1076_, v_sz_1075_);
if (v___x_1078_ == 0)
{
lean_dec(v_g_1074_);
return v_bs_1077_;
}
else
{
lean_object* v_v_1079_; lean_object* v___x_1080_; lean_object* v_bs_x27_1081_; lean_object* v___x_1082_; size_t v___x_1083_; size_t v___x_1084_; lean_object* v___x_1085_; 
v_v_1079_ = lean_array_uget(v_bs_1077_, v_i_1076_);
v___x_1080_ = lean_unsigned_to_nat(0u);
v_bs_x27_1081_ = lean_array_uset(v_bs_1077_, v_i_1076_, v___x_1080_);
lean_inc(v_g_1074_);
v___x_1082_ = lean_apply_1(v_g_1074_, v_v_1079_);
v___x_1083_ = ((size_t)1ULL);
v___x_1084_ = lean_usize_add(v_i_1076_, v___x_1083_);
v___x_1085_ = lean_array_uset(v_bs_x27_1081_, v_i_1076_, v___x_1082_);
v_i_1076_ = v___x_1084_;
v_bs_1077_ = v___x_1085_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg___boxed(lean_object* v_g_1087_, lean_object* v_sz_1088_, lean_object* v_i_1089_, lean_object* v_bs_1090_){
_start:
{
size_t v_sz_boxed_1091_; size_t v_i_boxed_1092_; lean_object* v_res_1093_; 
v_sz_boxed_1091_ = lean_unbox_usize(v_sz_1088_);
lean_dec(v_sz_1088_);
v_i_boxed_1092_ = lean_unbox_usize(v_i_1089_);
lean_dec(v_i_1089_);
v_res_1093_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1087_, v_sz_boxed_1091_, v_i_boxed_1092_, v_bs_1090_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___redArg(lean_object* v_f_1094_, lean_object* v_x_1095_, lean_object* v_g_1096_, lean_object* v_y_1097_){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v_res_1101_; lean_object* v___y_1103_; uint8_t v___x_1117_; 
v___x_1098_ = lean_array_get_size(v_x_1095_);
v___x_1099_ = lean_array_get_size(v_y_1097_);
v___x_1100_ = lean_nat_add(v___x_1098_, v___x_1099_);
v_res_1101_ = lean_mk_empty_array_with_capacity(v___x_1100_);
lean_dec(v___x_1100_);
v___x_1117_ = lean_nat_dec_le(v___x_1098_, v___x_1099_);
if (v___x_1117_ == 0)
{
v___y_1103_ = v___x_1099_;
goto v___jp_1102_;
}
else
{
v___y_1103_ = v___x_1098_;
goto v___jp_1102_;
}
v___jp_1102_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1104_ = lean_unsigned_to_nat(0u);
lean_inc(v_g_1096_);
lean_inc(v_f_1094_);
v___x_1105_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v___y_1103_, v_x_1095_, v_f_1094_, v_y_1097_, v_g_1096_, v___x_1104_, v_res_1101_);
v___x_1106_ = lean_nat_dec_lt(v___y_1103_, v___x_1098_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; size_t v_sz_1108_; size_t v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
lean_dec(v_f_1094_);
v___x_1107_ = l_Array_extract___redArg(v_y_1097_, v___y_1103_, v___x_1099_);
v_sz_1108_ = lean_array_size(v___x_1107_);
v___x_1109_ = ((size_t)0ULL);
v___x_1110_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1096_, v_sz_1108_, v___x_1109_, v___x_1107_);
v___x_1111_ = l_Array_append___redArg(v___x_1105_, v___x_1110_);
lean_dec_ref(v___x_1110_);
return v___x_1111_;
}
else
{
lean_object* v___x_1112_; size_t v_sz_1113_; size_t v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_dec(v_g_1096_);
v___x_1112_ = l_Array_extract___redArg(v_x_1095_, v___y_1103_, v___x_1098_);
v_sz_1113_ = lean_array_size(v___x_1112_);
v___x_1114_ = ((size_t)0ULL);
v___x_1115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_f_1094_, v_sz_1113_, v___x_1114_, v___x_1112_);
v___x_1116_ = l_Array_append___redArg(v___x_1105_, v___x_1115_);
lean_dec_ref(v___x_1115_);
return v___x_1116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___redArg___boxed(lean_object* v_f_1118_, lean_object* v_x_1119_, lean_object* v_g_1120_, lean_object* v_y_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v_f_1118_, v_x_1119_, v_g_1120_, v_y_1121_);
lean_dec_ref(v_y_1121_);
lean_dec_ref(v_x_1119_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith(lean_object* v_00_u03b1_1123_, lean_object* v_00_u03b2_1124_, lean_object* v_00_u03b3_1125_, lean_object* v_f_1126_, lean_object* v_x_1127_, lean_object* v_g_1128_, lean_object* v_y_1129_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v_f_1126_, v_x_1127_, v_g_1128_, v_y_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_interleaveWith___boxed(lean_object* v_00_u03b1_1131_, lean_object* v_00_u03b2_1132_, lean_object* v_00_u03b3_1133_, lean_object* v_f_1134_, lean_object* v_x_1135_, lean_object* v_g_1136_, lean_object* v_y_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_Meta_LibrarySearch_interleaveWith(v_00_u03b1_1131_, v_00_u03b2_1132_, v_00_u03b3_1133_, v_f_1134_, v_x_1135_, v_g_1136_, v_y_1137_);
lean_dec_ref(v_y_1137_);
lean_dec_ref(v_x_1135_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0(lean_object* v_00_u03b2_1139_, lean_object* v_00_u03b3_1140_, lean_object* v_g_1141_, size_t v_sz_1142_, size_t v_i_1143_, lean_object* v_bs_1144_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___redArg(v_g_1141_, v_sz_1142_, v_i_1143_, v_bs_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0___boxed(lean_object* v_00_u03b2_1146_, lean_object* v_00_u03b3_1147_, lean_object* v_g_1148_, lean_object* v_sz_1149_, lean_object* v_i_1150_, lean_object* v_bs_1151_){
_start:
{
size_t v_sz_boxed_1152_; size_t v_i_boxed_1153_; lean_object* v_res_1154_; 
v_sz_boxed_1152_ = lean_unbox_usize(v_sz_1149_);
lean_dec(v_sz_1149_);
v_i_boxed_1153_ = lean_unbox_usize(v_i_1150_);
lean_dec(v_i_1150_);
v_res_1154_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__0(v_00_u03b2_1146_, v_00_u03b3_1147_, v_g_1148_, v_sz_boxed_1152_, v_i_boxed_1153_, v_bs_1151_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1(lean_object* v_00_u03b3_1155_, lean_object* v_upperBound_1156_, lean_object* v_00_u03b1_1157_, lean_object* v_x_1158_, lean_object* v_f_1159_, lean_object* v_00_u03b2_1160_, lean_object* v_y_1161_, lean_object* v_g_1162_, lean_object* v_inst_1163_, lean_object* v_R_1164_, lean_object* v_a_1165_, lean_object* v_b_1166_, lean_object* v_c_1167_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___redArg(v_upperBound_1156_, v_x_1158_, v_f_1159_, v_y_1161_, v_g_1162_, v_a_1165_, v_b_1166_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1___boxed(lean_object* v_00_u03b3_1169_, lean_object* v_upperBound_1170_, lean_object* v_00_u03b1_1171_, lean_object* v_x_1172_, lean_object* v_f_1173_, lean_object* v_00_u03b2_1174_, lean_object* v_y_1175_, lean_object* v_g_1176_, lean_object* v_inst_1177_, lean_object* v_R_1178_, lean_object* v_a_1179_, lean_object* v_b_1180_, lean_object* v_c_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_LibrarySearch_interleaveWith_spec__1(v_00_u03b3_1169_, v_upperBound_1170_, v_00_u03b1_1171_, v_x_1172_, v_f_1173_, v_00_u03b2_1174_, v_y_1175_, v_g_1176_, v_inst_1177_, v_R_1178_, v_a_1179_, v_b_1180_, v_c_1181_);
lean_dec_ref(v_y_1175_);
lean_dec_ref(v_x_1172_);
lean_dec(v_upperBound_1170_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_));
v___x_1191_ = l_Lean_registerInternalExceptionId(v___x_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2____boxed(lean_object* v_a_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn_00___x40_Lean_Meta_Tactic_LibrarySearch_989218885____hygCtx___hyg_2_();
return v_res_1193_;
}
}
static lean_object* _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1194_ = lean_box(0);
v___x_1195_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_abortSpeculationId;
v___x_1196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
lean_ctor_set(v___x_1196_, 1, v___x_1194_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___redArg(lean_object* v_inst_1197_){
_start:
{
lean_object* v_throw_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v_throw_1198_ = lean_ctor_get(v_inst_1197_, 0);
lean_inc(v_throw_1198_);
lean_dec_ref(v_inst_1197_);
v___x_1199_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0, &l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0_once, _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0);
v___x_1200_ = lean_apply_2(v_throw_1198_, lean_box(0), v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation(lean_object* v_m_1201_, lean_object* v_00_u03b1_1202_, lean_object* v_inst_1203_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_Lean_Meta_LibrarySearch_abortSpeculation___redArg(v_inst_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_LibrarySearch_isAbortSpeculation(lean_object* v_x_1205_){
_start:
{
if (lean_obj_tag(v_x_1205_) == 1)
{
lean_object* v_id_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; 
v_id_1206_ = lean_ctor_get(v_x_1205_, 0);
v___x_1207_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_abortSpeculationId;
v___x_1208_ = l_Lean_instBEqInternalExceptionId_beq(v_id_1206_, v___x_1207_);
return v___x_1208_;
}
else
{
uint8_t v___x_1209_; 
v___x_1209_ = 0;
return v___x_1209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_isAbortSpeculation___boxed(lean_object* v_x_1210_){
_start:
{
uint8_t v_res_1211_; lean_object* v_r_1212_; 
v_res_1211_ = l_Lean_Meta_LibrarySearch_isAbortSpeculation(v_x_1210_);
lean_dec_ref(v_x_1210_);
v_r_1212_ = lean_box(v_res_1211_);
return v_r_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(lean_object* v_x_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_Meta_saveState___redArg(v___y_1215_, v___y_1217_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; lean_object* v___x_1221_; 
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_a_1220_);
lean_dec_ref_known(v___x_1219_, 1);
lean_inc(v___y_1217_);
lean_inc_ref(v___y_1216_);
lean_inc(v___y_1215_);
lean_inc_ref(v___y_1214_);
v___x_1221_ = lean_apply_5(v_x_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, lean_box(0));
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1230_; 
lean_dec(v_a_1220_);
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1224_ = v___x_1221_;
v_isShared_1225_ = v_isSharedCheck_1230_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1221_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1230_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___x_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1226_, 0, v_a_1222_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v___x_1226_);
v___x_1228_ = v___x_1224_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1260_; 
v_a_1231_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1233_ = v___x_1221_;
v_isShared_1234_ = v_isSharedCheck_1260_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1221_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1260_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
uint8_t v___y_1236_; uint8_t v___x_1258_; 
v___x_1258_ = l_Lean_Exception_isInterrupt(v_a_1231_);
if (v___x_1258_ == 0)
{
uint8_t v___x_1259_; 
lean_inc(v_a_1231_);
v___x_1259_ = l_Lean_Exception_isRuntime(v_a_1231_);
v___y_1236_ = v___x_1259_;
goto v___jp_1235_;
}
else
{
v___y_1236_ = v___x_1258_;
goto v___jp_1235_;
}
v___jp_1235_:
{
if (v___y_1236_ == 0)
{
lean_object* v___x_1237_; 
lean_del_object(v___x_1233_);
lean_dec(v_a_1231_);
v___x_1237_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1220_, v___y_1215_, v___y_1217_);
lean_dec(v_a_1220_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1245_; 
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1245_ == 0)
{
lean_object* v_unused_1246_; 
v_unused_1246_ = lean_ctor_get(v___x_1237_, 0);
lean_dec(v_unused_1246_);
v___x_1239_ = v___x_1237_;
v_isShared_1240_ = v_isSharedCheck_1245_;
goto v_resetjp_1238_;
}
else
{
lean_dec(v___x_1237_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1245_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1241_ = lean_box(0);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v___x_1241_);
v___x_1243_ = v___x_1239_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
else
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
v_a_1247_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1249_ = v___x_1237_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1237_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
else
{
lean_object* v___x_1256_; 
lean_dec(v_a_1220_);
if (v_isShared_1234_ == 0)
{
v___x_1256_ = v___x_1233_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1231_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
}
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
lean_dec_ref(v_x_1213_);
v_a_1261_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1219_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1219_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg___boxed(lean_object* v_x_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v_x_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0(lean_object* v_00_u03b1_1276_, lean_object* v_x_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v_x_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___boxed(lean_object* v_00_u03b1_1284_, lean_object* v_x_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0(v_00_u03b1_1284_, v_x_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(lean_object* v_e_1292_, lean_object* v___y_1293_){
_start:
{
uint8_t v___x_1295_; 
v___x_1295_ = l_Lean_Expr_hasMVar(v_e_1292_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; 
v___x_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1296_, 0, v_e_1292_);
return v___x_1296_;
}
else
{
lean_object* v___x_1297_; lean_object* v_mctx_1298_; lean_object* v___x_1299_; lean_object* v_fst_1300_; lean_object* v_snd_1301_; lean_object* v___x_1302_; lean_object* v_cache_1303_; lean_object* v_zetaDeltaFVarIds_1304_; lean_object* v_postponed_1305_; lean_object* v_diag_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1315_; 
v___x_1297_ = lean_st_ref_get(v___y_1293_);
v_mctx_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc_ref(v_mctx_1298_);
lean_dec(v___x_1297_);
v___x_1299_ = l_Lean_instantiateMVarsCore(v_mctx_1298_, v_e_1292_);
v_fst_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_fst_1300_);
v_snd_1301_ = lean_ctor_get(v___x_1299_, 1);
lean_inc(v_snd_1301_);
lean_dec_ref(v___x_1299_);
v___x_1302_ = lean_st_ref_take(v___y_1293_);
v_cache_1303_ = lean_ctor_get(v___x_1302_, 1);
v_zetaDeltaFVarIds_1304_ = lean_ctor_get(v___x_1302_, 2);
v_postponed_1305_ = lean_ctor_get(v___x_1302_, 3);
v_diag_1306_ = lean_ctor_get(v___x_1302_, 4);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1315_ == 0)
{
lean_object* v_unused_1316_; 
v_unused_1316_ = lean_ctor_get(v___x_1302_, 0);
lean_dec(v_unused_1316_);
v___x_1308_ = v___x_1302_;
v_isShared_1309_ = v_isSharedCheck_1315_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_diag_1306_);
lean_inc(v_postponed_1305_);
lean_inc(v_zetaDeltaFVarIds_1304_);
lean_inc(v_cache_1303_);
lean_dec(v___x_1302_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1315_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v_snd_1301_);
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_snd_1301_);
lean_ctor_set(v_reuseFailAlloc_1314_, 1, v_cache_1303_);
lean_ctor_set(v_reuseFailAlloc_1314_, 2, v_zetaDeltaFVarIds_1304_);
lean_ctor_set(v_reuseFailAlloc_1314_, 3, v_postponed_1305_);
lean_ctor_set(v_reuseFailAlloc_1314_, 4, v_diag_1306_);
v___x_1311_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = lean_st_ref_put(v___y_1293_, v___x_1311_);
v___x_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1313_, 0, v_fst_1300_);
return v___x_1313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg___boxed(lean_object* v_e_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_e_1317_, v___y_1318_);
lean_dec(v___y_1318_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1(lean_object* v_e_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_e_1321_, v___y_1323_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___boxed(lean_object* v_e_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1(v_e_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0(lean_object* v___x_1335_, lean_object* v_x_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1335_);
lean_ctor_set(v___x_1337_, 1, v_x_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(lean_object* v___x_1338_, size_t v_sz_1339_, size_t v_i_1340_, lean_object* v_bs_1341_){
_start:
{
uint8_t v___x_1342_; 
v___x_1342_ = lean_usize_dec_lt(v_i_1340_, v_sz_1339_);
if (v___x_1342_ == 0)
{
lean_dec_ref(v___x_1338_);
return v_bs_1341_;
}
else
{
lean_object* v_v_1343_; lean_object* v___x_1344_; lean_object* v_bs_x27_1345_; lean_object* v___x_1346_; size_t v___x_1347_; size_t v___x_1348_; lean_object* v___x_1349_; 
v_v_1343_ = lean_array_uget(v_bs_1341_, v_i_1340_);
v___x_1344_ = lean_unsigned_to_nat(0u);
v_bs_x27_1345_ = lean_array_uset(v_bs_1341_, v_i_1340_, v___x_1344_);
lean_inc_ref(v___x_1338_);
v___x_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1338_);
lean_ctor_set(v___x_1346_, 1, v_v_1343_);
v___x_1347_ = ((size_t)1ULL);
v___x_1348_ = lean_usize_add(v_i_1340_, v___x_1347_);
v___x_1349_ = lean_array_uset(v_bs_x27_1345_, v_i_1340_, v___x_1346_);
v_i_1340_ = v___x_1348_;
v_bs_1341_ = v___x_1349_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2___boxed(lean_object* v___x_1351_, lean_object* v_sz_1352_, lean_object* v_i_1353_, lean_object* v_bs_1354_){
_start:
{
size_t v_sz_boxed_1355_; size_t v_i_boxed_1356_; lean_object* v_res_1357_; 
v_sz_boxed_1355_ = lean_unbox_usize(v_sz_1352_);
lean_dec(v_sz_1352_);
v_i_boxed_1356_ = lean_unbox_usize(v_i_1353_);
lean_dec(v_i_1353_);
v_res_1357_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(v___x_1351_, v_sz_boxed_1355_, v_i_boxed_1356_, v_bs_1354_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm(lean_object* v_searchFn_1358_, lean_object* v_goal_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v___x_1365_; 
lean_inc(v_goal_1359_);
v___x_1365_ = l_Lean_MVarId_getType(v_goal_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1367_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1366_);
lean_dec_ref_known(v___x_1365_, 1);
lean_inc_ref(v_searchFn_1358_);
lean_inc(v_a_1363_);
lean_inc_ref(v_a_1362_);
lean_inc(v_a_1361_);
lean_inc_ref(v_a_1360_);
v___x_1367_ = lean_apply_6(v_searchFn_1358_, v_a_1366_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, lean_box(0));
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; lean_object* v___x_1369_; lean_object* v_mctx_1370_; lean_object* v___x_1371_; lean_object* v___f_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_a_1368_);
lean_dec_ref_known(v___x_1367_, 1);
v___x_1369_ = lean_st_ref_get(v_a_1361_);
v_mctx_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc_ref_n(v_mctx_1370_, 2);
lean_dec(v___x_1369_);
lean_inc(v_goal_1359_);
v___x_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1371_, 0, v_goal_1359_);
lean_ctor_set(v___x_1371_, 1, v_mctx_1370_);
lean_inc_ref(v___x_1371_);
v___f_1372_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0), 2, 1);
lean_closure_set(v___f_1372_, 0, v___x_1371_);
v___x_1373_ = lean_alloc_closure((void*)(l_Lean_MVarId_applySymm___boxed), 6, 1);
lean_closure_set(v___x_1373_, 0, v_goal_1359_);
v___x_1374_ = l_Lean_observing_x3f___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__0___redArg(v___x_1373_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1434_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1377_ = v___x_1374_;
v_isShared_1378_ = v_isSharedCheck_1434_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1374_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1434_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
if (lean_obj_tag(v_a_1375_) == 1)
{
lean_object* v_val_1379_; lean_object* v___x_1380_; 
lean_del_object(v___x_1377_);
lean_dec_ref_known(v___x_1371_, 2);
v_val_1379_ = lean_ctor_get(v_a_1375_, 0);
lean_inc_n(v_val_1379_, 2);
lean_dec_ref_known(v_a_1375_, 1);
v___x_1380_ = l_Lean_MVarId_getType(v_val_1379_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1382_; lean_object* v_a_1383_; lean_object* v___x_1384_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_a_1381_);
lean_dec_ref_known(v___x_1380_, 1);
v___x_1382_ = l_Lean_instantiateMVars___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__1___redArg(v_a_1381_, v_a_1361_);
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_a_1383_);
lean_dec_ref(v___x_1382_);
lean_inc(v_a_1363_);
lean_inc_ref(v_a_1362_);
lean_inc(v_a_1361_);
lean_inc_ref(v_a_1360_);
v___x_1384_ = lean_apply_6(v_searchFn_1358_, v_a_1383_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, lean_box(0));
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1411_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1387_ = v___x_1384_;
v_isShared_1388_ = v_isSharedCheck_1411_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1384_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1411_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v_mctx_1390_; lean_object* v___x_1391_; lean_object* v___f_1392_; lean_object* v___x_1393_; lean_object* v_cache_1394_; lean_object* v_zetaDeltaFVarIds_1395_; lean_object* v_postponed_1396_; lean_object* v_diag_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1409_; 
v___x_1389_ = lean_st_ref_get(v_a_1361_);
v_mctx_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc_ref(v_mctx_1390_);
lean_dec(v___x_1389_);
v___x_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1391_, 0, v_val_1379_);
lean_ctor_set(v___x_1391_, 1, v_mctx_1390_);
v___f_1392_ = lean_alloc_closure((void*)(l_Lean_Meta_LibrarySearch_librarySearchSymm___lam__0), 2, 1);
lean_closure_set(v___f_1392_, 0, v___x_1391_);
v___x_1393_ = lean_st_ref_take(v_a_1361_);
v_cache_1394_ = lean_ctor_get(v___x_1393_, 1);
v_zetaDeltaFVarIds_1395_ = lean_ctor_get(v___x_1393_, 2);
v_postponed_1396_ = lean_ctor_get(v___x_1393_, 3);
v_diag_1397_ = lean_ctor_get(v___x_1393_, 4);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1409_ == 0)
{
lean_object* v_unused_1410_; 
v_unused_1410_ = lean_ctor_get(v___x_1393_, 0);
lean_dec(v_unused_1410_);
v___x_1399_ = v___x_1393_;
v_isShared_1400_ = v_isSharedCheck_1409_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_diag_1397_);
lean_inc(v_postponed_1396_);
lean_inc(v_zetaDeltaFVarIds_1395_);
lean_inc(v_cache_1394_);
lean_dec(v___x_1393_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1409_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v_mctx_1370_);
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_mctx_1370_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_cache_1394_);
lean_ctor_set(v_reuseFailAlloc_1408_, 2, v_zetaDeltaFVarIds_1395_);
lean_ctor_set(v_reuseFailAlloc_1408_, 3, v_postponed_1396_);
lean_ctor_set(v_reuseFailAlloc_1408_, 4, v_diag_1397_);
v___x_1402_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1406_; 
v___x_1403_ = lean_st_ref_put(v_a_1361_, v___x_1402_);
v___x_1404_ = l_Lean_Meta_LibrarySearch_interleaveWith___redArg(v___f_1372_, v_a_1368_, v___f_1392_, v_a_1385_);
lean_dec(v_a_1385_);
lean_dec(v_a_1368_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v___x_1404_);
v___x_1406_ = v___x_1387_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1404_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
lean_dec(v_val_1379_);
lean_dec_ref(v___f_1372_);
lean_dec_ref(v_mctx_1370_);
lean_dec(v_a_1368_);
v_a_1412_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1384_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1384_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
lean_dec(v_val_1379_);
lean_dec_ref(v___f_1372_);
lean_dec_ref(v_mctx_1370_);
lean_dec(v_a_1368_);
lean_dec_ref(v_searchFn_1358_);
v_a_1420_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v___x_1380_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1380_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
else
{
size_t v_sz_1428_; size_t v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1432_; 
lean_dec(v_a_1375_);
lean_dec_ref(v___f_1372_);
lean_dec_ref(v_mctx_1370_);
lean_dec_ref(v_searchFn_1358_);
v_sz_1428_ = lean_array_size(v_a_1368_);
v___x_1429_ = ((size_t)0ULL);
v___x_1430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_LibrarySearch_librarySearchSymm_spec__2(v___x_1371_, v_sz_1428_, v___x_1429_, v_a_1368_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 0, v___x_1430_);
v___x_1432_ = v___x_1377_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
lean_dec_ref(v___f_1372_);
lean_dec_ref_known(v___x_1371_, 2);
lean_dec_ref(v_mctx_1370_);
lean_dec(v_a_1368_);
lean_dec_ref(v_searchFn_1358_);
v_a_1435_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1374_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1374_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec(v_goal_1359_);
lean_dec_ref(v_searchFn_1358_);
v_a_1443_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1367_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1367_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec(v_goal_1359_);
lean_dec_ref(v_searchFn_1358_);
v_a_1451_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1365_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1365_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearchSymm___boxed(lean_object* v_searchFn_1459_, lean_object* v_goal_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v_searchFn_1459_, v_goal_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
lean_dec(v_a_1462_);
lean_dec_ref(v_a_1461_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0(lean_object* v_e_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1477_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___closed__1));
v___x_1478_ = lean_unsigned_to_nat(1u);
v___x_1479_ = lean_mk_empty_array_with_capacity(v___x_1478_);
v___x_1480_ = lean_array_push(v___x_1479_, v_e_1471_);
v___x_1481_ = l_Lean_Meta_mkAppM(v___x_1477_, v___x_1480_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0___boxed(lean_object* v_e_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__0(v_e_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1(lean_object* v_e_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1499_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___closed__1));
v___x_1500_ = lean_unsigned_to_nat(1u);
v___x_1501_ = lean_mk_empty_array_with_capacity(v___x_1500_);
v___x_1502_ = lean_array_push(v___x_1501_, v_e_1493_);
v___x_1503_ = l_Lean_Meta_mkAppM(v___x_1499_, v___x_1502_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1___boxed(lean_object* v_e_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___lam__1(v_e_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(lean_object* v_lem_1513_, uint8_t v_mod_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v___f_1520_; lean_object* v___f_1521_; lean_object* v___x_1522_; 
v___f_1520_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__0));
v___f_1521_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___closed__1));
v___x_1522_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_lem_1513_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
if (lean_obj_tag(v___x_1522_) == 0)
{
switch(v_mod_1514_)
{
case 0:
{
return v___x_1522_;
}
case 1:
{
lean_object* v_a_1523_; lean_object* v___x_1524_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1522_, 1);
v___x_1524_ = l_Lean_Meta_mapForallTelescope(v___f_1520_, v_a_1523_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
return v___x_1524_;
}
default: 
{
lean_object* v_a_1525_; lean_object* v___x_1526_; 
v_a_1525_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v___x_1522_, 1);
v___x_1526_ = l_Lean_Meta_mapForallTelescope(v___f_1521_, v_a_1525_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
return v___x_1526_;
}
}
}
else
{
return v___x_1522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma___boxed(lean_object* v_lem_1527_, lean_object* v_mod_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_){
_start:
{
uint8_t v_mod_boxed_1534_; lean_object* v_res_1535_; 
v_mod_boxed_1534_ = lean_unbox(v_mod_1528_);
v_res_1535_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_lem_1527_, v_mod_boxed_1534_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
lean_dec(v_a_1530_);
lean_dec_ref(v_a_1529_);
return v_res_1535_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar(lean_object* v_e_1536_){
_start:
{
switch(lean_obj_tag(v_e_1536_))
{
case 0:
{
uint8_t v___x_1537_; 
v___x_1537_ = 1;
return v___x_1537_;
}
case 1:
{
uint8_t v___x_1538_; 
v___x_1538_ = 1;
return v___x_1538_;
}
case 2:
{
uint8_t v___x_1539_; 
v___x_1539_ = 1;
return v___x_1539_;
}
default: 
{
uint8_t v___x_1540_; 
v___x_1540_ = 0;
return v___x_1540_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar___boxed(lean_object* v_e_1541_){
_start:
{
uint8_t v_res_1542_; lean_object* v_r_1543_; 
v_res_1542_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_isVar(v_e_1541_);
lean_dec_ref(v_e_1541_);
v_r_1543_ = lean_box(v_res_1542_);
return v_r_1543_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1544_ = lean_unsigned_to_nat(32u);
v___x_1545_ = lean_mk_empty_array_with_capacity(v___x_1544_);
v___x_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
return v___x_1546_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1547_ = ((size_t)5ULL);
v___x_1548_ = lean_unsigned_to_nat(0u);
v___x_1549_ = lean_unsigned_to_nat(32u);
v___x_1550_ = lean_mk_empty_array_with_capacity(v___x_1549_);
v___x_1551_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__0);
v___x_1552_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
lean_ctor_set(v___x_1552_, 1, v___x_1550_);
lean_ctor_set(v___x_1552_, 2, v___x_1548_);
lean_ctor_set(v___x_1552_, 3, v___x_1548_);
lean_ctor_set_usize(v___x_1552_, 4, v___x_1547_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(lean_object* v___y_1553_){
_start:
{
lean_object* v___x_1555_; lean_object* v_traceState_1556_; lean_object* v_traces_1557_; lean_object* v___x_1558_; lean_object* v_traceState_1559_; lean_object* v_env_1560_; lean_object* v_nextMacroScope_1561_; lean_object* v_ngen_1562_; lean_object* v_auxDeclNGen_1563_; lean_object* v_cache_1564_; lean_object* v_recordedDeps_1565_; lean_object* v_messages_1566_; lean_object* v_infoState_1567_; lean_object* v_snapshotTasks_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1587_; 
v___x_1555_ = lean_st_ref_get(v___y_1553_);
v_traceState_1556_ = lean_ctor_get(v___x_1555_, 4);
lean_inc_ref(v_traceState_1556_);
lean_dec(v___x_1555_);
v_traces_1557_ = lean_ctor_get(v_traceState_1556_, 0);
lean_inc_ref(v_traces_1557_);
lean_dec_ref(v_traceState_1556_);
v___x_1558_ = lean_st_ref_take(v___y_1553_);
v_traceState_1559_ = lean_ctor_get(v___x_1558_, 4);
v_env_1560_ = lean_ctor_get(v___x_1558_, 0);
v_nextMacroScope_1561_ = lean_ctor_get(v___x_1558_, 1);
v_ngen_1562_ = lean_ctor_get(v___x_1558_, 2);
v_auxDeclNGen_1563_ = lean_ctor_get(v___x_1558_, 3);
v_cache_1564_ = lean_ctor_get(v___x_1558_, 5);
v_recordedDeps_1565_ = lean_ctor_get(v___x_1558_, 6);
v_messages_1566_ = lean_ctor_get(v___x_1558_, 7);
v_infoState_1567_ = lean_ctor_get(v___x_1558_, 8);
v_snapshotTasks_1568_ = lean_ctor_get(v___x_1558_, 9);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1570_ = v___x_1558_;
v_isShared_1571_ = v_isSharedCheck_1587_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_snapshotTasks_1568_);
lean_inc(v_infoState_1567_);
lean_inc(v_messages_1566_);
lean_inc(v_recordedDeps_1565_);
lean_inc(v_cache_1564_);
lean_inc(v_traceState_1559_);
lean_inc(v_auxDeclNGen_1563_);
lean_inc(v_ngen_1562_);
lean_inc(v_nextMacroScope_1561_);
lean_inc(v_env_1560_);
lean_dec(v___x_1558_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1587_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
uint64_t v_tid_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1585_; 
v_tid_1572_ = lean_ctor_get_uint64(v_traceState_1559_, sizeof(void*)*1);
v_isSharedCheck_1585_ = !lean_is_exclusive(v_traceState_1559_);
if (v_isSharedCheck_1585_ == 0)
{
lean_object* v_unused_1586_; 
v_unused_1586_ = lean_ctor_get(v_traceState_1559_, 0);
lean_dec(v_unused_1586_);
v___x_1574_ = v_traceState_1559_;
v_isShared_1575_ = v_isSharedCheck_1585_;
goto v_resetjp_1573_;
}
else
{
lean_dec(v_traceState_1559_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1585_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1576_; lean_object* v___x_1578_; 
v___x_1576_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___closed__1);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v___x_1576_);
v___x_1578_ = v___x_1574_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1576_);
lean_ctor_set_uint64(v_reuseFailAlloc_1584_, sizeof(void*)*1, v_tid_1572_);
v___x_1578_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
lean_object* v___x_1580_; 
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 4, v___x_1578_);
v___x_1580_ = v___x_1570_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_env_1560_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v_nextMacroScope_1561_);
lean_ctor_set(v_reuseFailAlloc_1583_, 2, v_ngen_1562_);
lean_ctor_set(v_reuseFailAlloc_1583_, 3, v_auxDeclNGen_1563_);
lean_ctor_set(v_reuseFailAlloc_1583_, 4, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1583_, 5, v_cache_1564_);
lean_ctor_set(v_reuseFailAlloc_1583_, 6, v_recordedDeps_1565_);
lean_ctor_set(v_reuseFailAlloc_1583_, 7, v_messages_1566_);
lean_ctor_set(v_reuseFailAlloc_1583_, 8, v_infoState_1567_);
lean_ctor_set(v_reuseFailAlloc_1583_, 9, v_snapshotTasks_1568_);
v___x_1580_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = lean_st_ref_put(v___y_1553_, v___x_1580_);
v___x_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1582_, 0, v_traces_1557_);
return v___x_1582_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg___boxed(lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v___y_1588_);
lean_dec(v___y_1588_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0(lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v___y_1594_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___boxed(lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0(v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
return v_res_1602_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(lean_object* v_opts_1603_, lean_object* v_opt_1604_){
_start:
{
lean_object* v_name_1605_; lean_object* v_defValue_1606_; lean_object* v_map_1607_; lean_object* v___x_1608_; 
v_name_1605_ = lean_ctor_get(v_opt_1604_, 0);
v_defValue_1606_ = lean_ctor_get(v_opt_1604_, 1);
v_map_1607_ = lean_ctor_get(v_opts_1603_, 0);
v___x_1608_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1607_, v_name_1605_);
if (lean_obj_tag(v___x_1608_) == 0)
{
uint8_t v___x_1609_; 
v___x_1609_ = lean_unbox(v_defValue_1606_);
return v___x_1609_;
}
else
{
lean_object* v_val_1610_; 
v_val_1610_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_val_1610_);
lean_dec_ref_known(v___x_1608_, 1);
if (lean_obj_tag(v_val_1610_) == 1)
{
uint8_t v_v_1611_; 
v_v_1611_ = lean_ctor_get_uint8(v_val_1610_, 0);
lean_dec_ref_known(v_val_1610_, 0);
return v_v_1611_;
}
else
{
uint8_t v___x_1612_; 
lean_dec(v_val_1610_);
v___x_1612_ = lean_unbox(v_defValue_1606_);
return v___x_1612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1___boxed(lean_object* v_opts_1613_, lean_object* v_opt_1614_){
_start:
{
uint8_t v_res_1615_; lean_object* v_r_1616_; 
v_res_1615_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1613_, v_opt_1614_);
lean_dec_ref(v_opt_1614_);
lean_dec_ref(v_opts_1613_);
v_r_1616_ = lean_box(v_res_1615_);
return v_r_1616_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__0));
v___x_1619_ = l_Lean_stringToMessageData(v___x_1618_);
return v___x_1619_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__2));
v___x_1622_ = l_Lean_stringToMessageData(v___x_1621_);
return v___x_1622_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__5));
v___x_1627_ = l_Lean_MessageData_ofFormat(v___x_1626_);
return v___x_1627_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__8));
v___x_1632_ = l_Lean_MessageData_ofFormat(v___x_1631_);
return v___x_1632_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12(void){
_start:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__11));
v___x_1637_ = l_Lean_MessageData_ofFormat(v___x_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0(lean_object* v_fst_1638_, uint8_t v_snd_1639_, lean_object* v_x_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___y_1650_; 
v___x_1646_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__1);
v___x_1647_ = l_Lean_MessageData_ofName(v_fst_1638_);
v___x_1648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1646_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
switch(v_snd_1639_)
{
case 0:
{
lean_object* v___x_1655_; 
v___x_1655_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__6);
v___y_1650_ = v___x_1655_;
goto v___jp_1649_;
}
case 1:
{
lean_object* v___x_1656_; 
v___x_1656_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__9);
v___y_1650_ = v___x_1656_;
goto v___jp_1649_;
}
default: 
{
lean_object* v___x_1657_; 
v___x_1657_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__12);
v___y_1650_ = v___x_1657_;
goto v___jp_1649_;
}
}
v___jp_1649_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
lean_inc_ref(v___y_1650_);
v___x_1651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1648_);
lean_ctor_set(v___x_1651_, 1, v___y_1650_);
v___x_1652_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__3);
v___x_1653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1651_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
return v___x_1654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___boxed(lean_object* v_fst_1658_, lean_object* v_snd_1659_, lean_object* v_x_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
uint8_t v_snd_11055__boxed_1666_; lean_object* v_res_1667_; 
v_snd_11055__boxed_1666_ = lean_unbox(v_snd_1659_);
v_res_1667_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0(v_fst_1658_, v_snd_11055__boxed_1666_, v_x_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec_ref(v_x_1660_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(lean_object* v_opts_1668_, lean_object* v_opt_1669_){
_start:
{
lean_object* v_name_1670_; lean_object* v_defValue_1671_; lean_object* v_map_1672_; lean_object* v___x_1673_; 
v_name_1670_ = lean_ctor_get(v_opt_1669_, 0);
v_defValue_1671_ = lean_ctor_get(v_opt_1669_, 1);
v_map_1672_ = lean_ctor_get(v_opts_1668_, 0);
v___x_1673_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1672_, v_name_1670_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_inc(v_defValue_1671_);
return v_defValue_1671_;
}
else
{
lean_object* v_val_1674_; 
v_val_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_val_1674_);
lean_dec_ref_known(v___x_1673_, 1);
if (lean_obj_tag(v_val_1674_) == 3)
{
lean_object* v_v_1675_; 
v_v_1675_ = lean_ctor_get(v_val_1674_, 0);
lean_inc(v_v_1675_);
lean_dec_ref_known(v_val_1674_, 1);
return v_v_1675_;
}
else
{
lean_dec(v_val_1674_);
lean_inc(v_defValue_1671_);
return v_defValue_1671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5___boxed(lean_object* v_opts_1676_, lean_object* v_opt_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1676_, v_opt_1677_);
lean_dec_ref(v_opt_1677_);
lean_dec_ref(v_opts_1676_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(lean_object* v_x_1679_){
_start:
{
if (lean_obj_tag(v_x_1679_) == 0)
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
v_a_1681_ = lean_ctor_get(v_x_1679_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_x_1679_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v_x_1679_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v_x_1679_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
lean_ctor_set_tag(v___x_1683_, 1);
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
v_a_1689_ = lean_ctor_get(v_x_1679_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_x_1679_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v_x_1679_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v_x_1679_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
lean_ctor_set_tag(v___x_1691_, 0);
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg___boxed(lean_object* v_x_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_x_1697_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(size_t v_sz_1700_, size_t v_i_1701_, lean_object* v_bs_1702_){
_start:
{
uint8_t v___x_1703_; 
v___x_1703_ = lean_usize_dec_lt(v_i_1701_, v_sz_1700_);
if (v___x_1703_ == 0)
{
return v_bs_1702_;
}
else
{
lean_object* v_v_1704_; lean_object* v_msg_1705_; lean_object* v___x_1706_; lean_object* v_bs_x27_1707_; size_t v___x_1708_; size_t v___x_1709_; lean_object* v___x_1710_; 
v_v_1704_ = lean_array_uget_borrowed(v_bs_1702_, v_i_1701_);
v_msg_1705_ = lean_ctor_get(v_v_1704_, 1);
lean_inc_ref(v_msg_1705_);
v___x_1706_ = lean_unsigned_to_nat(0u);
v_bs_x27_1707_ = lean_array_uset(v_bs_1702_, v_i_1701_, v___x_1706_);
v___x_1708_ = ((size_t)1ULL);
v___x_1709_ = lean_usize_add(v_i_1701_, v___x_1708_);
v___x_1710_ = lean_array_uset(v_bs_x27_1707_, v_i_1701_, v_msg_1705_);
v_i_1701_ = v___x_1709_;
v_bs_1702_ = v___x_1710_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1712_, lean_object* v_i_1713_, lean_object* v_bs_1714_){
_start:
{
size_t v_sz_boxed_1715_; size_t v_i_boxed_1716_; lean_object* v_res_1717_; 
v_sz_boxed_1715_ = lean_unbox_usize(v_sz_1712_);
lean_dec(v_sz_1712_);
v_i_boxed_1716_ = lean_unbox_usize(v_i_1713_);
lean_dec(v_i_1713_);
v_res_1717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(v_sz_boxed_1715_, v_i_boxed_1716_, v_bs_1714_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(lean_object* v_oldTraces_1718_, lean_object* v_data_1719_, lean_object* v_ref_1720_, lean_object* v_msg_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_toCold_1727_; lean_object* v_currRecDepth_1728_; lean_object* v_ref_1729_; uint16_t v_optionFlags_1730_; uint8_t v_suppressElabErrors_1731_; uint8_t v_isRecordingDeps_1732_; lean_object* v_ref_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v_traceState_1736_; lean_object* v_traces_1737_; lean_object* v___x_1738_; size_t v_sz_1739_; size_t v___x_1740_; lean_object* v___x_1741_; lean_object* v_msg_1742_; lean_object* v___x_1743_; lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1782_; 
v_toCold_1727_ = lean_ctor_get(v___y_1724_, 0);
v_currRecDepth_1728_ = lean_ctor_get(v___y_1724_, 1);
v_ref_1729_ = lean_ctor_get(v___y_1724_, 2);
v_optionFlags_1730_ = lean_ctor_get_uint16(v___y_1724_, sizeof(void*)*3);
v_suppressElabErrors_1731_ = lean_ctor_get_uint8(v___y_1724_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1732_ = lean_ctor_get_uint8(v___y_1724_, sizeof(void*)*3 + 3);
v_ref_1733_ = l_Lean_replaceRef(v_ref_1720_, v_ref_1729_);
lean_inc(v_currRecDepth_1728_);
lean_inc_ref(v_toCold_1727_);
v___x_1734_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1734_, 0, v_toCold_1727_);
lean_ctor_set(v___x_1734_, 1, v_currRecDepth_1728_);
lean_ctor_set(v___x_1734_, 2, v_ref_1733_);
lean_ctor_set_uint16(v___x_1734_, sizeof(void*)*3, v_optionFlags_1730_);
lean_ctor_set_uint8(v___x_1734_, sizeof(void*)*3 + 2, v_suppressElabErrors_1731_);
lean_ctor_set_uint8(v___x_1734_, sizeof(void*)*3 + 3, v_isRecordingDeps_1732_);
v___x_1735_ = lean_st_ref_get(v___y_1725_);
v_traceState_1736_ = lean_ctor_get(v___x_1735_, 4);
lean_inc_ref(v_traceState_1736_);
lean_dec(v___x_1735_);
v_traces_1737_ = lean_ctor_get(v_traceState_1736_, 0);
lean_inc_ref(v_traces_1737_);
lean_dec_ref(v_traceState_1736_);
v___x_1738_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1737_);
lean_dec_ref(v_traces_1737_);
v_sz_1739_ = lean_array_size(v___x_1738_);
v___x_1740_ = ((size_t)0ULL);
v___x_1741_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2_spec__3(v_sz_1739_, v___x_1740_, v___x_1738_);
v_msg_1742_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1742_, 0, v_data_1719_);
lean_ctor_set(v_msg_1742_, 1, v_msg_1721_);
lean_ctor_set(v_msg_1742_, 2, v___x_1741_);
v___x_1743_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0_spec__0(v_msg_1742_, v___y_1722_, v___y_1723_, v___x_1734_, v___y_1725_);
lean_dec_ref_known(v___x_1734_, 3);
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1746_ = v___x_1743_;
v_isShared_1747_ = v_isSharedCheck_1782_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1743_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1782_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1748_; lean_object* v_traceState_1749_; lean_object* v_env_1750_; lean_object* v_nextMacroScope_1751_; lean_object* v_ngen_1752_; lean_object* v_auxDeclNGen_1753_; lean_object* v_cache_1754_; lean_object* v_recordedDeps_1755_; lean_object* v_messages_1756_; lean_object* v_infoState_1757_; lean_object* v_snapshotTasks_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1781_; 
v___x_1748_ = lean_st_ref_take(v___y_1725_);
v_traceState_1749_ = lean_ctor_get(v___x_1748_, 4);
v_env_1750_ = lean_ctor_get(v___x_1748_, 0);
v_nextMacroScope_1751_ = lean_ctor_get(v___x_1748_, 1);
v_ngen_1752_ = lean_ctor_get(v___x_1748_, 2);
v_auxDeclNGen_1753_ = lean_ctor_get(v___x_1748_, 3);
v_cache_1754_ = lean_ctor_get(v___x_1748_, 5);
v_recordedDeps_1755_ = lean_ctor_get(v___x_1748_, 6);
v_messages_1756_ = lean_ctor_get(v___x_1748_, 7);
v_infoState_1757_ = lean_ctor_get(v___x_1748_, 8);
v_snapshotTasks_1758_ = lean_ctor_get(v___x_1748_, 9);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1760_ = v___x_1748_;
v_isShared_1761_ = v_isSharedCheck_1781_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_snapshotTasks_1758_);
lean_inc(v_infoState_1757_);
lean_inc(v_messages_1756_);
lean_inc(v_recordedDeps_1755_);
lean_inc(v_cache_1754_);
lean_inc(v_traceState_1749_);
lean_inc(v_auxDeclNGen_1753_);
lean_inc(v_ngen_1752_);
lean_inc(v_nextMacroScope_1751_);
lean_inc(v_env_1750_);
lean_dec(v___x_1748_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1781_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
uint64_t v_tid_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1779_; 
v_tid_1762_ = lean_ctor_get_uint64(v_traceState_1749_, sizeof(void*)*1);
v_isSharedCheck_1779_ = !lean_is_exclusive(v_traceState_1749_);
if (v_isSharedCheck_1779_ == 0)
{
lean_object* v_unused_1780_; 
v_unused_1780_ = lean_ctor_get(v_traceState_1749_, 0);
lean_dec(v_unused_1780_);
v___x_1764_ = v_traceState_1749_;
v_isShared_1765_ = v_isSharedCheck_1779_;
goto v_resetjp_1763_;
}
else
{
lean_dec(v_traceState_1749_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1779_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1770_; 
v___x_1766_ = lean_box(0);
v___x_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1767_, 0, v_ref_1720_);
lean_ctor_set(v___x_1767_, 1, v_a_1744_);
v___x_1768_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1718_, v___x_1767_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 0, v___x_1768_);
v___x_1770_ = v___x_1764_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1768_);
lean_ctor_set_uint64(v_reuseFailAlloc_1778_, sizeof(void*)*1, v_tid_1762_);
v___x_1770_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
lean_object* v___x_1772_; 
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 4, v___x_1770_);
v___x_1772_ = v___x_1760_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_env_1750_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_nextMacroScope_1751_);
lean_ctor_set(v_reuseFailAlloc_1777_, 2, v_ngen_1752_);
lean_ctor_set(v_reuseFailAlloc_1777_, 3, v_auxDeclNGen_1753_);
lean_ctor_set(v_reuseFailAlloc_1777_, 4, v___x_1770_);
lean_ctor_set(v_reuseFailAlloc_1777_, 5, v_cache_1754_);
lean_ctor_set(v_reuseFailAlloc_1777_, 6, v_recordedDeps_1755_);
lean_ctor_set(v_reuseFailAlloc_1777_, 7, v_messages_1756_);
lean_ctor_set(v_reuseFailAlloc_1777_, 8, v_infoState_1757_);
lean_ctor_set(v_reuseFailAlloc_1777_, 9, v_snapshotTasks_1758_);
v___x_1772_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1773_; lean_object* v___x_1775_; 
v___x_1773_ = lean_st_ref_put(v___y_1725_, v___x_1772_);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 0, v___x_1766_);
v___x_1775_ = v___x_1746_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1766_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2___boxed(lean_object* v_oldTraces_1783_, lean_object* v_data_1784_, lean_object* v_ref_1785_, lean_object* v_msg_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_1783_, v_data_1784_, v_ref_1785_, v_msg_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
return v_res_1792_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(lean_object* v_e_1793_){
_start:
{
if (lean_obj_tag(v_e_1793_) == 0)
{
uint8_t v___x_1794_; 
v___x_1794_ = 2;
return v___x_1794_;
}
else
{
uint8_t v___x_1795_; 
v___x_1795_ = 0;
return v___x_1795_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4___boxed(lean_object* v_e_1796_){
_start:
{
uint8_t v_res_1797_; lean_object* v_r_1798_; 
v_res_1797_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(v_e_1796_);
lean_dec_ref(v_e_1796_);
v_r_1798_ = lean_box(v_res_1797_);
return v_r_1798_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1799_; double v___x_1800_; 
v___x_1799_ = lean_unsigned_to_nat(0u);
v___x_1800_ = lean_float_of_nat(v___x_1799_);
return v___x_1800_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__1));
v___x_1803_ = l_Lean_stringToMessageData(v___x_1802_);
return v___x_1803_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1804_; double v___x_1805_; 
v___x_1804_ = lean_unsigned_to_nat(1000u);
v___x_1805_ = lean_float_of_nat(v___x_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(lean_object* v_cls_1806_, uint8_t v_collapsed_1807_, lean_object* v_tag_1808_, lean_object* v_opts_1809_, uint8_t v_clsEnabled_1810_, lean_object* v_oldTraces_1811_, lean_object* v_msg_1812_, lean_object* v_resStartStop_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v_fst_1819_; lean_object* v_snd_1820_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v_data_1824_; lean_object* v_fst_1835_; lean_object* v_snd_1836_; lean_object* v___x_1837_; uint8_t v___x_1838_; lean_object* v___y_1840_; lean_object* v_a_1841_; uint8_t v___y_1856_; double v___y_1888_; 
v_fst_1819_ = lean_ctor_get(v_resStartStop_1813_, 0);
lean_inc(v_fst_1819_);
v_snd_1820_ = lean_ctor_get(v_resStartStop_1813_, 1);
lean_inc(v_snd_1820_);
lean_dec_ref(v_resStartStop_1813_);
v_fst_1835_ = lean_ctor_get(v_snd_1820_, 0);
lean_inc(v_fst_1835_);
v_snd_1836_ = lean_ctor_get(v_snd_1820_, 1);
lean_inc(v_snd_1836_);
lean_dec(v_snd_1820_);
v___x_1837_ = l_Lean_trace_profiler;
v___x_1838_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1809_, v___x_1837_);
if (v___x_1838_ == 0)
{
v___y_1856_ = v___x_1838_;
goto v___jp_1855_;
}
else
{
lean_object* v___x_1893_; uint8_t v___x_1894_; 
v___x_1893_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1894_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_1809_, v___x_1893_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; lean_object* v___x_1896_; double v___x_1897_; double v___x_1898_; double v___x_1899_; 
v___x_1895_ = l_Lean_trace_profiler_threshold;
v___x_1896_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1809_, v___x_1895_);
v___x_1897_ = lean_float_of_nat(v___x_1896_);
v___x_1898_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3);
v___x_1899_ = lean_float_div(v___x_1897_, v___x_1898_);
v___y_1888_ = v___x_1899_;
goto v___jp_1887_;
}
else
{
lean_object* v___x_1900_; lean_object* v___x_1901_; double v___x_1902_; 
v___x_1900_ = l_Lean_trace_profiler_threshold;
v___x_1901_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_1809_, v___x_1900_);
v___x_1902_ = lean_float_of_nat(v___x_1901_);
v___y_1888_ = v___x_1902_;
goto v___jp_1887_;
}
}
v___jp_1821_:
{
lean_object* v___x_1825_; 
lean_inc(v___y_1822_);
v___x_1825_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_1811_, v_data_1824_, v___y_1822_, v___y_1823_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v___x_1826_; 
lean_dec_ref_known(v___x_1825_, 1);
v___x_1826_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_1819_);
return v___x_1826_;
}
else
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1834_; 
lean_dec(v_fst_1819_);
v_a_1827_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1829_ = v___x_1825_;
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1825_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1827_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
}
v___jp_1839_:
{
uint8_t v_result_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; double v___x_1845_; lean_object* v_data_1846_; 
v_result_1842_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__4(v_fst_1819_);
v___x_1843_ = lean_box(v_result_1842_);
v___x_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
v___x_1845_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0);
lean_inc_ref(v_tag_1808_);
lean_inc_ref(v___x_1844_);
lean_inc(v_cls_1806_);
v_data_1846_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1846_, 0, v_cls_1806_);
lean_ctor_set(v_data_1846_, 1, v___x_1844_);
lean_ctor_set(v_data_1846_, 2, v_tag_1808_);
lean_ctor_set_float(v_data_1846_, sizeof(void*)*3, v___x_1845_);
lean_ctor_set_float(v_data_1846_, sizeof(void*)*3 + 8, v___x_1845_);
lean_ctor_set_uint8(v_data_1846_, sizeof(void*)*3 + 16, v_collapsed_1807_);
if (v___x_1838_ == 0)
{
lean_dec_ref_known(v___x_1844_, 1);
lean_dec(v_snd_1836_);
lean_dec(v_fst_1835_);
lean_dec_ref(v_tag_1808_);
lean_dec(v_cls_1806_);
v___y_1822_ = v___y_1840_;
v___y_1823_ = v_a_1841_;
v_data_1824_ = v_data_1846_;
goto v___jp_1821_;
}
else
{
lean_object* v_data_1847_; double v___x_1848_; double v___x_1849_; 
lean_dec_ref_known(v_data_1846_, 3);
v_data_1847_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1847_, 0, v_cls_1806_);
lean_ctor_set(v_data_1847_, 1, v___x_1844_);
lean_ctor_set(v_data_1847_, 2, v_tag_1808_);
v___x_1848_ = lean_unbox_float(v_fst_1835_);
lean_dec(v_fst_1835_);
lean_ctor_set_float(v_data_1847_, sizeof(void*)*3, v___x_1848_);
v___x_1849_ = lean_unbox_float(v_snd_1836_);
lean_dec(v_snd_1836_);
lean_ctor_set_float(v_data_1847_, sizeof(void*)*3 + 8, v___x_1849_);
lean_ctor_set_uint8(v_data_1847_, sizeof(void*)*3 + 16, v_collapsed_1807_);
v___y_1822_ = v___y_1840_;
v___y_1823_ = v_a_1841_;
v_data_1824_ = v_data_1847_;
goto v___jp_1821_;
}
}
v___jp_1850_:
{
lean_object* v_ref_1851_; lean_object* v___x_1852_; 
v_ref_1851_ = lean_ctor_get(v___y_1816_, 2);
lean_inc(v___y_1817_);
lean_inc_ref(v___y_1816_);
lean_inc(v___y_1815_);
lean_inc_ref(v___y_1814_);
lean_inc(v_fst_1819_);
v___x_1852_ = lean_apply_6(v_msg_1812_, v_fst_1819_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, lean_box(0));
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_a_1853_);
lean_dec_ref_known(v___x_1852_, 1);
v___y_1840_ = v_ref_1851_;
v_a_1841_ = v_a_1853_;
goto v___jp_1839_;
}
else
{
lean_object* v___x_1854_; 
lean_dec_ref_known(v___x_1852_, 1);
v___x_1854_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2);
v___y_1840_ = v_ref_1851_;
v_a_1841_ = v___x_1854_;
goto v___jp_1839_;
}
}
v___jp_1855_:
{
if (v_clsEnabled_1810_ == 0)
{
if (v___y_1856_ == 0)
{
lean_object* v___x_1857_; lean_object* v_traceState_1858_; lean_object* v_env_1859_; lean_object* v_nextMacroScope_1860_; lean_object* v_ngen_1861_; lean_object* v_auxDeclNGen_1862_; lean_object* v_cache_1863_; lean_object* v_recordedDeps_1864_; lean_object* v_messages_1865_; lean_object* v_infoState_1866_; lean_object* v_snapshotTasks_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1886_; 
lean_dec(v_snd_1836_);
lean_dec(v_fst_1835_);
lean_dec_ref(v_msg_1812_);
lean_dec_ref(v_tag_1808_);
lean_dec(v_cls_1806_);
v___x_1857_ = lean_st_ref_take(v___y_1817_);
v_traceState_1858_ = lean_ctor_get(v___x_1857_, 4);
v_env_1859_ = lean_ctor_get(v___x_1857_, 0);
v_nextMacroScope_1860_ = lean_ctor_get(v___x_1857_, 1);
v_ngen_1861_ = lean_ctor_get(v___x_1857_, 2);
v_auxDeclNGen_1862_ = lean_ctor_get(v___x_1857_, 3);
v_cache_1863_ = lean_ctor_get(v___x_1857_, 5);
v_recordedDeps_1864_ = lean_ctor_get(v___x_1857_, 6);
v_messages_1865_ = lean_ctor_get(v___x_1857_, 7);
v_infoState_1866_ = lean_ctor_get(v___x_1857_, 8);
v_snapshotTasks_1867_ = lean_ctor_get(v___x_1857_, 9);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1869_ = v___x_1857_;
v_isShared_1870_ = v_isSharedCheck_1886_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_snapshotTasks_1867_);
lean_inc(v_infoState_1866_);
lean_inc(v_messages_1865_);
lean_inc(v_recordedDeps_1864_);
lean_inc(v_cache_1863_);
lean_inc(v_traceState_1858_);
lean_inc(v_auxDeclNGen_1862_);
lean_inc(v_ngen_1861_);
lean_inc(v_nextMacroScope_1860_);
lean_inc(v_env_1859_);
lean_dec(v___x_1857_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1886_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
uint64_t v_tid_1871_; lean_object* v_traces_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1885_; 
v_tid_1871_ = lean_ctor_get_uint64(v_traceState_1858_, sizeof(void*)*1);
v_traces_1872_ = lean_ctor_get(v_traceState_1858_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v_traceState_1858_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1874_ = v_traceState_1858_;
v_isShared_1875_ = v_isSharedCheck_1885_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_traces_1872_);
lean_dec(v_traceState_1858_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1885_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1876_; lean_object* v___x_1878_; 
v___x_1876_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1811_, v_traces_1872_);
lean_dec_ref(v_traces_1872_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v___x_1876_);
v___x_1878_ = v___x_1874_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1876_);
lean_ctor_set_uint64(v_reuseFailAlloc_1884_, sizeof(void*)*1, v_tid_1871_);
v___x_1878_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1880_; 
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 4, v___x_1878_);
v___x_1880_ = v___x_1869_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_env_1859_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_nextMacroScope_1860_);
lean_ctor_set(v_reuseFailAlloc_1883_, 2, v_ngen_1861_);
lean_ctor_set(v_reuseFailAlloc_1883_, 3, v_auxDeclNGen_1862_);
lean_ctor_set(v_reuseFailAlloc_1883_, 4, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1883_, 5, v_cache_1863_);
lean_ctor_set(v_reuseFailAlloc_1883_, 6, v_recordedDeps_1864_);
lean_ctor_set(v_reuseFailAlloc_1883_, 7, v_messages_1865_);
lean_ctor_set(v_reuseFailAlloc_1883_, 8, v_infoState_1866_);
lean_ctor_set(v_reuseFailAlloc_1883_, 9, v_snapshotTasks_1867_);
v___x_1880_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1881_ = lean_st_ref_put(v___y_1817_, v___x_1880_);
v___x_1882_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_1819_);
return v___x_1882_;
}
}
}
}
}
else
{
goto v___jp_1850_;
}
}
else
{
goto v___jp_1850_;
}
}
v___jp_1887_:
{
double v___x_1889_; double v___x_1890_; double v___x_1891_; uint8_t v___x_1892_; 
v___x_1889_ = lean_unbox_float(v_snd_1836_);
v___x_1890_ = lean_unbox_float(v_fst_1835_);
v___x_1891_ = lean_float_sub(v___x_1889_, v___x_1890_);
v___x_1892_ = lean_float_decLt(v___y_1888_, v___x_1891_);
v___y_1856_ = v___x_1892_;
goto v___jp_1855_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___boxed(lean_object* v_cls_1903_, lean_object* v_collapsed_1904_, lean_object* v_tag_1905_, lean_object* v_opts_1906_, lean_object* v_clsEnabled_1907_, lean_object* v_oldTraces_1908_, lean_object* v_msg_1909_, lean_object* v_resStartStop_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
uint8_t v_collapsed_boxed_1916_; uint8_t v_clsEnabled_boxed_1917_; lean_object* v_res_1918_; 
v_collapsed_boxed_1916_ = lean_unbox(v_collapsed_1904_);
v_clsEnabled_boxed_1917_ = lean_unbox(v_clsEnabled_1907_);
v_res_1918_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v_cls_1903_, v_collapsed_boxed_1916_, v_tag_1905_, v_opts_1906_, v_clsEnabled_boxed_1917_, v_oldTraces_1908_, v_msg_1909_, v_resStartStop_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec_ref(v_opts_1906_);
return v_res_1918_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2(void){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1922_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_1923_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__1));
v___x_1924_ = l_Lean_Name_append(v___x_1923_, v___x_1922_);
return v___x_1924_;
}
}
static double _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3(void){
_start:
{
lean_object* v___x_1925_; double v___x_1926_; 
v___x_1925_ = lean_unsigned_to_nat(1000000000u);
v___x_1926_ = lean_float_of_nat(v___x_1925_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(lean_object* v_cfg_1927_, lean_object* v_act_1928_, lean_object* v_allowFailure_1929_, lean_object* v_cand_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_){
_start:
{
lean_object* v_fst_1936_; lean_object* v_snd_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_2224_; 
v_fst_1936_ = lean_ctor_get(v_cand_1930_, 0);
v_snd_1937_ = lean_ctor_get(v_cand_1930_, 1);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_cand_1930_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_1939_ = v_cand_1930_;
v_isShared_1940_ = v_isSharedCheck_2224_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_snd_1937_);
lean_inc(v_fst_1936_);
lean_dec(v_cand_1930_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_2224_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v_toCold_1941_; lean_object* v_options_1942_; uint8_t v_hasTrace_1943_; 
v_toCold_1941_ = lean_ctor_get(v_a_1933_, 0);
v_options_1942_ = lean_ctor_get(v_toCold_1941_, 2);
v_hasTrace_1943_ = lean_ctor_get_uint8(v_options_1942_, sizeof(void*)*1);
if (v_hasTrace_1943_ == 0)
{
lean_object* v_fst_1944_; lean_object* v_snd_1945_; lean_object* v_fst_1946_; lean_object* v_snd_1947_; lean_object* v___x_1948_; lean_object* v_cache_1949_; lean_object* v_zetaDeltaFVarIds_1950_; lean_object* v_postponed_1951_; lean_object* v_diag_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_2000_; 
lean_del_object(v___x_1939_);
v_fst_1944_ = lean_ctor_get(v_fst_1936_, 0);
lean_inc(v_fst_1944_);
v_snd_1945_ = lean_ctor_get(v_fst_1936_, 1);
lean_inc(v_snd_1945_);
lean_dec(v_fst_1936_);
v_fst_1946_ = lean_ctor_get(v_snd_1937_, 0);
lean_inc(v_fst_1946_);
v_snd_1947_ = lean_ctor_get(v_snd_1937_, 1);
lean_inc(v_snd_1947_);
lean_dec(v_snd_1937_);
v___x_1948_ = lean_st_ref_take(v_a_1932_);
v_cache_1949_ = lean_ctor_get(v___x_1948_, 1);
v_zetaDeltaFVarIds_1950_ = lean_ctor_get(v___x_1948_, 2);
v_postponed_1951_ = lean_ctor_get(v___x_1948_, 3);
v_diag_1952_ = lean_ctor_get(v___x_1948_, 4);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_2000_ == 0)
{
lean_object* v_unused_2001_; 
v_unused_2001_ = lean_ctor_get(v___x_1948_, 0);
lean_dec(v_unused_2001_);
v___x_1954_ = v___x_1948_;
v_isShared_1955_ = v_isSharedCheck_2000_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_diag_1952_);
lean_inc(v_postponed_1951_);
lean_inc(v_zetaDeltaFVarIds_1950_);
lean_inc(v_cache_1949_);
lean_dec(v___x_1948_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_2000_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 0, v_snd_1945_);
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_snd_1945_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_cache_1949_);
lean_ctor_set(v_reuseFailAlloc_1999_, 2, v_zetaDeltaFVarIds_1950_);
lean_ctor_set(v_reuseFailAlloc_1999_, 3, v_postponed_1951_);
lean_ctor_set(v_reuseFailAlloc_1999_, 4, v_diag_1952_);
v___x_1957_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
lean_object* v___x_1958_; uint8_t v___x_1959_; lean_object* v___x_1960_; 
v___x_1958_ = lean_st_ref_put(v_a_1932_, v___x_1957_);
v___x_1959_ = lean_unbox(v_snd_1947_);
lean_dec(v_snd_1947_);
v___x_1960_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_1946_, v___x_1959_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1961_);
lean_dec_ref_known(v___x_1960_, 1);
v___x_1962_ = lean_box(0);
lean_inc(v_fst_1944_);
v___x_1963_ = l_Lean_MVarId_apply(v_fst_1944_, v_a_1961_, v_cfg_1927_, v___x_1962_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v_a_1964_; lean_object* v___x_1965_; 
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
lean_inc_n(v_a_1964_, 2);
lean_dec_ref_known(v___x_1963_, 1);
lean_inc(v_a_1934_);
lean_inc_ref(v_a_1933_);
lean_inc(v_a_1932_);
lean_inc_ref(v_a_1931_);
v___x_1965_ = lean_apply_6(v_act_1928_, v_a_1964_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, lean_box(0));
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_dec(v_a_1964_);
lean_dec(v_fst_1944_);
lean_dec_ref(v_allowFailure_1929_);
return v___x_1965_;
}
else
{
lean_object* v_a_1966_; uint8_t v___y_1968_; uint8_t v___x_1989_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1966_);
v___x_1989_ = l_Lean_Exception_isInterrupt(v_a_1966_);
if (v___x_1989_ == 0)
{
uint8_t v___x_1990_; 
v___x_1990_ = l_Lean_Exception_isRuntime(v_a_1966_);
v___y_1968_ = v___x_1990_;
goto v___jp_1967_;
}
else
{
lean_dec(v_a_1966_);
v___y_1968_ = v___x_1989_;
goto v___jp_1967_;
}
v___jp_1967_:
{
if (v___y_1968_ == 0)
{
lean_object* v___x_1969_; 
lean_dec_ref_known(v___x_1965_, 1);
lean_inc(v_a_1934_);
lean_inc_ref(v_a_1933_);
lean_inc(v_a_1932_);
lean_inc_ref(v_a_1931_);
v___x_1969_ = lean_apply_6(v_allowFailure_1929_, v_fst_1944_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, lean_box(0));
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1980_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_1980_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1980_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
uint8_t v___x_1974_; 
v___x_1974_ = lean_unbox(v_a_1970_);
lean_dec(v_a_1970_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
lean_del_object(v___x_1972_);
lean_dec(v_a_1964_);
v___x_1975_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1);
v___x_1976_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_1975_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
return v___x_1976_;
}
else
{
lean_object* v___x_1978_; 
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v_a_1964_);
v___x_1978_ = v___x_1972_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1964_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
lean_dec(v_a_1964_);
v_a_1981_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1969_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1969_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
else
{
lean_dec(v_a_1964_);
lean_dec(v_fst_1944_);
lean_dec_ref(v_allowFailure_1929_);
return v___x_1965_;
}
}
}
}
else
{
lean_dec(v_fst_1944_);
lean_dec_ref(v_allowFailure_1929_);
lean_dec_ref(v_act_1928_);
return v___x_1963_;
}
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
lean_dec(v_fst_1944_);
lean_dec_ref(v_allowFailure_1929_);
lean_dec_ref(v_act_1928_);
lean_dec_ref(v_cfg_1927_);
v_a_1991_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___x_1960_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1960_);
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
lean_object* v_fst_2002_; lean_object* v_snd_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2223_; 
v_fst_2002_ = lean_ctor_get(v_fst_1936_, 0);
v_snd_2003_ = lean_ctor_get(v_fst_1936_, 1);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_fst_1936_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2005_ = v_fst_1936_;
v_isShared_2006_ = v_isSharedCheck_2223_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_snd_2003_);
lean_inc(v_fst_2002_);
lean_dec(v_fst_1936_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2223_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v_fst_2007_; lean_object* v_snd_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2222_; 
v_fst_2007_ = lean_ctor_get(v_snd_1937_, 0);
v_snd_2008_ = lean_ctor_get(v_snd_1937_, 1);
v_isSharedCheck_2222_ = !lean_is_exclusive(v_snd_1937_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2010_ = v_snd_1937_;
v_isShared_2011_ = v_isSharedCheck_2222_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_snd_2008_);
lean_inc(v_fst_2007_);
lean_dec(v_snd_1937_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2222_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v_inheritedTraceOptions_2012_; lean_object* v___f_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; uint8_t v___x_2017_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v_a_2021_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v_a_2040_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v_a_2045_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; uint8_t v___y_2058_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v_a_2068_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v_a_2082_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v_a_2087_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; uint8_t v___y_2100_; 
v_inheritedTraceOptions_2012_ = lean_ctor_get(v_toCold_1941_, 11);
lean_inc(v_snd_2008_);
lean_inc(v_fst_2007_);
v___f_2013_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2013_, 0, v_fst_2007_);
lean_closure_set(v___f_2013_, 1, v_snd_2008_);
v___x_2014_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_2015_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4));
v___x_2016_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2);
v___x_2017_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2012_, v_options_1942_, v___x_2016_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2166_; uint8_t v___x_2167_; 
v___x_2166_ = l_Lean_trace_profiler;
v___x_2167_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_1942_, v___x_2166_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; lean_object* v_cache_2169_; lean_object* v_zetaDeltaFVarIds_2170_; lean_object* v_postponed_2171_; lean_object* v_diag_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2220_; 
lean_dec_ref(v___f_2013_);
lean_del_object(v___x_2010_);
lean_del_object(v___x_2005_);
lean_del_object(v___x_1939_);
v___x_2168_ = lean_st_ref_take(v_a_1932_);
v_cache_2169_ = lean_ctor_get(v___x_2168_, 1);
v_zetaDeltaFVarIds_2170_ = lean_ctor_get(v___x_2168_, 2);
v_postponed_2171_ = lean_ctor_get(v___x_2168_, 3);
v_diag_2172_ = lean_ctor_get(v___x_2168_, 4);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2220_ == 0)
{
lean_object* v_unused_2221_; 
v_unused_2221_ = lean_ctor_get(v___x_2168_, 0);
lean_dec(v_unused_2221_);
v___x_2174_ = v___x_2168_;
v_isShared_2175_ = v_isSharedCheck_2220_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_diag_2172_);
lean_inc(v_postponed_2171_);
lean_inc(v_zetaDeltaFVarIds_2170_);
lean_inc(v_cache_2169_);
lean_dec(v___x_2168_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2220_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v_snd_2003_);
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_snd_2003_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v_cache_2169_);
lean_ctor_set(v_reuseFailAlloc_2219_, 2, v_zetaDeltaFVarIds_2170_);
lean_ctor_set(v_reuseFailAlloc_2219_, 3, v_postponed_2171_);
lean_ctor_set(v_reuseFailAlloc_2219_, 4, v_diag_2172_);
v___x_2177_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
lean_object* v___x_2178_; uint8_t v___x_2179_; lean_object* v___x_2180_; 
v___x_2178_ = lean_st_ref_put(v_a_1932_, v___x_2177_);
v___x_2179_ = lean_unbox(v_snd_2008_);
lean_dec(v_snd_2008_);
v___x_2180_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2007_, v___x_2179_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2181_);
lean_dec_ref_known(v___x_2180_, 1);
v___x_2182_ = lean_box(0);
lean_inc(v_fst_2002_);
v___x_2183_ = l_Lean_MVarId_apply(v_fst_2002_, v_a_2181_, v_cfg_1927_, v___x_2182_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v___x_2185_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc_n(v_a_2184_, 2);
lean_dec_ref_known(v___x_2183_, 1);
lean_inc(v_a_1934_);
lean_inc_ref(v_a_1933_);
lean_inc(v_a_1932_);
lean_inc_ref(v_a_1931_);
v___x_2185_ = lean_apply_6(v_act_1928_, v_a_2184_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, lean_box(0));
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_dec(v_a_2184_);
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1929_);
return v___x_2185_;
}
else
{
lean_object* v_a_2186_; uint8_t v___y_2188_; uint8_t v___x_2209_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
v___x_2209_ = l_Lean_Exception_isInterrupt(v_a_2186_);
if (v___x_2209_ == 0)
{
uint8_t v___x_2210_; 
v___x_2210_ = l_Lean_Exception_isRuntime(v_a_2186_);
v___y_2188_ = v___x_2210_;
goto v___jp_2187_;
}
else
{
lean_dec(v_a_2186_);
v___y_2188_ = v___x_2209_;
goto v___jp_2187_;
}
v___jp_2187_:
{
if (v___y_2188_ == 0)
{
lean_object* v___x_2189_; 
lean_dec_ref_known(v___x_2185_, 1);
lean_inc(v_a_1934_);
lean_inc_ref(v_a_1933_);
lean_inc(v_a_1932_);
lean_inc_ref(v_a_1931_);
v___x_2189_ = lean_apply_6(v_allowFailure_1929_, v_fst_2002_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, lean_box(0));
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2200_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2192_ = v___x_2189_;
v_isShared_2193_ = v_isSharedCheck_2200_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2189_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2200_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
uint8_t v___x_2194_; 
v___x_2194_ = lean_unbox(v_a_2190_);
lean_dec(v_a_2190_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
lean_del_object(v___x_2192_);
lean_dec(v_a_2184_);
v___x_2195_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1);
v___x_2196_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2195_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
return v___x_2196_;
}
else
{
lean_object* v___x_2198_; 
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v_a_2184_);
v___x_2198_ = v___x_2192_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2184_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
lean_dec(v_a_2184_);
v_a_2201_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2189_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2189_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
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
return v___x_2206_;
}
}
}
}
else
{
lean_dec(v_a_2184_);
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1929_);
return v___x_2185_;
}
}
}
}
else
{
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1929_);
lean_dec_ref(v_act_1928_);
return v___x_2183_;
}
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1929_);
lean_dec_ref(v_act_1928_);
lean_dec_ref(v_cfg_1927_);
v_a_2211_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2180_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2180_);
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
}
}
else
{
goto v___jp_2107_;
}
}
else
{
goto v___jp_2107_;
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
v___x_2034_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v___x_2014_, v_hasTrace_1943_, v___x_2015_, v_options_1942_, v___x_2017_, v___y_2020_, v___f_2013_, v___x_2033_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
return v___x_2034_;
}
}
}
v___jp_2037_:
{
lean_object* v___x_2041_; 
v___x_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2041_, 0, v_a_2040_);
v___y_2019_ = v___y_2038_;
v___y_2020_ = v___y_2039_;
v_a_2021_ = v___x_2041_;
goto v___jp_2018_;
}
v___jp_2042_:
{
lean_object* v___x_2046_; 
v___x_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2046_, 0, v_a_2045_);
v___y_2019_ = v___y_2043_;
v___y_2020_ = v___y_2044_;
v_a_2021_ = v___x_2046_;
goto v___jp_2018_;
}
v___jp_2047_:
{
if (lean_obj_tag(v___y_2050_) == 0)
{
lean_object* v_a_2051_; 
v_a_2051_ = lean_ctor_get(v___y_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref_known(v___y_2050_, 1);
v___y_2038_ = v___y_2048_;
v___y_2039_ = v___y_2049_;
v_a_2040_ = v_a_2051_;
goto v___jp_2037_;
}
else
{
lean_object* v_a_2052_; 
v_a_2052_ = lean_ctor_get(v___y_2050_, 0);
lean_inc(v_a_2052_);
lean_dec_ref_known(v___y_2050_, 1);
v___y_2043_ = v___y_2048_;
v___y_2044_ = v___y_2049_;
v_a_2045_ = v_a_2052_;
goto v___jp_2042_;
}
}
v___jp_2053_:
{
if (v___y_2058_ == 0)
{
lean_object* v___x_2059_; 
lean_dec_ref(v___y_2054_);
lean_inc(v_a_1934_);
lean_inc_ref(v_a_1933_);
lean_inc(v_a_1932_);
lean_inc_ref(v_a_1931_);
v___x_2059_ = lean_apply_6(v_allowFailure_1929_, v_fst_2002_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, lean_box(0));
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v_a_2060_; uint8_t v___x_2061_; 
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
lean_inc(v_a_2060_);
lean_dec_ref_known(v___x_2059_, 1);
v___x_2061_ = lean_unbox(v_a_2060_);
lean_dec(v_a_2060_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
lean_dec(v___y_2056_);
v___x_2062_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1);
v___x_2063_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2062_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
v___y_2048_ = v___y_2055_;
v___y_2049_ = v___y_2057_;
v___y_2050_ = v___x_2063_;
goto v___jp_2047_;
}
else
{
v___y_2038_ = v___y_2055_;
v___y_2039_ = v___y_2057_;
v_a_2040_ = v___y_2056_;
goto v___jp_2037_;
}
}
else
{
lean_object* v_a_2064_; 
lean_dec(v___y_2056_);
v_a_2064_ = lean_ctor_get(v___x_2059_, 0);
lean_inc(v_a_2064_);
lean_dec_ref_known(v___x_2059_, 1);
v___y_2043_ = v___y_2055_;
v___y_2044_ = v___y_2057_;
v_a_2045_ = v_a_2064_;
goto v___jp_2042_;
}
}
else
{
lean_dec(v___y_2056_);
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1929_);
v___y_2043_ = v___y_2055_;
v___y_2044_ = v___y_2057_;
v_a_2045_ = v___y_2054_;
goto v___jp_2042_;
}
}
v___jp_2065_:
{
lean_object* v___x_2069_; double v___x_2070_; double v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2075_; 
v___x_2069_ = lean_io_get_num_heartbeats();
v___x_2070_ = lean_float_of_nat(v___y_2067_);
v___x_2071_ = lean_float_of_nat(v___x_2069_);
v___x_2072_ = lean_box_float(v___x_2070_);
v___x_2073_ = lean_box_float(v___x_2071_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 1, v___x_2073_);
lean_ctor_set(v___x_1939_, 0, v___x_2072_);
v___x_2075_ = v___x_1939_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2072_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v___x_2073_);
v___x_2075_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2076_, 0, v_a_2068_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
v___x_2077_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2(v___x_2014_, v_hasTrace_1943_, v___x_2015_, v_options_1942_, v___x_2017_, v___y_2066_, v___f_2013_, v___x_2076_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
return v___x_2077_;
}
}
v___jp_2079_:
{
lean_object* v___x_2083_; 
v___x_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2083_, 0, v_a_2082_);
v___y_2066_ = v___y_2080_;
v___y_2067_ = v___y_2081_;
v_a_2068_ = v___x_2083_;
goto v___jp_2065_;
}
v___jp_2084_:
{
lean_object* v___x_2088_; 
v___x_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2088_, 0, v_a_2087_);
v___y_2066_ = v___y_2085_;
v___y_2067_ = v___y_2086_;
v_a_2068_ = v___x_2088_;
goto v___jp_2065_;
}
v___jp_2089_:
{
if (lean_obj_tag(v___y_2092_) == 0)
{
lean_object* v_a_2093_; 
v_a_2093_ = lean_ctor_get(v___y_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___y_2092_, 1);
v___y_2080_ = v___y_2090_;
v___y_2081_ = v___y_2091_;
v_a_2082_ = v_a_2093_;
goto v___jp_2079_;
}
else
{
lean_object* v_a_2094_; 
v_a_2094_ = lean_ctor_get(v___y_2092_, 0);
lean_inc(v_a_2094_);
lean_dec_ref_known(v___y_2092_, 1);
v___y_2085_ = v___y_2090_;
v___y_2086_ = v___y_2091_;
v_a_2087_ = v_a_2094_;
goto v___jp_2084_;
}
}
v___jp_2095_:
{
if (v___y_2100_ == 0)
{
lean_object* v___x_2101_; 
lean_dec_ref(v___y_2098_);
lean_inc(v_a_1934_);
lean_inc_ref(v_a_1933_);
lean_inc(v_a_1932_);
lean_inc_ref(v_a_1931_);
v___x_2101_ = lean_apply_6(v_allowFailure_1929_, v_fst_2002_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, lean_box(0));
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; uint8_t v___x_2103_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref_known(v___x_2101_, 1);
v___x_2103_ = lean_unbox(v_a_2102_);
lean_dec(v_a_2102_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
lean_dec(v___y_2099_);
v___x_2104_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1, &l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_LibrarySearch_solveByElim___lam__2___closed__1);
v___x_2105_ = l_Lean_throwError___at___00Lean_Meta_LibrarySearch_solveByElim_spec__0___redArg(v___x_2104_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
v___y_2090_ = v___y_2096_;
v___y_2091_ = v___y_2097_;
v___y_2092_ = v___x_2105_;
goto v___jp_2089_;
}
else
{
v___y_2080_ = v___y_2096_;
v___y_2081_ = v___y_2097_;
v_a_2082_ = v___y_2099_;
goto v___jp_2079_;
}
}
else
{
lean_object* v_a_2106_; 
lean_dec(v___y_2099_);
v_a_2106_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2106_);
lean_dec_ref_known(v___x_2101_, 1);
v___y_2085_ = v___y_2096_;
v___y_2086_ = v___y_2097_;
v_a_2087_ = v_a_2106_;
goto v___jp_2084_;
}
}
else
{
lean_dec(v___y_2099_);
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1929_);
v___y_2085_ = v___y_2096_;
v___y_2086_ = v___y_2097_;
v_a_2087_ = v___y_2098_;
goto v___jp_2084_;
}
}
v___jp_2107_:
{
lean_object* v___x_2108_; lean_object* v_a_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2108_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v_a_1934_);
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref(v___x_2108_);
v___x_2110_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2111_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_1942_, v___x_2110_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v_cache_2114_; lean_object* v_zetaDeltaFVarIds_2115_; lean_object* v_postponed_2116_; lean_object* v_diag_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2137_; 
lean_del_object(v___x_1939_);
v___x_2112_ = lean_io_mono_nanos_now();
v___x_2113_ = lean_st_ref_take(v_a_1932_);
v_cache_2114_ = lean_ctor_get(v___x_2113_, 1);
v_zetaDeltaFVarIds_2115_ = lean_ctor_get(v___x_2113_, 2);
v_postponed_2116_ = lean_ctor_get(v___x_2113_, 3);
v_diag_2117_ = lean_ctor_get(v___x_2113_, 4);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2137_ == 0)
{
lean_object* v_unused_2138_; 
v_unused_2138_ = lean_ctor_get(v___x_2113_, 0);
lean_dec(v_unused_2138_);
v___x_2119_ = v___x_2113_;
v_isShared_2120_ = v_isSharedCheck_2137_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_diag_2117_);
lean_inc(v_postponed_2116_);
lean_inc(v_zetaDeltaFVarIds_2115_);
lean_inc(v_cache_2114_);
lean_dec(v___x_2113_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2137_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 0, v_snd_2003_);
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_snd_2003_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_cache_2114_);
lean_ctor_set(v_reuseFailAlloc_2136_, 2, v_zetaDeltaFVarIds_2115_);
lean_ctor_set(v_reuseFailAlloc_2136_, 3, v_postponed_2116_);
lean_ctor_set(v_reuseFailAlloc_2136_, 4, v_diag_2117_);
v___x_2122_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2123_; uint8_t v___x_2124_; lean_object* v___x_2125_; 
v___x_2123_ = lean_st_ref_put(v_a_1932_, v___x_2122_);
v___x_2124_ = lean_unbox(v_snd_2008_);
lean_dec(v_snd_2008_);
v___x_2125_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2007_, v___x_2124_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2125_, 1);
v___x_2127_ = lean_box(0);
lean_inc(v_fst_2002_);
v___x_2128_ = l_Lean_MVarId_apply(v_fst_2002_, v_a_2126_, v_cfg_1927_, v___x_2127_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2130_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc_n(v_a_2129_, 2);
lean_dec_ref_known(v___x_2128_, 1);
lean_inc(v_a_1934_);
lean_inc_ref(v_a_1933_);
lean_inc(v_a_1932_);
lean_inc_ref(v_a_1931_);
v___x_2130_ = lean_apply_6(v_act_1928_, v_a_2129_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, lean_box(0));
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; 
lean_dec(v_a_2129_);
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1929_);
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v___y_2038_ = v___x_2112_;
v___y_2039_ = v_a_2109_;
v_a_2040_ = v_a_2131_;
goto v___jp_2037_;
}
else
{
lean_object* v_a_2132_; uint8_t v___x_2133_; 
v_a_2132_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2130_, 1);
v___x_2133_ = l_Lean_Exception_isInterrupt(v_a_2132_);
if (v___x_2133_ == 0)
{
uint8_t v___x_2134_; 
lean_inc(v_a_2132_);
v___x_2134_ = l_Lean_Exception_isRuntime(v_a_2132_);
v___y_2054_ = v_a_2132_;
v___y_2055_ = v___x_2112_;
v___y_2056_ = v_a_2129_;
v___y_2057_ = v_a_2109_;
v___y_2058_ = v___x_2134_;
goto v___jp_2053_;
}
else
{
v___y_2054_ = v_a_2132_;
v___y_2055_ = v___x_2112_;
v___y_2056_ = v_a_2129_;
v___y_2057_ = v_a_2109_;
v___y_2058_ = v___x_2133_;
goto v___jp_2053_;
}
}
}
else
{
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1929_);
lean_dec_ref(v_act_1928_);
v___y_2048_ = v___x_2112_;
v___y_2049_ = v_a_2109_;
v___y_2050_ = v___x_2128_;
goto v___jp_2047_;
}
}
else
{
lean_object* v_a_2135_; 
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1929_);
lean_dec_ref(v_act_1928_);
lean_dec_ref(v_cfg_1927_);
v_a_2135_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2125_, 1);
v___y_2043_ = v___x_2112_;
v___y_2044_ = v_a_2109_;
v_a_2045_ = v_a_2135_;
goto v___jp_2042_;
}
}
}
}
else
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v_cache_2141_; lean_object* v_zetaDeltaFVarIds_2142_; lean_object* v_postponed_2143_; lean_object* v_diag_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2164_; 
lean_del_object(v___x_2010_);
lean_del_object(v___x_2005_);
v___x_2139_ = lean_io_get_num_heartbeats();
v___x_2140_ = lean_st_ref_take(v_a_1932_);
v_cache_2141_ = lean_ctor_get(v___x_2140_, 1);
v_zetaDeltaFVarIds_2142_ = lean_ctor_get(v___x_2140_, 2);
v_postponed_2143_ = lean_ctor_get(v___x_2140_, 3);
v_diag_2144_ = lean_ctor_get(v___x_2140_, 4);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2164_ == 0)
{
lean_object* v_unused_2165_; 
v_unused_2165_ = lean_ctor_get(v___x_2140_, 0);
lean_dec(v_unused_2165_);
v___x_2146_ = v___x_2140_;
v_isShared_2147_ = v_isSharedCheck_2164_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_diag_2144_);
lean_inc(v_postponed_2143_);
lean_inc(v_zetaDeltaFVarIds_2142_);
lean_inc(v_cache_2141_);
lean_dec(v___x_2140_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2164_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v_snd_2003_);
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_snd_2003_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_cache_2141_);
lean_ctor_set(v_reuseFailAlloc_2163_, 2, v_zetaDeltaFVarIds_2142_);
lean_ctor_set(v_reuseFailAlloc_2163_, 3, v_postponed_2143_);
lean_ctor_set(v_reuseFailAlloc_2163_, 4, v_diag_2144_);
v___x_2149_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
lean_object* v___x_2150_; uint8_t v___x_2151_; lean_object* v___x_2152_; 
v___x_2150_ = lean_st_ref_put(v_a_1932_, v___x_2149_);
v___x_2151_ = lean_unbox(v_snd_2008_);
lean_dec(v_snd_2008_);
v___x_2152_ = l_Lean_Meta_LibrarySearch_mkLibrarySearchLemma(v_fst_2007_, v___x_2151_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v_a_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_a_2153_);
lean_dec_ref_known(v___x_2152_, 1);
v___x_2154_ = lean_box(0);
lean_inc(v_fst_2002_);
v___x_2155_ = l_Lean_MVarId_apply(v_fst_2002_, v_a_2153_, v_cfg_1927_, v___x_2154_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v___x_2157_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
lean_inc_n(v_a_2156_, 2);
lean_dec_ref_known(v___x_2155_, 1);
lean_inc(v_a_1934_);
lean_inc_ref(v_a_1933_);
lean_inc(v_a_1932_);
lean_inc_ref(v_a_1931_);
v___x_2157_ = lean_apply_6(v_act_1928_, v_a_2156_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, lean_box(0));
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; 
lean_dec(v_a_2156_);
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1929_);
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2158_);
lean_dec_ref_known(v___x_2157_, 1);
v___y_2080_ = v_a_2109_;
v___y_2081_ = v___x_2139_;
v_a_2082_ = v_a_2158_;
goto v___jp_2079_;
}
else
{
lean_object* v_a_2159_; uint8_t v___x_2160_; 
v_a_2159_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2159_);
lean_dec_ref_known(v___x_2157_, 1);
v___x_2160_ = l_Lean_Exception_isInterrupt(v_a_2159_);
if (v___x_2160_ == 0)
{
uint8_t v___x_2161_; 
lean_inc(v_a_2159_);
v___x_2161_ = l_Lean_Exception_isRuntime(v_a_2159_);
v___y_2096_ = v_a_2109_;
v___y_2097_ = v___x_2139_;
v___y_2098_ = v_a_2159_;
v___y_2099_ = v_a_2156_;
v___y_2100_ = v___x_2161_;
goto v___jp_2095_;
}
else
{
v___y_2096_ = v_a_2109_;
v___y_2097_ = v___x_2139_;
v___y_2098_ = v_a_2159_;
v___y_2099_ = v_a_2156_;
v___y_2100_ = v___x_2160_;
goto v___jp_2095_;
}
}
}
else
{
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1929_);
lean_dec_ref(v_act_1928_);
v___y_2090_ = v_a_2109_;
v___y_2091_ = v___x_2139_;
v___y_2092_ = v___x_2155_;
goto v___jp_2089_;
}
}
else
{
lean_object* v_a_2162_; 
lean_dec(v_fst_2002_);
lean_dec_ref(v_allowFailure_1929_);
lean_dec_ref(v_act_1928_);
lean_dec_ref(v_cfg_1927_);
v_a_2162_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_a_2162_);
lean_dec_ref_known(v___x_2152_, 1);
v___y_2085_ = v_a_2109_;
v___y_2086_ = v___x_2139_;
v_a_2087_ = v_a_2162_;
goto v___jp_2084_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___boxed(lean_object* v_cfg_2225_, lean_object* v_act_2226_, lean_object* v_allowFailure_2227_, lean_object* v_cand_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(v_cfg_2225_, v_act_2226_, v_allowFailure_2227_, v_cand_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
lean_dec(v_a_2230_);
lean_dec_ref(v_a_2229_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(lean_object* v_00_u03b1_2235_, lean_object* v_x_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_x_2236_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2243_, lean_object* v_x_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3(v_00_u03b1_2243_, v_x_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(lean_object* v_act_2253_, lean_object* v_a_2254_, uint8_t v_collectAll_2255_, lean_object* v_as_2256_, size_t v_sz_2257_, size_t v_i_2258_, lean_object* v_b_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v_a_2266_; uint8_t v___x_2270_; 
v___x_2270_ = lean_usize_dec_lt(v_i_2258_, v_sz_2257_);
if (v___x_2270_ == 0)
{
lean_object* v___x_2271_; 
lean_dec_ref(v_act_2253_);
v___x_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2271_, 0, v_b_2259_);
return v___x_2271_;
}
else
{
lean_object* v_snd_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2345_; 
v_snd_2272_ = lean_ctor_get(v_b_2259_, 1);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_b_2259_);
if (v_isSharedCheck_2345_ == 0)
{
lean_object* v_unused_2346_; 
v_unused_2346_ = lean_ctor_get(v_b_2259_, 0);
lean_dec(v_unused_2346_);
v___x_2274_ = v_b_2259_;
v_isShared_2275_ = v_isSharedCheck_2345_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_snd_2272_);
lean_dec(v_b_2259_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2345_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2276_; lean_object* v_a_2277_; lean_object* v___x_2278_; 
v___x_2276_ = lean_box(0);
v_a_2277_ = lean_array_uget_borrowed(v_as_2256_, v_i_2258_);
lean_inc_ref(v_act_2253_);
lean_inc(v___y_2263_);
lean_inc_ref(v___y_2262_);
lean_inc(v___y_2261_);
lean_inc_ref(v___y_2260_);
lean_inc(v_a_2277_);
v___x_2278_ = lean_apply_6(v_act_2253_, v_a_2277_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, lean_box(0));
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2308_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2281_ = v___x_2278_;
v_isShared_2282_ = v_isSharedCheck_2308_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2278_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2308_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
uint8_t v___y_2301_; uint8_t v___x_2307_; 
v___x_2307_ = l_List_isEmpty___redArg(v_a_2279_);
if (v___x_2307_ == 0)
{
v___y_2301_ = v___x_2307_;
goto v___jp_2300_;
}
else
{
if (v_collectAll_2255_ == 0)
{
v___y_2301_ = v___x_2307_;
goto v___jp_2300_;
}
else
{
lean_del_object(v___x_2281_);
goto v___jp_2283_;
}
}
v___jp_2283_:
{
lean_object* v___x_2284_; lean_object* v_mctx_2285_; lean_object* v___x_2286_; 
v___x_2284_ = lean_st_ref_get(v___y_2261_);
v_mctx_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc_ref(v_mctx_2285_);
lean_dec(v___x_2284_);
v___x_2286_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2254_, v___y_2261_, v___y_2263_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v___x_2288_; 
lean_dec_ref_known(v___x_2286_, 1);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 1, v_mctx_2285_);
lean_ctor_set(v___x_2274_, 0, v_a_2279_);
v___x_2288_ = v___x_2274_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2279_);
lean_ctor_set(v_reuseFailAlloc_2291_, 1, v_mctx_2285_);
v___x_2288_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2289_ = lean_array_push(v_snd_2272_, v___x_2288_);
v___x_2290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2276_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
v_a_2266_ = v___x_2290_;
goto v___jp_2265_;
}
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_dec_ref(v_mctx_2285_);
lean_dec(v_a_2279_);
lean_del_object(v___x_2274_);
lean_dec(v_snd_2272_);
lean_dec_ref(v_act_2253_);
v_a_2292_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2286_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2286_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
v___jp_2300_:
{
if (v___y_2301_ == 0)
{
lean_del_object(v___x_2281_);
goto v___jp_2283_;
}
else
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2305_; 
lean_dec(v_a_2279_);
lean_del_object(v___x_2274_);
lean_dec_ref(v_act_2253_);
v___x_2302_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___closed__0));
v___x_2303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
lean_ctor_set(v___x_2303_, 1, v_snd_2272_);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 0, v___x_2303_);
v___x_2305_ = v___x_2281_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2303_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2344_; 
v_a_2309_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2311_ = v___x_2278_;
v_isShared_2312_ = v_isSharedCheck_2344_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2278_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2344_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
uint8_t v___y_2314_; uint8_t v___x_2342_; 
v___x_2342_ = l_Lean_Exception_isInterrupt(v_a_2309_);
if (v___x_2342_ == 0)
{
uint8_t v___x_2343_; 
lean_inc(v_a_2309_);
v___x_2343_ = l_Lean_Exception_isRuntime(v_a_2309_);
v___y_2314_ = v___x_2343_;
goto v___jp_2313_;
}
else
{
v___y_2314_ = v___x_2342_;
goto v___jp_2313_;
}
v___jp_2313_:
{
if (v___y_2314_ == 0)
{
lean_object* v___x_2315_; 
lean_del_object(v___x_2311_);
v___x_2315_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2254_, v___y_2261_, v___y_2263_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2329_; 
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2329_ == 0)
{
lean_object* v_unused_2330_; 
v_unused_2330_ = lean_ctor_get(v___x_2315_, 0);
lean_dec(v_unused_2330_);
v___x_2317_ = v___x_2315_;
v_isShared_2318_ = v_isSharedCheck_2329_;
goto v_resetjp_2316_;
}
else
{
lean_dec(v___x_2315_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2329_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
uint8_t v___x_2319_; 
v___x_2319_ = l_Lean_Meta_LibrarySearch_isAbortSpeculation(v_a_2309_);
lean_dec(v_a_2309_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2321_; 
lean_del_object(v___x_2317_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 0, v___x_2276_);
v___x_2321_ = v___x_2274_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2322_, 1, v_snd_2272_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
v_a_2266_ = v___x_2321_;
goto v___jp_2265_;
}
}
else
{
lean_object* v___x_2324_; 
lean_dec_ref(v_act_2253_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 0, v___x_2276_);
v___x_2324_ = v___x_2274_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2328_, 1, v_snd_2272_);
v___x_2324_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
lean_object* v___x_2326_; 
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 0, v___x_2324_);
v___x_2326_ = v___x_2317_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2324_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
}
else
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
lean_dec(v_a_2309_);
lean_del_object(v___x_2274_);
lean_dec(v_snd_2272_);
lean_dec_ref(v_act_2253_);
v_a_2331_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2333_ = v___x_2315_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2315_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
}
else
{
lean_object* v___x_2340_; 
lean_del_object(v___x_2274_);
lean_dec(v_snd_2272_);
lean_dec_ref(v_act_2253_);
if (v_isShared_2312_ == 0)
{
v___x_2340_ = v___x_2311_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2309_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
}
}
}
v___jp_2265_:
{
size_t v___x_2267_; size_t v___x_2268_; 
v___x_2267_ = ((size_t)1ULL);
v___x_2268_ = lean_usize_add(v_i_2258_, v___x_2267_);
v_i_2258_ = v___x_2268_;
v_b_2259_ = v_a_2266_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0___boxed(lean_object* v_act_2347_, lean_object* v_a_2348_, lean_object* v_collectAll_2349_, lean_object* v_as_2350_, lean_object* v_sz_2351_, lean_object* v_i_2352_, lean_object* v_b_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
uint8_t v_collectAll_boxed_2359_; size_t v_sz_boxed_2360_; size_t v_i_boxed_2361_; lean_object* v_res_2362_; 
v_collectAll_boxed_2359_ = lean_unbox(v_collectAll_2349_);
v_sz_boxed_2360_ = lean_unbox_usize(v_sz_2351_);
lean_dec(v_sz_2351_);
v_i_boxed_2361_ = lean_unbox_usize(v_i_2352_);
lean_dec(v_i_2352_);
v_res_2362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(v_act_2347_, v_a_2348_, v_collectAll_boxed_2359_, v_as_2350_, v_sz_boxed_2360_, v_i_boxed_2361_, v_b_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec_ref(v_as_2350_);
lean_dec_ref(v_a_2348_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryOnEach(lean_object* v_act_2368_, lean_object* v_candidates_2369_, uint8_t v_collectAll_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_){
_start:
{
lean_object* v___x_2376_; 
v___x_2376_ = l_Lean_Meta_saveState___redArg(v_a_2372_, v_a_2374_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; lean_object* v___x_2378_; size_t v_sz_2379_; size_t v___x_2380_; lean_object* v___x_2381_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_a_2377_);
lean_dec_ref_known(v___x_2376_, 1);
v___x_2378_ = ((lean_object*)(l_Lean_Meta_LibrarySearch_tryOnEach___closed__1));
v_sz_2379_ = lean_array_size(v_candidates_2369_);
v___x_2380_ = ((size_t)0ULL);
v___x_2381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_LibrarySearch_tryOnEach_spec__0(v_act_2368_, v_a_2377_, v_collectAll_2370_, v_candidates_2369_, v_sz_2379_, v___x_2380_, v___x_2378_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_);
lean_dec(v_a_2377_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2396_; 
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2384_ = v___x_2381_;
v_isShared_2385_ = v_isSharedCheck_2396_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2381_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2396_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v_fst_2386_; 
v_fst_2386_ = lean_ctor_get(v_a_2382_, 0);
if (lean_obj_tag(v_fst_2386_) == 0)
{
lean_object* v_snd_2387_; lean_object* v___x_2388_; lean_object* v___x_2390_; 
v_snd_2387_ = lean_ctor_get(v_a_2382_, 1);
lean_inc(v_snd_2387_);
lean_dec(v_a_2382_);
v___x_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2388_, 0, v_snd_2387_);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 0, v___x_2388_);
v___x_2390_ = v___x_2384_;
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
else
{
lean_object* v_val_2392_; lean_object* v___x_2394_; 
lean_inc_ref(v_fst_2386_);
lean_dec(v_a_2382_);
v_val_2392_ = lean_ctor_get(v_fst_2386_, 0);
lean_inc(v_val_2392_);
lean_dec_ref_known(v_fst_2386_, 1);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 0, v_val_2392_);
v___x_2394_ = v___x_2384_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_val_2392_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
v_a_2397_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2381_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2381_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
else
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2412_; 
lean_dec_ref(v_act_2368_);
v_a_2405_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2407_ = v___x_2376_;
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2376_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2410_; 
if (v_isShared_2408_ == 0)
{
v___x_2410_ = v___x_2407_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2405_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_tryOnEach___boxed(lean_object* v_act_2413_, lean_object* v_candidates_2414_, lean_object* v_collectAll_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_){
_start:
{
uint8_t v_collectAll_boxed_2421_; lean_object* v_res_2422_; 
v_collectAll_boxed_2421_ = lean_unbox(v_collectAll_2415_);
v_res_2422_ = l_Lean_Meta_LibrarySearch_tryOnEach(v_act_2413_, v_candidates_2414_, v_collectAll_boxed_2421_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_);
lean_dec(v_a_2419_);
lean_dec_ref(v_a_2418_);
lean_dec(v_a_2417_);
lean_dec_ref(v_a_2416_);
lean_dec_ref(v_candidates_2414_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg(){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = lean_obj_once(&l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0, &l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0_once, _init_l_Lean_Meta_LibrarySearch_abortSpeculation___redArg___closed__0);
v___x_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg___boxed(lean_object* v___y_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(lean_object* v_00_u03b1_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___boxed(lean_object* v_00_u03b1_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0(v_00_u03b1_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(lean_object* v_category_2442_, lean_object* v_opts_2443_, lean_object* v_act_2444_, lean_object* v_decl_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
lean_inc(v___y_2449_);
lean_inc_ref(v___y_2448_);
lean_inc(v___y_2447_);
lean_inc_ref(v___y_2446_);
v___x_2451_ = lean_apply_4(v_act_2444_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
v___x_2452_ = l_Lean_profileitIOUnsafe___redArg(v_category_2442_, v_opts_2443_, v___x_2451_, v_decl_2445_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg___boxed(lean_object* v_category_2453_, lean_object* v_opts_2454_, lean_object* v_act_2455_, lean_object* v_decl_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v_category_2453_, v_opts_2454_, v_act_2455_, v_decl_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec_ref(v_opts_2454_);
lean_dec_ref(v_category_2453_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(lean_object* v_00_u03b1_2463_, lean_object* v_category_2464_, lean_object* v_opts_2465_, lean_object* v_act_2466_, lean_object* v_decl_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v_category_2464_, v_opts_2465_, v_act_2466_, v_decl_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___boxed(lean_object* v_00_u03b1_2474_, lean_object* v_category_2475_, lean_object* v_opts_2476_, lean_object* v_act_2477_, lean_object* v_decl_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3(v_00_u03b1_2474_, v_category_2475_, v_opts_2476_, v_act_2477_, v_decl_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec_ref(v_opts_2476_);
lean_dec_ref(v_category_2475_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0(lean_object* v_a_2485_, lean_object* v___x_2486_, lean_object* v_tactic_2487_, lean_object* v_allowFailure_2488_, lean_object* v_cand_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v___x_2495_; 
lean_inc(v___y_2493_);
lean_inc_ref(v___y_2492_);
lean_inc(v___y_2491_);
lean_inc_ref(v___y_2490_);
v___x_2495_ = lean_apply_5(v_a_2485_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, lean_box(0));
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_a_2496_; uint8_t v___x_2497_; 
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_a_2496_);
lean_dec_ref_known(v___x_2495_, 1);
v___x_2497_ = lean_unbox(v_a_2496_);
lean_dec(v_a_2496_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2498_; 
v___x_2498_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma(v___x_2486_, v_tactic_2487_, v_allowFailure_2488_, v_cand_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
return v___x_2498_;
}
else
{
lean_object* v___x_2499_; lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_dec_ref(v_cand_2489_);
lean_dec_ref(v_allowFailure_2488_);
lean_dec_ref(v_tactic_2487_);
lean_dec_ref(v___x_2486_);
v___x_2499_ = l_Lean_Meta_LibrarySearch_abortSpeculation___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__0___redArg();
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2499_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2499_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_dec_ref(v_cand_2489_);
lean_dec_ref(v_allowFailure_2488_);
lean_dec_ref(v_tactic_2487_);
lean_dec_ref(v___x_2486_);
v_a_2508_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2495_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2495_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed(lean_object* v_a_2516_, lean_object* v___x_2517_, lean_object* v_tactic_2518_, lean_object* v_allowFailure_2519_, lean_object* v_cand_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0(v_a_2516_, v___x_2517_, v_tactic_2518_, v_allowFailure_2519_, v_cand_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
return v_res_2526_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(lean_object* v_as_2527_, size_t v_i_2528_, size_t v_stop_2529_){
_start:
{
uint8_t v___x_2530_; 
v___x_2530_ = lean_usize_dec_eq(v_i_2528_, v_stop_2529_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; lean_object* v_fst_2532_; uint8_t v___x_2533_; 
v___x_2531_ = lean_array_uget_borrowed(v_as_2527_, v_i_2528_);
v_fst_2532_ = lean_ctor_get(v___x_2531_, 0);
v___x_2533_ = l_List_isEmpty___redArg(v_fst_2532_);
if (v___x_2533_ == 0)
{
size_t v___x_2534_; size_t v___x_2535_; 
v___x_2534_ = ((size_t)1ULL);
v___x_2535_ = lean_usize_add(v_i_2528_, v___x_2534_);
v_i_2528_ = v___x_2535_;
goto _start;
}
else
{
return v___x_2533_;
}
}
else
{
uint8_t v___x_2537_; 
v___x_2537_ = 0;
return v___x_2537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2___boxed(lean_object* v_as_2538_, lean_object* v_i_2539_, lean_object* v_stop_2540_){
_start:
{
size_t v_i_boxed_2541_; size_t v_stop_boxed_2542_; uint8_t v_res_2543_; lean_object* v_r_2544_; 
v_i_boxed_2541_ = lean_unbox_usize(v_i_2539_);
lean_dec(v_i_2539_);
v_stop_boxed_2542_ = lean_unbox_usize(v_stop_2540_);
lean_dec(v_stop_2540_);
v_res_2543_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_as_2538_, v_i_boxed_2541_, v_stop_boxed_2542_);
lean_dec_ref(v_as_2538_);
v_r_2544_ = lean_box(v_res_2543_);
return v_r_2544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(lean_object* v_goal_2545_, lean_object* v___x_2546_, size_t v_sz_2547_, size_t v_i_2548_, lean_object* v_bs_2549_){
_start:
{
uint8_t v___x_2550_; 
v___x_2550_ = lean_usize_dec_lt(v_i_2548_, v_sz_2547_);
if (v___x_2550_ == 0)
{
lean_dec_ref(v___x_2546_);
lean_dec(v_goal_2545_);
return v_bs_2549_;
}
else
{
lean_object* v_v_2551_; lean_object* v___x_2552_; lean_object* v_bs_x27_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; size_t v___x_2556_; size_t v___x_2557_; lean_object* v___x_2558_; 
v_v_2551_ = lean_array_uget(v_bs_2549_, v_i_2548_);
v___x_2552_ = lean_unsigned_to_nat(0u);
v_bs_x27_2553_ = lean_array_uset(v_bs_2549_, v_i_2548_, v___x_2552_);
lean_inc_ref(v___x_2546_);
lean_inc(v_goal_2545_);
v___x_2554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2554_, 0, v_goal_2545_);
lean_ctor_set(v___x_2554_, 1, v___x_2546_);
v___x_2555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
lean_ctor_set(v___x_2555_, 1, v_v_2551_);
v___x_2556_ = ((size_t)1ULL);
v___x_2557_ = lean_usize_add(v_i_2548_, v___x_2556_);
v___x_2558_ = lean_array_uset(v_bs_x27_2553_, v_i_2548_, v___x_2555_);
v_i_2548_ = v___x_2557_;
v_bs_2549_ = v___x_2558_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1___boxed(lean_object* v_goal_2560_, lean_object* v___x_2561_, lean_object* v_sz_2562_, lean_object* v_i_2563_, lean_object* v_bs_2564_){
_start:
{
size_t v_sz_boxed_2565_; size_t v_i_boxed_2566_; lean_object* v_res_2567_; 
v_sz_boxed_2565_ = lean_unbox_usize(v_sz_2562_);
lean_dec(v_sz_2562_);
v_i_boxed_2566_ = lean_unbox_usize(v_i_2563_);
lean_dec(v_i_2563_);
v_res_2567_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2560_, v___x_2561_, v_sz_boxed_2565_, v_i_boxed_2566_, v_bs_2564_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(lean_object* v_leavePercentHeartbeats_2569_, lean_object* v___x_2570_, lean_object* v_tactic_2571_, lean_object* v_allowFailure_2572_, lean_object* v_goal_2573_, uint8_t v_collectAll_2574_, uint8_t v_includeStar_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v___x_2584_; 
v___x_2584_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2569_, v___y_2578_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; lean_object* v___f_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_a_2585_);
lean_dec_ref_known(v___x_2584_, 1);
v___f_2586_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2586_, 0, v_a_2585_);
lean_closure_set(v___f_2586_, 1, v___x_2570_);
lean_closure_set(v___f_2586_, 2, v_tactic_2571_);
lean_closure_set(v___f_2586_, 3, v_allowFailure_2572_);
v___x_2587_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0));
lean_inc(v_goal_2573_);
v___x_2588_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2587_, v_goal_2573_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2590_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref_known(v___x_2588_, 1);
lean_inc_ref(v___f_2586_);
v___x_2590_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2586_, v_a_2589_, v_collectAll_2574_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
lean_dec(v_a_2589_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_a_2591_);
if (lean_obj_tag(v_a_2591_) == 0)
{
lean_dec_ref_known(v___x_2590_, 1);
lean_dec_ref(v___f_2586_);
lean_dec(v_goal_2573_);
goto v___jp_2581_;
}
else
{
lean_object* v_val_2592_; lean_object* v___x_2641_; lean_object* v___x_2642_; uint8_t v___x_2643_; 
v_val_2592_ = lean_ctor_get(v_a_2591_, 0);
v___x_2641_ = lean_unsigned_to_nat(0u);
v___x_2642_ = lean_array_get_size(v_val_2592_);
v___x_2643_ = lean_nat_dec_lt(v___x_2641_, v___x_2642_);
if (v___x_2643_ == 0)
{
goto v___jp_2637_;
}
else
{
if (v___x_2643_ == 0)
{
goto v___jp_2637_;
}
else
{
size_t v___x_2644_; size_t v___x_2645_; uint8_t v___x_2646_; 
v___x_2644_ = ((size_t)0ULL);
v___x_2645_ = lean_usize_of_nat(v___x_2642_);
v___x_2646_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_val_2592_, v___x_2644_, v___x_2645_);
if (v___x_2646_ == 0)
{
goto v___jp_2637_;
}
else
{
lean_dec_ref_known(v_a_2591_, 1);
lean_dec_ref(v___f_2586_);
lean_dec(v_goal_2573_);
return v___x_2590_;
}
}
}
v___jp_2593_:
{
if (v_includeStar_2575_ == 0)
{
lean_dec_ref_known(v_a_2591_, 1);
lean_dec_ref(v___f_2586_);
lean_dec(v_goal_2573_);
return v___x_2590_;
}
else
{
lean_object* v___x_2594_; 
lean_dec_ref_known(v___x_2590_, 1);
v___x_2594_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2628_; 
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2597_ = v___x_2594_;
v_isShared_2598_ = v_isSharedCheck_2628_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2594_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2628_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; uint8_t v___x_2601_; 
v___x_2599_ = lean_array_get_size(v_a_2595_);
v___x_2600_ = lean_unsigned_to_nat(0u);
v___x_2601_ = lean_nat_dec_eq(v___x_2599_, v___x_2600_);
if (v___x_2601_ == 0)
{
lean_object* v___x_2602_; lean_object* v_mctx_2603_; size_t v_sz_2604_; size_t v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
lean_inc(v_val_2592_);
lean_del_object(v___x_2597_);
lean_dec_ref_known(v_a_2591_, 1);
v___x_2602_ = lean_st_ref_get(v___y_2577_);
v_mctx_2603_ = lean_ctor_get(v___x_2602_, 0);
lean_inc_ref(v_mctx_2603_);
lean_dec(v___x_2602_);
v_sz_2604_ = lean_array_size(v_a_2595_);
v___x_2605_ = ((size_t)0ULL);
v___x_2606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2573_, v_mctx_2603_, v_sz_2604_, v___x_2605_, v_a_2595_);
v___x_2607_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2586_, v___x_2606_, v_collectAll_2574_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
lean_dec_ref(v___x_2606_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2624_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2610_ = v___x_2607_;
v_isShared_2611_ = v_isSharedCheck_2624_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2607_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2624_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
if (lean_obj_tag(v_a_2608_) == 0)
{
lean_del_object(v___x_2610_);
lean_dec(v_val_2592_);
goto v___jp_2581_;
}
else
{
lean_object* v_val_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2623_; 
v_val_2612_ = lean_ctor_get(v_a_2608_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v_a_2608_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2614_ = v_a_2608_;
v_isShared_2615_ = v_isSharedCheck_2623_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_val_2612_);
lean_dec(v_a_2608_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2623_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2616_; lean_object* v___x_2618_; 
v___x_2616_ = l_Array_append___redArg(v_val_2592_, v_val_2612_);
lean_dec(v_val_2612_);
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 0, v___x_2616_);
v___x_2618_ = v___x_2614_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v___x_2616_);
v___x_2618_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
lean_object* v___x_2620_; 
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 0, v___x_2618_);
v___x_2620_ = v___x_2610_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v___x_2618_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2592_);
return v___x_2607_;
}
}
else
{
lean_object* v___x_2626_; 
lean_dec(v_a_2595_);
lean_dec_ref(v___f_2586_);
lean_dec(v_goal_2573_);
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 0, v_a_2591_);
v___x_2626_ = v___x_2597_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2591_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_dec_ref_known(v_a_2591_, 1);
lean_dec_ref(v___f_2586_);
lean_dec(v_goal_2573_);
v_a_2629_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2594_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2594_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
}
v___jp_2637_:
{
if (v_collectAll_2574_ == 0)
{
lean_object* v___x_2638_; lean_object* v___x_2639_; uint8_t v___x_2640_; 
v___x_2638_ = lean_array_get_size(v_val_2592_);
v___x_2639_ = lean_unsigned_to_nat(0u);
v___x_2640_ = lean_nat_dec_eq(v___x_2638_, v___x_2639_);
if (v___x_2640_ == 0)
{
lean_dec_ref_known(v_a_2591_, 1);
lean_dec_ref(v___f_2586_);
lean_dec(v_goal_2573_);
return v___x_2590_;
}
else
{
goto v___jp_2593_;
}
}
else
{
goto v___jp_2593_;
}
}
}
}
else
{
lean_dec_ref(v___f_2586_);
lean_dec(v_goal_2573_);
return v___x_2590_;
}
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
lean_dec_ref(v___f_2586_);
lean_dec(v_goal_2573_);
v_a_2647_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2649_ = v___x_2588_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2588_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2647_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
else
{
lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2662_; 
lean_dec(v_goal_2573_);
lean_dec_ref(v_allowFailure_2572_);
lean_dec_ref(v_tactic_2571_);
lean_dec_ref(v___x_2570_);
v_a_2655_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2657_ = v___x_2584_;
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2655_);
lean_dec(v___x_2584_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2662_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2660_; 
if (v_isShared_2658_ == 0)
{
v___x_2660_ = v___x_2657_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2655_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
v___jp_2581_:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2582_ = lean_box(0);
v___x_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2582_);
return v___x_2583_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed(lean_object* v_leavePercentHeartbeats_2663_, lean_object* v___x_2664_, lean_object* v_tactic_2665_, lean_object* v_allowFailure_2666_, lean_object* v_goal_2667_, lean_object* v_collectAll_2668_, lean_object* v_includeStar_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
uint8_t v_collectAll_boxed_2675_; uint8_t v_includeStar_boxed_2676_; lean_object* v_res_2677_; 
v_collectAll_boxed_2675_ = lean_unbox(v_collectAll_2668_);
v_includeStar_boxed_2676_ = lean_unbox(v_includeStar_2669_);
v_res_2677_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1(v_leavePercentHeartbeats_2663_, v___x_2664_, v_tactic_2665_, v_allowFailure_2666_, v_goal_2667_, v_collectAll_boxed_2675_, v_includeStar_boxed_2676_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
lean_dec(v_leavePercentHeartbeats_2663_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2(lean_object* v_goal_2678_, lean_object* v_x_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
lean_object* v___x_2685_; 
v___x_2685_ = l_Lean_MVarId_getType(v_goal_2678_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2694_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2688_ = v___x_2685_;
v_isShared_2689_ = v_isSharedCheck_2694_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2685_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2694_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2690_; lean_object* v___x_2692_; 
v___x_2690_ = l_Lean_MessageData_ofExpr(v_a_2686_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2690_);
v___x_2692_ = v___x_2688_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2690_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
v_a_2695_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2685_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2685_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___boxed(lean_object* v_goal_2703_, lean_object* v_x_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2(v_goal_2703_, v_x_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec_ref(v_x_2704_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__6(lean_object* v_leavePercentHeartbeats_2711_, lean_object* v___x_2712_, lean_object* v_tactic_2713_, lean_object* v_allowFailure_2714_, lean_object* v_goal_2715_, uint8_t v_collectAll_2716_, uint8_t v_includeStar_2717_, uint8_t v___x_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = l_Lean_Meta_LibrarySearch_mkHeartbeatCheck___redArg(v_leavePercentHeartbeats_2711_, v___y_2721_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_object* v_a_2728_; lean_object* v___f_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
lean_inc(v_a_2728_);
lean_dec_ref_known(v___x_2727_, 1);
v___f_2729_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2729_, 0, v_a_2728_);
lean_closure_set(v___f_2729_, 1, v___x_2712_);
lean_closure_set(v___f_2729_, 2, v_tactic_2713_);
lean_closure_set(v___f_2729_, 3, v_allowFailure_2714_);
v___x_2730_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___closed__0));
lean_inc(v_goal_2715_);
v___x_2731_ = l_Lean_Meta_LibrarySearch_librarySearchSymm(v___x_2730_, v_goal_2715_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; lean_object* v___x_2733_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2732_);
lean_dec_ref_known(v___x_2731_, 1);
lean_inc_ref(v___f_2729_);
v___x_2733_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2729_, v_a_2732_, v_collectAll_2716_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
lean_dec(v_a_2732_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v_a_2734_; 
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
lean_inc(v_a_2734_);
if (lean_obj_tag(v_a_2734_) == 0)
{
lean_dec_ref_known(v___x_2733_, 1);
lean_dec_ref(v___f_2729_);
lean_dec(v_goal_2715_);
goto v___jp_2724_;
}
else
{
lean_object* v_val_2735_; lean_object* v___x_2785_; lean_object* v___x_2786_; uint8_t v___x_2787_; 
v_val_2735_ = lean_ctor_get(v_a_2734_, 0);
v___x_2785_ = lean_unsigned_to_nat(0u);
v___x_2786_ = lean_array_get_size(v_val_2735_);
v___x_2787_ = lean_nat_dec_lt(v___x_2785_, v___x_2786_);
if (v___x_2787_ == 0)
{
goto v___jp_2781_;
}
else
{
if (v___x_2787_ == 0)
{
goto v___jp_2781_;
}
else
{
size_t v___x_2788_; size_t v___x_2789_; uint8_t v___x_2790_; 
v___x_2788_ = ((size_t)0ULL);
v___x_2789_ = lean_usize_of_nat(v___x_2786_);
v___x_2790_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__2(v_val_2735_, v___x_2788_, v___x_2789_);
if (v___x_2790_ == 0)
{
goto v___jp_2781_;
}
else
{
if (v___x_2718_ == 0)
{
goto v___jp_2780_;
}
else
{
lean_dec_ref_known(v_a_2734_, 1);
lean_dec_ref(v___f_2729_);
lean_dec(v_goal_2715_);
return v___x_2733_;
}
}
}
}
v___jp_2736_:
{
lean_object* v___x_2737_; 
v___x_2737_ = l_Lean_Meta_LibrarySearch_getStarLemmas(v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2771_; 
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2740_ = v___x_2737_;
v_isShared_2741_ = v_isSharedCheck_2771_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2737_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2771_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; uint8_t v___x_2744_; 
v___x_2742_ = lean_array_get_size(v_a_2738_);
v___x_2743_ = lean_unsigned_to_nat(0u);
v___x_2744_ = lean_nat_dec_eq(v___x_2742_, v___x_2743_);
if (v___x_2744_ == 0)
{
lean_object* v___x_2745_; lean_object* v_mctx_2746_; size_t v_sz_2747_; size_t v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
lean_inc(v_val_2735_);
lean_del_object(v___x_2740_);
lean_dec_ref_known(v_a_2734_, 1);
v___x_2745_ = lean_st_ref_get(v___y_2720_);
v_mctx_2746_ = lean_ctor_get(v___x_2745_, 0);
lean_inc_ref(v_mctx_2746_);
lean_dec(v___x_2745_);
v_sz_2747_ = lean_array_size(v_a_2738_);
v___x_2748_ = ((size_t)0ULL);
v___x_2749_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__1(v_goal_2715_, v_mctx_2746_, v_sz_2747_, v___x_2748_, v_a_2738_);
v___x_2750_ = l_Lean_Meta_LibrarySearch_tryOnEach(v___f_2729_, v___x_2749_, v_collectAll_2716_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
lean_dec_ref(v___x_2749_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2767_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2753_ = v___x_2750_;
v_isShared_2754_ = v_isSharedCheck_2767_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2750_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2767_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
if (lean_obj_tag(v_a_2751_) == 0)
{
lean_del_object(v___x_2753_);
lean_dec(v_val_2735_);
goto v___jp_2724_;
}
else
{
lean_object* v_val_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2766_; 
v_val_2755_ = lean_ctor_get(v_a_2751_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v_a_2751_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2757_ = v_a_2751_;
v_isShared_2758_ = v_isSharedCheck_2766_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_val_2755_);
lean_dec(v_a_2751_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2766_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2759_; lean_object* v___x_2761_; 
v___x_2759_ = l_Array_append___redArg(v_val_2735_, v_val_2755_);
lean_dec(v_val_2755_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 0, v___x_2759_);
v___x_2761_ = v___x_2757_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2759_);
v___x_2761_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
lean_object* v___x_2763_; 
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 0, v___x_2761_);
v___x_2763_ = v___x_2753_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2761_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2735_);
return v___x_2750_;
}
}
else
{
lean_object* v___x_2769_; 
lean_dec(v_a_2738_);
lean_dec_ref(v___f_2729_);
lean_dec(v_goal_2715_);
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 0, v_a_2734_);
v___x_2769_ = v___x_2740_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2734_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
else
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
lean_dec_ref_known(v_a_2734_, 1);
lean_dec_ref(v___f_2729_);
lean_dec(v_goal_2715_);
v_a_2772_ = lean_ctor_get(v___x_2737_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2737_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2737_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
v___jp_2780_:
{
if (v_includeStar_2717_ == 0)
{
if (v___x_2718_ == 0)
{
lean_dec_ref_known(v___x_2733_, 1);
goto v___jp_2736_;
}
else
{
lean_dec_ref_known(v_a_2734_, 1);
lean_dec_ref(v___f_2729_);
lean_dec(v_goal_2715_);
return v___x_2733_;
}
}
else
{
lean_dec_ref_known(v___x_2733_, 1);
goto v___jp_2736_;
}
}
v___jp_2781_:
{
if (v_collectAll_2716_ == 0)
{
if (v___x_2718_ == 0)
{
goto v___jp_2780_;
}
else
{
lean_object* v___x_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; 
v___x_2782_ = lean_array_get_size(v_val_2735_);
v___x_2783_ = lean_unsigned_to_nat(0u);
v___x_2784_ = lean_nat_dec_eq(v___x_2782_, v___x_2783_);
if (v___x_2784_ == 0)
{
lean_dec_ref_known(v_a_2734_, 1);
lean_dec_ref(v___f_2729_);
lean_dec(v_goal_2715_);
return v___x_2733_;
}
else
{
goto v___jp_2780_;
}
}
}
else
{
goto v___jp_2780_;
}
}
}
}
else
{
lean_dec_ref(v___f_2729_);
lean_dec(v_goal_2715_);
return v___x_2733_;
}
}
else
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
lean_dec_ref(v___f_2729_);
lean_dec(v_goal_2715_);
v_a_2791_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___x_2731_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2731_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
else
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
lean_dec(v_goal_2715_);
lean_dec_ref(v_allowFailure_2714_);
lean_dec_ref(v_tactic_2713_);
lean_dec_ref(v___x_2712_);
v_a_2799_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2727_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2727_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
v___jp_2724_:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2725_ = lean_box(0);
v___x_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2725_);
return v___x_2726_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__6___boxed(lean_object* v_leavePercentHeartbeats_2807_, lean_object* v___x_2808_, lean_object* v_tactic_2809_, lean_object* v_allowFailure_2810_, lean_object* v_goal_2811_, lean_object* v_collectAll_2812_, lean_object* v_includeStar_2813_, lean_object* v___x_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
uint8_t v_collectAll_boxed_2820_; uint8_t v_includeStar_boxed_2821_; uint8_t v___x_13998__boxed_2822_; lean_object* v_res_2823_; 
v_collectAll_boxed_2820_ = lean_unbox(v_collectAll_2812_);
v_includeStar_boxed_2821_ = lean_unbox(v_includeStar_2813_);
v___x_13998__boxed_2822_ = lean_unbox(v___x_2814_);
v_res_2823_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__6(v_leavePercentHeartbeats_2807_, v___x_2808_, v_tactic_2809_, v_allowFailure_2810_, v_goal_2811_, v_collectAll_boxed_2820_, v_includeStar_boxed_2821_, v___x_13998__boxed_2822_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v_leavePercentHeartbeats_2807_);
return v_res_2823_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(lean_object* v_e_2824_){
_start:
{
if (lean_obj_tag(v_e_2824_) == 0)
{
uint8_t v___x_2825_; 
v___x_2825_ = 2;
return v___x_2825_;
}
else
{
lean_object* v_a_2826_; 
v_a_2826_ = lean_ctor_get(v_e_2824_, 0);
if (lean_obj_tag(v_a_2826_) == 0)
{
uint8_t v___x_2827_; 
v___x_2827_ = 1;
return v___x_2827_;
}
else
{
uint8_t v___x_2828_; 
v___x_2828_ = 0;
return v___x_2828_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4___boxed(lean_object* v_e_2829_){
_start:
{
uint8_t v_res_2830_; lean_object* v_r_2831_; 
v_res_2830_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(v_e_2829_);
lean_dec_ref(v_e_2829_);
v_r_2831_ = lean_box(v_res_2830_);
return v_r_2831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(lean_object* v_cls_2832_, uint8_t v_collapsed_2833_, lean_object* v_tag_2834_, lean_object* v_opts_2835_, uint8_t v_clsEnabled_2836_, lean_object* v_oldTraces_2837_, lean_object* v_msg_2838_, lean_object* v_resStartStop_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v_fst_2845_; lean_object* v_snd_2846_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v_data_2850_; lean_object* v_fst_2861_; lean_object* v_snd_2862_; lean_object* v___x_2863_; uint8_t v___x_2864_; lean_object* v___y_2866_; lean_object* v_a_2867_; uint8_t v___y_2882_; double v___y_2914_; 
v_fst_2845_ = lean_ctor_get(v_resStartStop_2839_, 0);
lean_inc(v_fst_2845_);
v_snd_2846_ = lean_ctor_get(v_resStartStop_2839_, 1);
lean_inc(v_snd_2846_);
lean_dec_ref(v_resStartStop_2839_);
v_fst_2861_ = lean_ctor_get(v_snd_2846_, 0);
lean_inc(v_fst_2861_);
v_snd_2862_ = lean_ctor_get(v_snd_2846_, 1);
lean_inc(v_snd_2862_);
lean_dec(v_snd_2846_);
v___x_2863_ = l_Lean_trace_profiler;
v___x_2864_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_2835_, v___x_2863_);
if (v___x_2864_ == 0)
{
v___y_2882_ = v___x_2864_;
goto v___jp_2881_;
}
else
{
lean_object* v___x_2919_; uint8_t v___x_2920_; 
v___x_2919_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2920_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_opts_2835_, v___x_2919_);
if (v___x_2920_ == 0)
{
lean_object* v___x_2921_; lean_object* v___x_2922_; double v___x_2923_; double v___x_2924_; double v___x_2925_; 
v___x_2921_ = l_Lean_trace_profiler_threshold;
v___x_2922_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_2835_, v___x_2921_);
v___x_2923_ = lean_float_of_nat(v___x_2922_);
v___x_2924_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__3);
v___x_2925_ = lean_float_div(v___x_2923_, v___x_2924_);
v___y_2914_ = v___x_2925_;
goto v___jp_2913_;
}
else
{
lean_object* v___x_2926_; lean_object* v___x_2927_; double v___x_2928_; 
v___x_2926_ = l_Lean_trace_profiler_threshold;
v___x_2927_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__5(v_opts_2835_, v___x_2926_);
v___x_2928_ = lean_float_of_nat(v___x_2927_);
v___y_2914_ = v___x_2928_;
goto v___jp_2913_;
}
}
v___jp_2847_:
{
lean_object* v___x_2851_; 
lean_inc(v___y_2848_);
v___x_2851_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__2(v_oldTraces_2837_, v_data_2850_, v___y_2848_, v___y_2849_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v___x_2852_; 
lean_dec_ref_known(v___x_2851_, 1);
v___x_2852_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_2845_);
return v___x_2852_;
}
else
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
lean_dec(v_fst_2845_);
v_a_2853_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2855_ = v___x_2851_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2851_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2853_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
}
v___jp_2865_:
{
uint8_t v_result_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; double v___x_2871_; lean_object* v_data_2872_; 
v_result_2868_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4_spec__4(v_fst_2845_);
v___x_2869_ = lean_box(v_result_2868_);
v___x_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2869_);
v___x_2871_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__0);
lean_inc_ref(v_tag_2834_);
lean_inc_ref(v___x_2870_);
lean_inc(v_cls_2832_);
v_data_2872_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2872_, 0, v_cls_2832_);
lean_ctor_set(v_data_2872_, 1, v___x_2870_);
lean_ctor_set(v_data_2872_, 2, v_tag_2834_);
lean_ctor_set_float(v_data_2872_, sizeof(void*)*3, v___x_2871_);
lean_ctor_set_float(v_data_2872_, sizeof(void*)*3 + 8, v___x_2871_);
lean_ctor_set_uint8(v_data_2872_, sizeof(void*)*3 + 16, v_collapsed_2833_);
if (v___x_2864_ == 0)
{
lean_dec_ref_known(v___x_2870_, 1);
lean_dec(v_snd_2862_);
lean_dec(v_fst_2861_);
lean_dec_ref(v_tag_2834_);
lean_dec(v_cls_2832_);
v___y_2848_ = v___y_2866_;
v___y_2849_ = v_a_2867_;
v_data_2850_ = v_data_2872_;
goto v___jp_2847_;
}
else
{
lean_object* v_data_2873_; double v___x_2874_; double v___x_2875_; 
lean_dec_ref_known(v_data_2872_, 3);
v_data_2873_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2873_, 0, v_cls_2832_);
lean_ctor_set(v_data_2873_, 1, v___x_2870_);
lean_ctor_set(v_data_2873_, 2, v_tag_2834_);
v___x_2874_ = lean_unbox_float(v_fst_2861_);
lean_dec(v_fst_2861_);
lean_ctor_set_float(v_data_2873_, sizeof(void*)*3, v___x_2874_);
v___x_2875_ = lean_unbox_float(v_snd_2862_);
lean_dec(v_snd_2862_);
lean_ctor_set_float(v_data_2873_, sizeof(void*)*3 + 8, v___x_2875_);
lean_ctor_set_uint8(v_data_2873_, sizeof(void*)*3 + 16, v_collapsed_2833_);
v___y_2848_ = v___y_2866_;
v___y_2849_ = v_a_2867_;
v_data_2850_ = v_data_2873_;
goto v___jp_2847_;
}
}
v___jp_2876_:
{
lean_object* v_ref_2877_; lean_object* v___x_2878_; 
v_ref_2877_ = lean_ctor_get(v___y_2842_, 2);
lean_inc(v___y_2843_);
lean_inc_ref(v___y_2842_);
lean_inc(v___y_2841_);
lean_inc_ref(v___y_2840_);
lean_inc(v_fst_2845_);
v___x_2878_ = lean_apply_6(v_msg_2838_, v_fst_2845_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, lean_box(0));
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_a_2879_);
lean_dec_ref_known(v___x_2878_, 1);
v___y_2866_ = v_ref_2877_;
v_a_2867_ = v_a_2879_;
goto v___jp_2865_;
}
else
{
lean_object* v___x_2880_; 
lean_dec_ref_known(v___x_2878_, 1);
v___x_2880_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2___closed__2);
v___y_2866_ = v_ref_2877_;
v_a_2867_ = v___x_2880_;
goto v___jp_2865_;
}
}
v___jp_2881_:
{
if (v_clsEnabled_2836_ == 0)
{
if (v___y_2882_ == 0)
{
lean_object* v___x_2883_; lean_object* v_traceState_2884_; lean_object* v_env_2885_; lean_object* v_nextMacroScope_2886_; lean_object* v_ngen_2887_; lean_object* v_auxDeclNGen_2888_; lean_object* v_cache_2889_; lean_object* v_recordedDeps_2890_; lean_object* v_messages_2891_; lean_object* v_infoState_2892_; lean_object* v_snapshotTasks_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2912_; 
lean_dec(v_snd_2862_);
lean_dec(v_fst_2861_);
lean_dec_ref(v_msg_2838_);
lean_dec_ref(v_tag_2834_);
lean_dec(v_cls_2832_);
v___x_2883_ = lean_st_ref_take(v___y_2843_);
v_traceState_2884_ = lean_ctor_get(v___x_2883_, 4);
v_env_2885_ = lean_ctor_get(v___x_2883_, 0);
v_nextMacroScope_2886_ = lean_ctor_get(v___x_2883_, 1);
v_ngen_2887_ = lean_ctor_get(v___x_2883_, 2);
v_auxDeclNGen_2888_ = lean_ctor_get(v___x_2883_, 3);
v_cache_2889_ = lean_ctor_get(v___x_2883_, 5);
v_recordedDeps_2890_ = lean_ctor_get(v___x_2883_, 6);
v_messages_2891_ = lean_ctor_get(v___x_2883_, 7);
v_infoState_2892_ = lean_ctor_get(v___x_2883_, 8);
v_snapshotTasks_2893_ = lean_ctor_get(v___x_2883_, 9);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2895_ = v___x_2883_;
v_isShared_2896_ = v_isSharedCheck_2912_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_snapshotTasks_2893_);
lean_inc(v_infoState_2892_);
lean_inc(v_messages_2891_);
lean_inc(v_recordedDeps_2890_);
lean_inc(v_cache_2889_);
lean_inc(v_traceState_2884_);
lean_inc(v_auxDeclNGen_2888_);
lean_inc(v_ngen_2887_);
lean_inc(v_nextMacroScope_2886_);
lean_inc(v_env_2885_);
lean_dec(v___x_2883_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2912_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
uint64_t v_tid_2897_; lean_object* v_traces_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2911_; 
v_tid_2897_ = lean_ctor_get_uint64(v_traceState_2884_, sizeof(void*)*1);
v_traces_2898_ = lean_ctor_get(v_traceState_2884_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v_traceState_2884_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2900_ = v_traceState_2884_;
v_isShared_2901_ = v_isSharedCheck_2911_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_traces_2898_);
lean_dec(v_traceState_2884_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2911_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2902_; lean_object* v___x_2904_; 
v___x_2902_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2837_, v_traces_2898_);
lean_dec_ref(v_traces_2898_);
if (v_isShared_2901_ == 0)
{
lean_ctor_set(v___x_2900_, 0, v___x_2902_);
v___x_2904_ = v___x_2900_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2902_);
lean_ctor_set_uint64(v_reuseFailAlloc_2910_, sizeof(void*)*1, v_tid_2897_);
v___x_2904_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
lean_object* v___x_2906_; 
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 4, v___x_2904_);
v___x_2906_ = v___x_2895_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_env_2885_);
lean_ctor_set(v_reuseFailAlloc_2909_, 1, v_nextMacroScope_2886_);
lean_ctor_set(v_reuseFailAlloc_2909_, 2, v_ngen_2887_);
lean_ctor_set(v_reuseFailAlloc_2909_, 3, v_auxDeclNGen_2888_);
lean_ctor_set(v_reuseFailAlloc_2909_, 4, v___x_2904_);
lean_ctor_set(v_reuseFailAlloc_2909_, 5, v_cache_2889_);
lean_ctor_set(v_reuseFailAlloc_2909_, 6, v_recordedDeps_2890_);
lean_ctor_set(v_reuseFailAlloc_2909_, 7, v_messages_2891_);
lean_ctor_set(v_reuseFailAlloc_2909_, 8, v_infoState_2892_);
lean_ctor_set(v_reuseFailAlloc_2909_, 9, v_snapshotTasks_2893_);
v___x_2906_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2907_ = lean_st_ref_put(v___y_2843_, v___x_2906_);
v___x_2908_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__2_spec__3___redArg(v_fst_2845_);
return v___x_2908_;
}
}
}
}
}
else
{
goto v___jp_2876_;
}
}
else
{
goto v___jp_2876_;
}
}
v___jp_2913_:
{
double v___x_2915_; double v___x_2916_; double v___x_2917_; uint8_t v___x_2918_; 
v___x_2915_ = lean_unbox_float(v_snd_2862_);
v___x_2916_ = lean_unbox_float(v_fst_2861_);
v___x_2917_ = lean_float_sub(v___x_2915_, v___x_2916_);
v___x_2918_ = lean_float_decLt(v___y_2914_, v___x_2917_);
v___y_2882_ = v___x_2918_;
goto v___jp_2881_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4___boxed(lean_object* v_cls_2929_, lean_object* v_collapsed_2930_, lean_object* v_tag_2931_, lean_object* v_opts_2932_, lean_object* v_clsEnabled_2933_, lean_object* v_oldTraces_2934_, lean_object* v_msg_2935_, lean_object* v_resStartStop_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
uint8_t v_collapsed_boxed_2942_; uint8_t v_clsEnabled_boxed_2943_; lean_object* v_res_2944_; 
v_collapsed_boxed_2942_ = lean_unbox(v_collapsed_2930_);
v_clsEnabled_boxed_2943_ = lean_unbox(v_clsEnabled_2933_);
v_res_2944_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v_cls_2929_, v_collapsed_boxed_2942_, v_tag_2931_, v_opts_2932_, v_clsEnabled_boxed_2943_, v_oldTraces_2934_, v_msg_2935_, v_resStartStop_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec_ref(v_opts_2932_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(lean_object* v_goal_2948_, lean_object* v_tactic_2949_, lean_object* v_allowFailure_2950_, lean_object* v_leavePercentHeartbeats_2951_, uint8_t v_includeStar_2952_, uint8_t v_collectAll_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_){
_start:
{
lean_object* v_toCold_2959_; lean_object* v_options_2960_; lean_object* v_inheritedTraceOptions_2961_; uint8_t v_hasTrace_2962_; lean_object* v___x_2963_; 
v_toCold_2959_ = lean_ctor_get(v_a_2956_, 0);
v_options_2960_ = lean_ctor_get(v_toCold_2959_, 2);
v_inheritedTraceOptions_2961_ = lean_ctor_get(v_toCold_2959_, 11);
v_hasTrace_2962_ = lean_ctor_get_uint8(v_options_2960_, sizeof(void*)*1);
v___x_2963_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__1_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
if (v_hasTrace_2962_ == 0)
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___f_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2964_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2956_);
v___x_2965_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___closed__0));
v___x_2966_ = lean_box(v_collectAll_2953_);
v___x_2967_ = lean_box(v_includeStar_2952_);
v___f_2968_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed), 12, 7);
lean_closure_set(v___f_2968_, 0, v_leavePercentHeartbeats_2951_);
lean_closure_set(v___f_2968_, 1, v___x_2965_);
lean_closure_set(v___f_2968_, 2, v_tactic_2949_);
lean_closure_set(v___f_2968_, 3, v_allowFailure_2950_);
lean_closure_set(v___f_2968_, 4, v_goal_2948_);
lean_closure_set(v___f_2968_, 5, v___x_2966_);
lean_closure_set(v___f_2968_, 6, v___x_2967_);
v___x_2969_ = lean_box(0);
v___x_2970_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_2963_, v___x_2964_, v___f_2968_, v___x_2969_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_);
lean_dec_ref(v___x_2964_);
return v___x_2970_;
}
else
{
lean_object* v___f_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; uint8_t v___x_2975_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v_a_2979_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v_a_2994_; 
lean_inc(v_goal_2948_);
v___f_2971_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2971_, 0, v_goal_2948_);
v___x_2972_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_initFn___closed__2_00___x40_Lean_Meta_Tactic_LibrarySearch_4259869437____hygCtx___hyg_2_));
v___x_2973_ = ((lean_object*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___lam__0___closed__4));
v___x_2974_ = lean_obj_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__2);
v___x_2975_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2961_, v_options_2960_, v___x_2974_);
if (v___x_2975_ == 0)
{
lean_object* v___x_3059_; uint8_t v___x_3060_; 
v___x_3059_ = l_Lean_trace_profiler;
v___x_3060_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_2960_, v___x_3059_);
if (v___x_3060_ == 0)
{
lean_object* v___x_3061_; uint8_t v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___f_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
lean_dec_ref(v___f_2971_);
v___x_3061_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2956_);
v___x_3062_ = 0;
v___x_3063_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3063_, 0, v___x_3062_);
lean_ctor_set_uint8(v___x_3063_, 1, v_hasTrace_2962_);
lean_ctor_set_uint8(v___x_3063_, 2, v_hasTrace_2962_);
lean_ctor_set_uint8(v___x_3063_, 3, v_hasTrace_2962_);
v___x_3064_ = lean_box(v_collectAll_2953_);
v___x_3065_ = lean_box(v_includeStar_2952_);
v___f_3066_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed), 12, 7);
lean_closure_set(v___f_3066_, 0, v_leavePercentHeartbeats_2951_);
lean_closure_set(v___f_3066_, 1, v___x_3063_);
lean_closure_set(v___f_3066_, 2, v_tactic_2949_);
lean_closure_set(v___f_3066_, 3, v_allowFailure_2950_);
lean_closure_set(v___f_3066_, 4, v_goal_2948_);
lean_closure_set(v___f_3066_, 5, v___x_3064_);
lean_closure_set(v___f_3066_, 6, v___x_3065_);
v___x_3067_ = lean_box(0);
v___x_3068_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_2963_, v___x_3061_, v___f_3066_, v___x_3067_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_);
lean_dec_ref(v___x_3061_);
return v___x_3068_;
}
else
{
goto v___jp_3003_;
}
}
else
{
goto v___jp_3003_;
}
v___jp_2976_:
{
lean_object* v___x_2980_; double v___x_2981_; double v___x_2982_; double v___x_2983_; double v___x_2984_; double v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2980_ = lean_io_mono_nanos_now();
v___x_2981_ = lean_float_of_nat(v___y_2977_);
v___x_2982_ = lean_float_once(&l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3, &l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3_once, _init_l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma___closed__3);
v___x_2983_ = lean_float_div(v___x_2981_, v___x_2982_);
v___x_2984_ = lean_float_of_nat(v___x_2980_);
v___x_2985_ = lean_float_div(v___x_2984_, v___x_2982_);
v___x_2986_ = lean_box_float(v___x_2983_);
v___x_2987_ = lean_box_float(v___x_2985_);
v___x_2988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2986_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
v___x_2989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2989_, 0, v_a_2979_);
lean_ctor_set(v___x_2989_, 1, v___x_2988_);
v___x_2990_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v___x_2972_, v_hasTrace_2962_, v___x_2973_, v_options_2960_, v___x_2975_, v___y_2978_, v___f_2971_, v___x_2989_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_);
return v___x_2990_;
}
v___jp_2991_:
{
lean_object* v___x_2995_; double v___x_2996_; double v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_2995_ = lean_io_get_num_heartbeats();
v___x_2996_ = lean_float_of_nat(v___y_2993_);
v___x_2997_ = lean_float_of_nat(v___x_2995_);
v___x_2998_ = lean_box_float(v___x_2996_);
v___x_2999_ = lean_box_float(v___x_2997_);
v___x_3000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2998_);
lean_ctor_set(v___x_3000_, 1, v___x_2999_);
v___x_3001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3001_, 0, v_a_2994_);
lean_ctor_set(v___x_3001_, 1, v___x_3000_);
v___x_3002_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__4(v___x_2972_, v_hasTrace_2962_, v___x_2973_, v_options_2960_, v___x_2975_, v___y_2992_, v___f_2971_, v___x_3001_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_);
return v___x_3002_;
}
v___jp_3003_:
{
lean_object* v___x_3004_; lean_object* v_a_3005_; lean_object* v___x_3006_; uint8_t v___x_3007_; 
v___x_3004_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__0___redArg(v_a_2957_);
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref(v___x_3004_);
v___x_3006_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3007_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearchLemma_spec__1(v_options_2960_, v___x_3006_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; lean_object* v___x_3009_; uint8_t v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___f_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3008_ = lean_io_mono_nanos_now();
v___x_3009_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2956_);
v___x_3010_ = 0;
v___x_3011_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3011_, 0, v___x_3010_);
lean_ctor_set_uint8(v___x_3011_, 1, v_hasTrace_2962_);
lean_ctor_set_uint8(v___x_3011_, 2, v_hasTrace_2962_);
lean_ctor_set_uint8(v___x_3011_, 3, v_hasTrace_2962_);
v___x_3012_ = lean_box(v_collectAll_2953_);
v___x_3013_ = lean_box(v_includeStar_2952_);
v___f_3014_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__1___boxed), 12, 7);
lean_closure_set(v___f_3014_, 0, v_leavePercentHeartbeats_2951_);
lean_closure_set(v___f_3014_, 1, v___x_3011_);
lean_closure_set(v___f_3014_, 2, v_tactic_2949_);
lean_closure_set(v___f_3014_, 3, v_allowFailure_2950_);
lean_closure_set(v___f_3014_, 4, v_goal_2948_);
lean_closure_set(v___f_3014_, 5, v___x_3012_);
lean_closure_set(v___f_3014_, 6, v___x_3013_);
v___x_3015_ = lean_box(0);
v___x_3016_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_2963_, v___x_3009_, v___f_3014_, v___x_3015_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_);
lean_dec_ref(v___x_3009_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3024_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3019_ = v___x_3016_;
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_3016_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3022_; 
if (v_isShared_3020_ == 0)
{
lean_ctor_set_tag(v___x_3019_, 1);
v___x_3022_ = v___x_3019_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_a_3017_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
v___y_2977_ = v___x_3008_;
v___y_2978_ = v_a_3005_;
v_a_2979_ = v___x_3022_;
goto v___jp_2976_;
}
}
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
v_a_3025_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_3016_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_3016_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
lean_ctor_set_tag(v___x_3027_, 0);
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
v___y_2977_ = v___x_3008_;
v___y_2978_ = v_a_3005_;
v_a_2979_ = v___x_3030_;
goto v___jp_2976_;
}
}
}
}
else
{
lean_object* v___x_3033_; lean_object* v___x_3034_; uint8_t v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___f_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3033_ = lean_io_get_num_heartbeats();
v___x_3034_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2956_);
v___x_3035_ = 0;
v___x_3036_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3036_, 0, v___x_3035_);
lean_ctor_set_uint8(v___x_3036_, 1, v___x_3007_);
lean_ctor_set_uint8(v___x_3036_, 2, v___x_3007_);
lean_ctor_set_uint8(v___x_3036_, 3, v___x_3007_);
v___x_3037_ = lean_box(v_collectAll_2953_);
v___x_3038_ = lean_box(v_includeStar_2952_);
v___x_3039_ = lean_box(v___x_3007_);
v___f_3040_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___lam__6___boxed), 13, 8);
lean_closure_set(v___f_3040_, 0, v_leavePercentHeartbeats_2951_);
lean_closure_set(v___f_3040_, 1, v___x_3036_);
lean_closure_set(v___f_3040_, 2, v_tactic_2949_);
lean_closure_set(v___f_3040_, 3, v_allowFailure_2950_);
lean_closure_set(v___f_3040_, 4, v_goal_2948_);
lean_closure_set(v___f_3040_, 5, v___x_3037_);
lean_closure_set(v___f_3040_, 6, v___x_3038_);
lean_closure_set(v___f_3040_, 7, v___x_3039_);
v___x_3041_ = lean_box(0);
v___x_3042_ = l_Lean_profileitM___at___00__private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27_spec__3___redArg(v___x_2963_, v___x_3034_, v___f_3040_, v___x_3041_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_);
lean_dec_ref(v___x_3034_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_3042_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3042_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
lean_ctor_set_tag(v___x_3045_, 1);
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
v___y_2992_ = v_a_3005_;
v___y_2993_ = v___x_3033_;
v_a_2994_ = v___x_3048_;
goto v___jp_2991_;
}
}
}
else
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
v_a_3051_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_3042_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3042_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
lean_ctor_set_tag(v___x_3053_, 0);
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
v___y_2992_ = v_a_3005_;
v___y_2993_ = v___x_3033_;
v_a_2994_ = v___x_3056_;
goto v___jp_2991_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27___boxed(lean_object* v_goal_3069_, lean_object* v_tactic_3070_, lean_object* v_allowFailure_3071_, lean_object* v_leavePercentHeartbeats_3072_, lean_object* v_includeStar_3073_, lean_object* v_collectAll_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_){
_start:
{
uint8_t v_includeStar_boxed_3080_; uint8_t v_collectAll_boxed_3081_; lean_object* v_res_3082_; 
v_includeStar_boxed_3080_ = lean_unbox(v_includeStar_3073_);
v_collectAll_boxed_3081_ = lean_unbox(v_collectAll_3074_);
v_res_3082_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(v_goal_3069_, v_tactic_3070_, v_allowFailure_3071_, v_leavePercentHeartbeats_3072_, v_includeStar_boxed_3080_, v_collectAll_boxed_3081_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_);
lean_dec(v_a_3078_);
lean_dec_ref(v_a_3077_);
lean_dec(v_a_3076_);
lean_dec_ref(v_a_3075_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearch(lean_object* v_goal_3083_, lean_object* v_tactic_3084_, lean_object* v_allowFailure_3085_, lean_object* v_leavePercentHeartbeats_3086_, uint8_t v_includeStar_3087_, uint8_t v_collectAll_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_){
_start:
{
lean_object* v___x_3094_; 
v___x_3094_ = l___private_Lean_Meta_Tactic_LibrarySearch_0__Lean_Meta_LibrarySearch_librarySearch_x27(v_goal_3083_, v_tactic_3084_, v_allowFailure_3085_, v_leavePercentHeartbeats_3086_, v_includeStar_3087_, v_collectAll_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_LibrarySearch_librarySearch___boxed(lean_object* v_goal_3095_, lean_object* v_tactic_3096_, lean_object* v_allowFailure_3097_, lean_object* v_leavePercentHeartbeats_3098_, lean_object* v_includeStar_3099_, lean_object* v_collectAll_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_){
_start:
{
uint8_t v_includeStar_boxed_3106_; uint8_t v_collectAll_boxed_3107_; lean_object* v_res_3108_; 
v_includeStar_boxed_3106_ = lean_unbox(v_includeStar_3099_);
v_collectAll_boxed_3107_ = lean_unbox(v_collectAll_3100_);
v_res_3108_ = l_Lean_Meta_LibrarySearch_librarySearch(v_goal_3095_, v_tactic_3096_, v_allowFailure_3097_, v_leavePercentHeartbeats_3098_, v_includeStar_boxed_3106_, v_collectAll_boxed_3107_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_);
lean_dec(v_a_3104_);
lean_dec_ref(v_a_3103_);
lean_dec(v_a_3102_);
lean_dec_ref(v_a_3101_);
return v_res_3108_;
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
